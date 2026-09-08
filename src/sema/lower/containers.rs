// The three literals that build a type a library declared.
//
// All three are literal syntax for a type a library declares, which is the
// shape §8 settles: "A map and a set are `Map<K, V>` and `Set<T>`, and the
// hashed kinds are types of their own, `HashMap<K, V>` and `HashSet<T>` -- so
// which one you named says how it behaves, and a `#{` literal builds the hashed
// one." So nothing is built in here; the names are looked up like any other.

use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // `{1: 2}` and `#{1: 2}`. Every key is one type and every value another,
    // which is what makes a map a map rather than a list of pairs.
    pub(super) fn map(
        &mut self,
        hashed: bool,
        entries: &[crate::tir::tir_nodes::TIRMapEntry],
        at: TIRExprId,
    ) -> TTIRExprId {
        let mut made = Vec::new();
        let mut key = self.types.fresh();
        let mut value = self.types.fresh();
        for entry in entries {
            let k = self.expr(entry.key);
            let v = self.expr(entry.value);
            key = self.agree(key, self.out.exprs[k].ty, "every key of a map is one type", at);
            value =
                self.agree(value, self.out.exprs[v].ty, "every value of a map is one type", at);
            made.push((k, v));
        }
        let held = self.container(hashed, "Map", vec![key, value], at);
        let entries = made.into_iter().flat_map(|(k, v)| [k, v]).collect();
        self.built_by(held, &[key, value], 2, entries, at)
    }

    // `{1, 2}` and `#{1, 2}`, and `{,}` which is the empty one.
    pub(super) fn set(&mut self, hashed: bool, elems: &[TIRExprId], at: TIRExprId) -> TTIRExprId {
        let mut made = Vec::new();
        let mut elem = self.types.fresh();
        for &held in elems {
            let e = self.expr(held);
            elem = self.agree(elem, self.out.exprs[e].ty, "every element of a set is one type", at);
            made.push(e);
        }
        let held = self.container(hashed, "Set", vec![elem], at);
        self.built_by(held, &[elem], 1, made, at)
    }

    // `1..10`, `1..`, `..10` and `..`. One type for however many bounds were
    // written, and a `..` with neither is a hole until something fills it.
    pub(super) fn range(
        &mut self,
        op: crate::tir::tir_nodes::TIRRangeOp,
        start: Option<TIRExprId>,
        end: Option<TIRExprId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        let mut bound = self.types.fresh();
        let start = start.map(|s| self.expr(s));
        let end = end.map(|e| self.expr(e));
        for &held in start.iter().chain(end.iter()) {
            bound = self.agree(bound, self.out.exprs[held].ty, "a range runs between one type", at);
        }
        // The prose names `Map` and `Set` and does not name this one, so the
        // name is a choice: one `Range<T>` for all four shapes, the bounds
        // being optional in the value rather than in the type. Four types for
        // four shapes is the other answer, and nothing here settles it.
        // A range is still built where it stands: it holds its two bounds and
        // nothing else, so there is nothing for a library routine to do that
        // the two words cannot.
        let ty = match self.container(false, "Range", vec![bound], at) {
            Some((_, ty)) => ty,
            None => self.types.error(),
        };
        self.make(TTIRExprKind::Range { op, start, end }, ty, at)
    }

    // What a literal *is*: the library's own routines, called.
    //
    // `#{1: 2}` is `var m = hashmap::empty(); hashmap::insert(*m, 1, 2); m`,
    // written out here rather than by the reader. That is what "a literal is
    // syntax for a type a library declares" has to mean -- the type is the
    // library's, so the value has to be one the library made.
    //
    // It was not. The lowering made a handle to the runtime's own table, which
    // was written when no library declared one and says so in
    // `src/mir/runtime.rs`: a map and a set "standing in for the library §8
    // says should one day declare them". The library arrived and the lowering
    // did not move, so `#{1: 2}` built a runtime handle, typed it as the
    // eighty-byte `hashmap::HashMap` a Forte file declares, handed the slot's
    // *address* to the runtime as if it were the handle, and read its fields
    // out of uninitialised bytes. `m.len` on a map of three came back 136.
    //
    // The bound comes with it, and is the reason this is not just a rewrite: a
    // key that answers neither `Hash` nor `Eq` is turned down at the literal,
    // where the reader wrote it, because `instance_of` puts the routine's
    // obligations where every other call's go.
    fn built_by(
        &mut self,
        held: Option<(TTIRItemId, TyId)>,
        args: &[TyId],
        per: usize,
        entries: Vec<TTIRExprId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        // The type was not found, and that has been said once already.
        let Some((declared, ty)) = held else { return self.errored(at) };
        // Beside the declaration and not by a path: the type is whatever the
        // prelude found or whatever this file declared instead, and the
        // routines that build it are its neighbours either way. A path would
        // name `hashmap::empty` and miss a suite that wrote its own `HashMap`.
        let Some((file, _)) = self.from_item.get(declared).copied().flatten() else {
            return self.errored(at);
        };
        // A map puts one in and a set adds one, which is the only place the
        // two shapes differ below.
        let adder = if per == 2 { "insert" } else { "add" };
        let (Some(empty), Some(add)) = (
            self.beside(declared, file, "empty", true),
            self.beside(declared, file, adder, false),
        ) else {
            let name = self.spell(ty);
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` is declared and cannot be built", name),
                    self.at(at),
                )
                .with_label("this builds one")
                .with_note(format!(
                    "a literal calls `empty` and `{}` beside the declaration, and \
                     the file that declares the type declares neither",
                    adder
                )),
            );
            return self.errored(at);
        };
        // A frame to put the value in. A literal is a value that is built by
        // running something, so there has to be somewhere for it to run.
        if self.frames.is_empty() {
            let held = self.spell(ty);
            self.errors.push(
                Diagnostic::error(
                    format!("a `{}` is built where a body runs", held),
                    self.at(at),
                )
                .with_label("this is written outside one")
                .with_note(
                    "a literal calls the library that declares the type, and a \
                     global's value is written into the image before anything runs",
                ),
            );
            return self.errored(at);
        }

        let init = self.calling_in(empty, args, Vec::new(), at);
        let _ = self.types.unify(self.out.exprs[init].ty, ty);
        let name = format!("(built {})", self.builds);
        self.builds += 1;
        let slot = self.bind(
            TIRBinding::Name(name),
            ty,
            crate::tir::tir_nodes::TIRIntro::Var,
            self.at(at),
        );
        let mut stmts = vec![TTIRStmt::Let { is_unsafe: false, local: slot, init: Some(init) }];
        let taken = self.types.intern(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: ty });
        for entry in entries.chunks(per) {
            let local = self.make(TTIRExprKind::Local(slot), ty, at);
            let recv = self.make(
                TTIRExprKind::Unary { op: TIRUnaryOp::Ref(TIRRefOp::Mut), operand: local },
                taken,
                at,
            );
            let mut handed = vec![recv];
            handed.extend(entry.iter().copied());
            let call = self.calling_in(add, args, handed, at);
            stmts.push(TTIRStmt::Expr { is_unsafe: false, expr: call });
        }
        let tail = self.make(TTIRExprKind::Local(slot), ty, at);
        self.make(TTIRExprKind::Block { stmts, tail: Some(tail) }, ty, at)
    }

    // A routine written beside a declaration: `empty`, which answers with one
    // of it, and `insert` or `add`, which takes one to put something in.
    //
    // By what it is *about* and not by its name alone. A file may declare more
    // than one container -- the tests do -- and `empty` there would be one name
    // for two routines; the type each is written about is what tells them
    // apart, and it is the same question `head_of` asks everywhere else.
    fn beside(
        &self,
        declared: TTIRItemId,
        file: usize,
        name: &str,
        answers: bool,
    ) -> Option<TTIRItemId> {
        let want = Head::Named(declared);
        (0..self.out.items.len()).find(|&item| {
            if self.from_item.get(item).copied().flatten().map(|(f, _)| f) != Some(file) {
                return false;
            }
            let TTIRItemKind::Fn(f) = &self.out.items[item].kind else { return false };
            if f.name != name {
                return false;
            }
            let Some(Ty::Fn { params, ret, .. }) = Some(self.types.get(f.ty)) else {
                return false;
            };
            let held = match answers {
                true => *ret,
                false => match params.first() {
                    Some(&first) => match Some(self.types.get(first)) {
                        Some(Ty::Ref { inner, .. }) => *inner,
                        _ => first,
                    },
                    None => return false,
                },
            };
            match Some(self.types.get(held)) {
                Some(ty) => head_of(ty) == want,
                None => false,
            }
        })
    }

    // One call to a library routine the reader did not write. `args` are the
    // type arguments -- `K` and `V`, or `T` -- and they are unified with the
    // holes `instance_of` made rather than written in, so the routine's bounds
    // are pending against the same types every other call's are.
    fn calling_in(
        &mut self,
        item: TTIRItemId,
        args: &[TyId],
        handed: Vec<TTIRExprId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        let (fn_ty, types) = self.instance_of(item, at);
        for (&hole, &want) in types.iter().zip(args.iter()) {
            let _ = self.types.unify(hole, want);
        }
        let Ty::Fn { params, ret, .. } = self.types.get(fn_ty).clone() else {
            return self.errored(at);
        };
        // Held to the declaration the same way a written call is, so a value
        // of the wrong type is one message and not a silent conversion.
        for (&want, &got) in params.iter().zip(handed.iter()) {
            let got = self.out.exprs[got].ty;
            let _ = self.types.unify(got, want);
        }
        let callee = self.make(TTIRExprKind::Item(item), fn_ty, at);
        self.make(TTIRExprKind::Call { callee, args: handed, types }, ret, at)
    }

    // The declaration a literal builds. `#` makes it the hashed kind, which is
    // "a type of its own" and not the same one with a flag.
    //
    // What a `{` literal with no annotation builds is left open by §8. It
    // builds the ordered one here, `#` being what the language spends on saying
    // hashed -- so a literal with nothing on it is the one with nothing on it.
    fn container(
        &mut self,
        hashed: bool,
        kind: &str,
        args: Vec<TyId>,
        at: TIRExprId,
    ) -> Option<(TTIRItemId, TyId)> {
        let name = if hashed { format!("Hash{}", kind) } else { kind.to_string() };
        match self.look(&name) {
            Some(item) if matches!(
                self.out.items[item].kind,
                TTIRItemKind::Struct { .. } | TTIRItemKind::Enum { .. }
            ) =>
            {
                let regions = self.named_regions(item, &[], self.at(at));
                Some((item, self.types.intern(Ty::Named { item, args, regions })))
            }
            _ => {
                self.errors.push(
                    Diagnostic::error(format!("no type is called `{}`", name), self.at(at))
                        .with_label("this builds one")
                        .with_note("a literal is syntax for a type a library declares, and this suite declares none"),
                );
                None
            }
        }
    }

    // Two types that have to be one, with what to say where they are not.
    fn agree(&mut self, held: TyId, found: TyId, what: &str, at: TIRExprId) -> TyId {
        match self.types.unify(held, found) {
            Ok(one) => one,
            Err(_) => {
                let (held, found) = (self.spell(held), self.spell(found));
                self.errors.push(
                    Diagnostic::error(format!("`{}` and `{}` are not one type", held, found), self.at(at))
                        .with_label(what),
                );
                self.types.error()
            }
        }
    }
}
