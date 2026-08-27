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
        let ty = self.container(hashed, "Map", vec![key, value], at);
        self.make(TTIRExprKind::Map { hashed, entries: made }, ty, at)
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
        let ty = self.container(hashed, "Set", vec![elem], at);
        self.make(TTIRExprKind::Set { hashed, elems: made }, ty, at)
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
        let ty = self.container(false, "Range", vec![bound], at);
        self.make(TTIRExprKind::Range { op, start, end }, ty, at)
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
    ) -> TyId {
        let name = if hashed { format!("Hash{}", kind) } else { kind.to_string() };
        match self.names.get(&name).copied() {
            Some(item) if matches!(
                self.out.items[item].kind,
                TTIRItemKind::Struct { .. } | TTIRItemKind::Enum { .. }
            ) =>
            {
                let regions = self.named_regions(item, &[], self.at(at));
                self.types.intern(Ty::Named { item, args, regions })
            }
            _ => {
                self.errors.push(
                    Diagnostic::error(format!("no type is called `{}`", name), self.at(at))
                        .with_label("this builds one")
                        .with_note("a literal is syntax for a type a library declares, and this suite declares none"),
                );
                self.types.error()
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
