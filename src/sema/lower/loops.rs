// `while` and `for`, and the one thing that makes them more than a block.
//
// A `for` binds a name per turn, which is a slot of the body like any other
// and a scope of its own -- so what the loop declares goes when the loop does.
// And a `break` may carry a value, which makes a loop an expression with a
// type: every `break` out of one has to agree with every other, and a loop
// nothing breaks out of with a value is `null`.

use std::collections::HashMap;

use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

// The three routines a container writes to say how it is walked, and what they
// are written about.
pub(super) struct Walk {
    pub step:      TTIRItemId,
    pub valid:     TTIRItemId,
    pub elem:      TTIRItemId,
    // The declaration's own type, without whatever reference reached it, and
    // the arguments it was given.
    pub container: TyId,
    pub args:      Vec<TyId>,
}

impl<'a> Lowerer<'a> {
    // `for x in it`. The loop variable is a slot of the body, bound afresh each
    // turn, and what it holds is what the iterable holds.
    pub(super) fn for_each(
        &mut self,
        name: &TIRBinding,
        iter: TIRExprId,
        body: TIRExprId,
        at: TIRExprId,
    ) -> TTIRExprId {
        let it = self.expr(iter);
        let over = self.out.exprs[it].ty;
        // A container that says how it is walked is walked that way, and the
        // loop the three routines make is written out here -- see `walking`.
        if let Some(walk) = self.walked(over) {
            return self.walking(walk, name, it, body, at);
        }
        let elem = match self.elem_of(over) {
            Some(elem) => elem,
            None => {
                if !matches!(self.types.get(over), Ty::Error) {
                    // A hole a number goes in spells as `_`, which says
                    // nothing here; what it will come to does.
                    let held = match self.types.standing(over) {
                        Some(prim) => crate::sema::types::prim_name(prim).to_string(),
                        None => self.spell(over),
                    };
                    self.errors.push(
                        Diagnostic::error(
                            format!("there is no running through a `{}`", held),
                            self.at(iter),
                        )
                        .with_label("this is what the loop is over")
                        .with_note(
                            "an array, a view of one, a `Range`, or a type whose \
                             file writes `step`, `valid` and `elem` beside it",
                        )
                        .with_help(
                            "the language has no iterator protocol, so what may be \
                             run through is a closed set -- and a file joins that \
                             set by writing the three routines a walk calls",
                        ),
                    );
                }
                self.types.error()
            }
        };

        // The loop variable stands in the body and nowhere else.
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
        let local =
            self.bind(name.clone(), elem, crate::tir::tir_nodes::TIRIntro::Let, self.at(at));
        self.breaks.push(Vec::new());
        let b = self.expr(body);
        let ty = self.loop_value(at);
        self.frames.last_mut().expect("a frame").scopes.pop();

        self.make(TTIRExprKind::For { local, iter: it, body: b }, ty, at)
    }

    // What a loop is worth: "the operand of the `break` that leaves it... and
    // where none is given the loop is `null`". A loop that can end by itself
    // has `null` among the values it yields, which is the same rule asked of
    // the loop -- and `null` belongs to every type, so a loop with a `break x`
    // is worth what `x` is.
    pub(super) fn loop_value(&mut self, at: TIRExprId) -> TyId {
        let held = self.breaks.pop().unwrap_or_default();
        let mut ty = self.types.null();
        for found in held {
            match self.types.unify(ty, found) {
                Ok(one) => ty = one,
                Err(_) => {
                    let (ty, found) = (self.spell(ty), self.spell(found));
                    self.errors.push(
                        Diagnostic::error(
                            format!("one `break` gives `{}` and another `{}`", ty, found),
                            self.at(at),
                        )
                        .with_label("a loop is worth one type"),
                    );
                    return self.types.error();
                }
            }
        }
        ty
    }

    // The three routines a container writes to say how it is walked, where it
    // wrote them: `step`, `valid` and `elem`, each taking a reference to one.
    //
    // "The language has no iterator protocol, so what may be run through is a
    // closed set" (§5) -- and the set stays closed. What moved is where the
    // answer comes from: an array, a view and a `Range` are walked by index
    // arithmetic because a call to add one to a number would be a call to add
    // one to a number, and everything else says so in the file that declares
    // it. That is what lets a map be run through at all: it hands out a pair,
    // and the pair is `elem`'s answer rather than something the compiler has
    // to know how to make.
    pub(super) fn walked(&mut self, ty: TyId) -> Option<Walk> {
        let bare = self.reached(ty);
        let Ty::Named { item, args, .. } = self.types.get(bare).clone() else { return None };
        let (file, _) = self.from_item.get(item).copied().flatten()?;
        Some(Walk {
            step:      self.beside(item, file, "step", false)?,
            valid:     self.beside(item, file, "valid", false)?,
            elem:      self.beside(item, file, "elem", false)?,
            container: bare,
            args,
        })
    }

    // Through however many references to what is at the end of them. A `gc`
    // counts: it is one word holding an address and is reached through exactly
    // as a reference is (§2).
    fn reached(&mut self, ty: TyId) -> TyId {
        match self.types.get(self.types.shallow(ty)).clone() {
            Ty::Ref { inner, .. } | Ty::GC(inner) => self.reached(inner),
            _ => self.types.shallow(ty),
        }
    }

    // `for x in c` where `c` says how it is walked, written out as the loop
    // its three routines make:
    //
    //     let $c = &c
    //     var $at = -1
    //     while true {
    //         $at = step($c, $at)
    //         if !valid($c, $at) { break }
    //         let x = elem($c, $at)
    //         ..body..
    //     }
    //
    // Here and not further down, because what comes out is three ordinary
    // calls: `mir::mono` finds the instances the same way it finds every other
    // one, and no pass below this has to learn a thing.
    //
    // The cursor starts at -1 and the first thing a turn does is step, so the
    // contract is that stepping from -1 lands on the first -- which is the one
    // the runtime's own cursor already had.
    fn walking(
        &mut self,
        walk: Walk,
        name: &TIRBinding,
        it: TTIRExprId,
        body: TIRExprId,
        at: TIRExprId,
    ) -> TTIRExprId {
        let whole = self.types.prim(TIRPrim::I64);
        let truth = self.types.prim(TIRPrim::Bool);
        let null = self.types.null();
        let where_ = self.at(at);

        // Everything the loop binds stands in the body and nowhere else, the
        // two it did not write among them.
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());

        // `let $c = &c`. A reference and not a copy: what is being run through
        // is not the loop's to take, and the three routines all ask for one.
        let held = self.out.exprs[it].ty;
        let taken = match self.types.get(self.types.shallow(held)) {
            Ty::Ref { .. } | Ty::GC(_) | Ty::Ptr(_) => it,
            _ => {
                let ty = self
                    .types
                    .intern(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: walk.container });
                self.make(
                    TTIRExprKind::Unary { op: TIRUnaryOp::Ref(TIRRefOp::Imm), operand: it },
                    ty,
                    at,
                )
            }
        };
        let over = self.out.exprs[taken].ty;
        let held = self.holder("walk", over, TIRIntro::Let, where_);
        let cursor = self.holder("at", whole, TIRIntro::Var, where_);
        let first = self.make(TTIRExprKind::Literal(TIRLit::Int(-1)), whole, at);
        let mut outer = vec![
            TTIRStmt::Let { is_unsafe: false, local: held, init: Some(taken) },
            TTIRStmt::Let { is_unsafe: false, local: cursor, init: Some(first) },
        ];

        // `$at = step($c, $at)`
        let (a, b) = (
            self.make(TTIRExprKind::Local(held), over, at),
            self.make(TTIRExprKind::Local(cursor), whole, at),
        );
        let step = self.calling_in(walk.step, &walk.args, vec![a, b], at);
        let place = self.make(TTIRExprKind::Local(cursor), whole, at);
        let moved = self.make(
            TTIRExprKind::Assign { op: TIRAssignOp::Set, place, value: step },
            null,
            at,
        );

        // `if !valid($c, $at) { break }`
        let (a, b) = (
            self.make(TTIRExprKind::Local(held), over, at),
            self.make(TTIRExprKind::Local(cursor), whole, at),
        );
        let asked = self.calling_in(walk.valid, &walk.args, vec![a, b], at);
        let done = self.make(
            TTIRExprKind::Unary { op: TIRUnaryOp::Not, operand: asked },
            truth,
            at,
        );
        // The `break` the loop is left by, which carries nothing -- so `null`
        // is among what the loop is worth, exactly as it is for a `while` that
        // can end by itself.
        self.breaks.push(vec![null]);
        let never = self.types.never();
        let leaves = self.make(TTIRExprKind::Break(None), never, at);
        let out = self.make(
            TTIRExprKind::If { cond: done, then: leaves, els: None },
            null,
            at,
        );

        // `let x = elem($c, $at)`, which is the binding the reader wrote.
        let (a, b) = (
            self.make(TTIRExprKind::Local(held), over, at),
            self.make(TTIRExprKind::Local(cursor), whole, at),
        );
        let one = self.calling_in(walk.elem, &walk.args, vec![a, b], at);
        let elem = self.out.exprs[one].ty;
        let slot = self.bind(name.clone(), elem, TIRIntro::Let, where_);

        let inner = vec![
            TTIRStmt::Expr { is_unsafe: false, expr: moved },
            TTIRStmt::Expr { is_unsafe: false, expr: out },
            TTIRStmt::Let { is_unsafe: false, local: slot, init: Some(one) },
            TTIRStmt::Expr { is_unsafe: false, expr: self.expr(body) },
        ];
        let ty = self.loop_value(at);
        self.frames.last_mut().expect("a frame").scopes.pop();

        let inner = self.make(TTIRExprKind::Block { stmts: inner, tail: None }, null, at);
        let cond = self.make(TTIRExprKind::Literal(TIRLit::Bool(true)), truth, at);
        let held = self.make(TTIRExprKind::While { cond, body: inner }, ty, at);
        // The loop is the block's *value* and not a statement in it: a `for` is
        // worth "the operand of the `break` that leaves it" (§5.1), and a block
        // with nothing at the end is worth `null` however much ran in it.
        self.make(TTIRExprKind::Block { stmts: outer, tail: Some(held) }, ty, at)
    }

    // A slot the reader did not write, named so that nothing written reaches it.
    fn holder(
        &mut self,
        what: &str,
        ty: TyId,
        intro: TIRIntro,
        where_: crate::error::Span,
    ) -> TTIRLocalId {
        let name = format!("({} {})", what, self.builds);
        self.builds += 1;
        self.bind(TIRBinding::Name(name), ty, intro, where_)
    }

    // What running through a thing hands out, one at a time.
    //
    // A closed set, and it has to be: the language has no trait with code
    // behind it, so there is no protocol for a library to answer and no way to
    // ask one. These are the sequences the language itself has -- and when a
    // protocol exists, this is the function that goes.
    fn elem_of(&mut self, ty: TyId) -> Option<TyId> {
        match self.types.get(ty).clone() {
            // "T[8]" owns and "T[]" is a run only a reference can hold.
            Ty::Array { elem, .. } | Ty::Run(elem) => Some(elem),
            // "A reference to a fixed array is a view of it" (§3), and a view
            // is what is run through.
            Ty::Ref { inner, .. } | Ty::GC(inner) => self.elem_of(inner),
            Ty::Named { item, args, .. } => {
                let held = match &self.out.items[item].kind {
                    TTIRItemKind::Struct { name, .. } | TTIRItemKind::Enum { name, .. } => {
                        name.as_str()
                    }
                    _ => return None,
                };
                // A `Range` and nothing else by name. Everything else a
                // library declares says how it is walked in the file that
                // declares it -- see `walked`, which is asked first -- and a
                // range does not, because a range is two numbers and walking
                // one is counting.
                match held {
                    "Range" => args.first().copied(),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
