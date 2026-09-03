// What taking a value apart does to it.
//
// A pattern that binds a name out of a value takes that part of the value with
// it, which is a move -- so the rest of the value is not all there any more,
// and a second arm that wanted the whole of it is asking for something that
// has gone. That is what everything here is about: which parts a pattern hands
// away, which it only looks at, and what is left of the subject afterwards.
//
// It is here and not in `sema::borrows` because it is a question about a
// pattern, and a pattern is a shape this pass has in hand and that one would
// have to walk again. What `borrows` does with the answer is refuse the uses
// that come after.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // A name that binds: a slot of the body, standing in this arm alone.
    pub(super) fn binding(&mut self, path: &[String], want: TyId, id: TIRPatId) -> TTIRPatId {
        if path.len() != 1 {
            let name = path.join("::");
            self.errors.push(
                Diagnostic::error(format!("nothing is called `{}`", name), self.pat_at(id))
                    .with_label("no such constant or variant")
                    .with_help("a name with a `::` in it tests; a bare one binds"),
            );
            return self.errored_pat(id, want);
        }
        let slot = self.bind(
            TIRBinding::Name(path[0].clone()),
            want,
            crate::tir::tir_nodes::TIRIntro::Let,
            self.pat_at(id),
        );
        self.make_pat(TTIRPatKind::Bind(slot), want, id)
    }

    pub(super) fn errored_pat(&mut self, id: TIRPatId, want: TyId) -> TTIRPatId {
        self.make_pat(TTIRPatKind::Wildcard, want, id)
    }

    // A pattern's own type held against what it is tested on.
    // Whether a body hands a slot's value over rather than reading through it.
    // The four places §2 names -- an argument, a return, the right of an
    // assignment, a field of a literal being built -- come to one thing here: a
    // name standing for its value and not for a place reached into.
    //
    // Walked from the body's own value and not over the arena: "a
    // `TTIRLocalId` is a slot of the body that holds it, not of the program",
    // so the same number in two bodies is two different slots.
    pub(super) fn hands_away(&self, body: TTIRBodyId, slot: TTIRLocalId) -> bool {
        self.given_away(self.out.bodies[body].value, slot)
    }

    // Whether a body writes to a slot, however it reaches it: a `var n = ..`
    // captured by value and assigned to is a closure with state of its own.
    pub(super) fn writes_to(&self, body: TTIRBodyId, slot: TTIRLocalId) -> bool {
        self.out.exprs.iter().enumerate().any(|(id, e)| {
            matches!(&e.kind, TTIRExprKind::Assign { place, .. } if self.roots_at(*place, slot))
                && self.within(self.out.bodies[body].value, id)
        })
    }

    // Whether a place is reached from a slot: the name at the bottom of it.
    fn roots_at(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Local(held) => *held == slot,
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.roots_at(*base, slot),
            _ => false,
        }
    }

    // Whether one expression stands inside another, which is how a body says
    // which expressions are its own -- the arena holds every body's at once.
    fn within(&self, outer: TTIRExprId, id: TTIRExprId) -> bool {
        if outer == id {
            return true;
        }
        self.kids_of(outer).into_iter().any(|kid| self.within(kid, id))
    }

    // Everything one expression holds, whatever it is. A closure's body is not
    // among them: it is a body of its own and its slots are its own.
    fn kids_of(&self, id: TTIRExprId) -> Vec<TTIRExprId> {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                vec![*base]
            }
            TTIRExprKind::Index { base, index } => vec![*base, *index],
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => vec![*operand],
            TTIRExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            TTIRExprKind::Assign { place, value, .. } => vec![*place, *value],
            TTIRExprKind::Call { callee, args } => {
                std::iter::once(*callee).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::Method { recv, args, .. } => {
                std::iter::once(*recv).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => fields.clone(),
            TTIRExprKind::Map { entries, .. } => {
                entries.iter().flat_map(|&(k, v)| [k, v]).collect()
            }
            TTIRExprKind::Range { start, end, .. } => {
                [start, end].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::Block { stmts, tail } => {
                let mut held: Vec<TTIRExprId> = Vec::new();
                for stmt in stmts {
                    match stmt {
                        TTIRStmt::Let { init, .. } => held.extend(init.iter()),
                        TTIRStmt::Expr { expr, .. } => held.push(*expr),
                        TTIRStmt::Item(_) => {}
                    }
                }
                held.extend(tail.iter());
                held
            }
            TTIRExprKind::If { cond, then, els } => {
                [Some(cond), Some(then), els.as_ref()].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::While { cond, body } => vec![*cond, *body],
            TTIRExprKind::For { iter, body, .. } => vec![*iter, *body],
            TTIRExprKind::Match { scrutinee, arms } => std::iter::once(*scrutinee)
                .chain(arms.iter().map(|a| a.body))
                .collect(),
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                value.iter().copied().collect()
            }
            _ => Vec::new(),
        }
    }

    fn given_away(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        let kids: Vec<TTIRExprId> = match &self.out.exprs[id].kind {
            // Here it is, standing for its value: this is the handing over.
            TTIRExprKind::Local(held) => return *held == slot,
            // Reached into or borrowed, either of which leaves it where it is.
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. } => {
                return self.reaches_past(*base, slot)
            }
            TTIRExprKind::Index { base, index } => {
                return self.reaches_past(*base, slot) || self.given_away(*index, slot)
            }
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), operand }
            | TTIRExprKind::Unary { op: TIRUnaryOp::Addr, operand } => {
                return self.reaches_past(*operand, slot)
            }
            TTIRExprKind::Assign { place, value, .. } => {
                return self.reaches_past(*place, slot) || self.given_away(*value, slot)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => vec![*operand],
            TTIRExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            TTIRExprKind::Call { callee, args } => {
                std::iter::once(*callee).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::Method { recv, args, .. } => {
                std::iter::once(*recv).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => fields.clone(),
            TTIRExprKind::Map { entries, .. } => {
                entries.iter().flat_map(|&(k, v)| [k, v]).collect()
            }
            TTIRExprKind::Range { start, end, .. } => {
                [start, end].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::Block { stmts, tail } => {
                let mut held: Vec<TTIRExprId> = Vec::new();
                for stmt in stmts {
                    match stmt {
                        TTIRStmt::Let { init, .. } => held.extend(init.iter()),
                        TTIRStmt::Expr { expr, .. } => held.push(*expr),
                        TTIRStmt::Item(_) => {}
                    }
                }
                held.extend(tail.iter());
                held
            }
            TTIRExprKind::If { cond, then, els } => {
                [Some(cond), Some(then), els.as_ref()].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::While { cond, body } => vec![*cond, *body],
            TTIRExprKind::For { iter, body, .. } => vec![*iter, *body],
            TTIRExprKind::Match { scrutinee, arms } => std::iter::once(*scrutinee)
                .chain(arms.iter().map(|a| a.body))
                .collect(),
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                value.iter().copied().collect()
            }
            // A closure inside a closure names the outer frame's slots through
            // its own captures, which the outer one already caught.
            _ => Vec::new(),
        };
        kids.into_iter().any(|kid| self.given_away(kid, slot))
    }

    // The same walk, of something being reached into rather than handed over:
    // the name at the bottom of it stays where it is, and anything else in it
    // is handed over as it would be anywhere.
    fn reaches_past(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Local(_) => false,
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                self.reaches_past(*base, slot)
            }
            TTIRExprKind::Index { base, index } => {
                self.reaches_past(*base, slot) || self.given_away(*index, slot)
            }
            _ => self.given_away(id, slot),
        }
    }

    // Whether a type is copied where it is handed over. `Copy` is found by
    // name, as §2 says the compiler knows it.
    pub(super) fn copies(&self, ty: TyId) -> bool {
        // Through a filled hole: this runs while the body's types are still
        // being worked out, and a number is a hole until something fixes it.
        match self.types.get(self.types.shallow(ty)) {
            Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Fn { .. } | Ty::Run(_) => true,
            // One nobody has worked out yet, and one that went wrong: both
            // read as copying, which is the answer that adds no second message
            // to a program that already has one.
            Ty::Var(_) | Ty::Error => true,
            Ty::Named { item, .. } => self.out.items.iter().any(|held| {
                matches!(&held.kind, TTIRItemKind::Impl { ty, of: Some(of), .. }
                    if matches!(self.types.get(*ty), Ty::Named { item: named, .. } if named == item)
                        && matches!(&self.out.items[*of].kind,
                            TTIRItemKind::Trait { name, .. } if name == "Copy"))
            }),
            _ => false,
        }
    }

    // "a closure stands where a weaker one is wanted: reading is less than
    // writing and writing is less than taking" -- and not the other way. This
    // is the half `unify` cannot say: it takes the greater of the two, which is
    // the right answer where a hole is being filled and the wrong one where a
    // person wrote what they wanted. So wherever what was written is one side
    // and what was found is the other, this is asked as well.
    pub(super) fn stands_as(&mut self, found: TyId, want: TyId, at: Span) {
        let found = self.types.shallow(found);
        let want = self.types.shallow(want);
        let (Ty::Fn { uses: got, .. }, Ty::Fn { uses: asked, .. }) =
            (self.types.get(found).clone(), self.types.get(want).clone())
        else {
            return;
        };
        if got <= asked {
            return;
        }
        let (found, want) = (self.spell(found), self.spell(want));
        self.errors.push(
            Diagnostic::error(
                format!("this is `{}` and what wants it says `{}`", found, want),
                at,
            )
            .with_label("it may be called fewer times than that")
            .with_note("`fn` reads what a closure captured, `var fn` writes to it and `once fn` takes it")
            .with_help("a closure stands where a weaker one is wanted, and not the other way"),
        );
    }

    pub(super) fn hold(&mut self, found: TyId, want: TyId, id: TIRPatId) {
        if self.types.unify(found, want).is_err() {
            let (found, want) = (self.spell(found), self.spell(want));
            self.errors.push(
                Diagnostic::error(
                    format!("this tests `{}` against `{}`", found, want),
                    self.pat_at(id),
                )
                .with_label("the two do not meet"),
            );
        }
    }

    // The enum a path names a variant of, and which variant it is. "`::`
    // reaches into a namespace, a module or a type" (§5) -- an enum is the
    // type, and the name after it is the variant, so `Color::Red` is the enum
    // named by everything but the last segment.
    pub(super) fn variant_path(&self, path: &[String]) -> Option<(TTIRItemId, usize)> {
        if path.len() < 2 {
            return None;
        }
        let last = path.last()?;
        let of = self.look(&path[..path.len() - 1].join("::"))?;
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else { return None };
        variants.iter().position(|v| v.name == *last).map(|i| (of, i))
    }

    // What one variant carries, by the names it gave them: a struct-shaped
    // variant names its fields, and a pattern may reach them by name.
    pub(super) fn payload_names(&self, of: TTIRItemId, index: usize) -> Vec<(String, TyId)> {
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else {
            return Vec::new();
        };
        match variants.get(index).map(|v| &v.payload) {
            Some(TTIRPayload::Named(fields)) => {
                fields.iter().map(|f| (f.name.clone(), f.ty)).collect()
            }
            // A tuple variant names nothing, so nothing reaches it by name.
            _ => Vec::new(),
        }
    }

    // What one variant carries, as types.
    pub(super) fn payload_tys(&self, of: TTIRItemId, index: usize) -> Vec<TyId> {
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else {
            return Vec::new();
        };
        match variants.get(index).map(|v| &v.payload) {
            Some(TTIRPayload::Tuple(tys)) => tys.clone(),
            Some(TTIRPayload::Named(fields)) => fields.iter().map(|f| f.ty).collect(),
            _ => Vec::new(),
        }
    }
}
