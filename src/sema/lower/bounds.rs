// Which types answer which traits.
//
// An impl is what makes a method callable and a bound satisfiable, and both
// questions come down to the same lookup: for this type and this trait, is
// there an impl. `Head` is what makes the lookup cheap -- a type is reduced to
// what it is at the top, since an impl is written for a declaration and not
// for a shape -- and everything else here is the walk that checks a
// declaration's bounds are met by what a caller supplied.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // Which types answer each trait. "an impl makes methods for its type" and
    // an `impl Show for Buf` is Buf saying it answers Show -- so the impls are
    // the whole of what a bound can be held against.
    pub(super) fn gather_impls(&mut self) {
        for id in 0..self.out.items.len() {
            let TTIRItemKind::Impl { ty, of: Some(held), .. } = &self.out.items[id].kind else {
                continue;
            };
            let (ty, held) = (*ty, *held);
            self.answers.entry(held).or_default().push(ty);
        }
    }

    // Whether one type is held to one bound, said where it is not.
    pub(super) fn holds(&mut self, arg: TyId, bound: &TTIRBound, name: &str, at: TIRExprId) {
        // A region is another pass's, and a type nobody worked out has been
        // reported once already.
        let TTIRBound::Trait(want) = bound else { return };
        // Followed first: a hole that was filled still reads as one in the
        // arena, and what filled it is what is being held to the bound.
        let arg = self.types.shallow(arg);
        if matches!(self.types.get(arg), Ty::Var(_) | Ty::Error) {
            return;
        }
        let Ty::Named { item: held, .. } = self.types.get(*want).clone() else { return };
        if self.answers_to(arg, held) {
            return;
        }
        let (arg, held) = (self.spell(arg), self.spell(*want));
        self.errors.push(
            Diagnostic::error(format!("`{}` does not answer `{}`", arg, held), self.at(at))
                .with_label(format!("`{}` is held to it here", name))
                .with_help(format!("`impl {} for {}` is how a type says it does", held, arg)),
        );
    }

    // Whether a type answers a trait: an impl of it written for that type, or
    // -- where the type is a parameter of the declaration being walked -- a
    // bound saying it will be. A generic holding another generic to a trait is
    // answered by the caller and not here.
    fn answers_to(&mut self, arg: TyId, want: TTIRItemId) -> bool {
        let arg = self.types.shallow(arg);
        if let Ty::Param { index, .. } = self.types.get(arg).clone() {
            return self.param_bounds(index).iter().any(|bound| {
                matches!(bound, TTIRBound::Trait(held)
                    if matches!(self.types.get(*held), Ty::Named { item, .. } if *item == want))
            });
        }
        let Some(written) = self.answers.get(&want) else { return false };
        let held = head_of(self.types.get(arg));
        written.clone().iter().any(|&subject| head_of(self.types.get(subject)) == held)
    }

    // What the declaration being walked holds its own parameter at `index` to.
    // Carried on the walk rather than searched for -- see `Lowerer::bounds`.
    pub(super) fn param_bounds(&self, index: usize) -> Vec<TTIRBound> {
        self.bounds.get(index).cloned().unwrap_or_default()
    }
}

// What a type is, for asking whether an impl was written for it. A declaration
// by the one it is, and anything else by itself: `impl Copy for i32` is written
// for the primitive and not for a name.
#[derive(PartialEq, Eq)]
enum Head {
    Named(TTIRItemId),
    Exact(String),
}

fn head_of(ty: &Ty) -> Head {
    match ty {
        Ty::Named { item, .. } => Head::Named(*item),
        other => Head::Exact(format!("{:?}", other)),
    }
}
