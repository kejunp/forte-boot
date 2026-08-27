// What a rule about borrowing is about, and how the walk finds one.
//
// A place is not a name. `p.x` and `p.y` are two places under one name and
// `*self` is one place under none, so every rule in this pass is written about
// a root and a way in from it rather than about a local -- which is what lets
// two fields of one structure be moved out of separately, and what makes
// crossing a reference something the shape can say.
//
// The two halves are here together because they answer each other. `Place` is
// what a rule compares; `place` is what turns an expression somebody wrote
// into one, or into nothing where the expression names no place at all, which
// is what a literal and a call do.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::TIRBinding;
use crate::tir::ttir_nodes::{
    TTIRExprId, TTIRExprKind, TTIRLocalId, Ty,
};

use super::Checker;

// What a rule about borrowing is about. Not a name: `p.x` and `p.y` are two
// places under one name, and `*self` is one place under none.
//
// The root is the slot it starts at and the path is the way in from there.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: TTIRLocalId,
    pub path: Vec<Step>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Step {
    // `.x`, by the index the resolver settled it to.
    Field(usize),
    // `.0`
    Tuple(u64),
    // `[i]`, and the index is not kept: `a[i]` and `a[j]` are one place here.
    // Whether two views of one array whose ranges do not meet are one place or
    // two is left open by §3, and this is the half that turns more down.
    Index,
    // Crossing a reference. Nothing in the source writes this -- "a reference
    // stands for the place it refers to and is read, called, indexed and
    // reached into exactly as that place is" (§3), so there is no operator for
    // it -- and the walk puts one in wherever a projection's base is a `Ty::Ref`.
    Deref,
}

impl Place {
    pub(super) fn of(root: TTIRLocalId) -> Place {
        Place { root, path: Vec::new() }
    }

    fn then(&self, step: Step) -> Place {
        let mut path = self.path.clone();
        path.push(step);
        Place { root: self.root, path }
    }

    // Whether touching one touches the other. One place conflicts with another
    // where they share a root and one way in is a prefix of the other: `p`
    // conflicts with `p.x`, and `p.x` with nothing of `p.y`.
    //
    // Distinct fields not conflicting is the other half of what §3 leaves open,
    // decided the way that turns fewer programs down.
    pub fn conflicts(&self, other: &Place) -> bool {
        if self.root != other.root {
            return false;
        }
        let shorter = self.path.len().min(other.path.len());
        self.path[..shorter] == other.path[..shorter]
    }
}

impl<'a> Checker<'a> {
    // The place an expression names, where it names one. A call names none, and
    // neither does a literal: "`&x` asks... any place at all, and a value with
    // no home of its own, which the compiler gives one" (§5).
    pub(super) fn place(&self, id: TTIRExprId) -> Option<Place> {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Local(local) => Some(Place::of(*local)),
            TTIRExprKind::Field { base, index } => {
                Some(self.reach(*base)?.then(Step::Field(*index)))
            }
            TTIRExprKind::TupleIndex { base, index } => {
                Some(self.reach(*base)?.then(Step::Tuple(*index)))
            }
            TTIRExprKind::Index { base, .. } => Some(self.reach(*base)?.then(Step::Index)),
            _ => None,
        }
    }

    // The base of a projection, with a `Deref` put in where it crosses a
    // reference. Nothing writes that step -- a reference is read and reached
    // into exactly as the place it refers to is (§3) -- so the type is the only
    // thing that says one happened.
    fn reach(&self, base: TTIRExprId) -> Option<Place> {
        let place = self.place(base)?;
        match &self.p.types[self.p.exprs[base].ty] {
            Ty::Ref { .. } => Some(place.then(Step::Deref)),
            _ => Some(place),
        }
    }

    // What to call a place in a message. The root's name and the way in, which
    // is what the reader wrote.
    pub(super) fn name(&self, place: &Place) -> String {
        let local = &self.p.bodies[self.body].locals[place.root];
        let mut out = match &local.name {
            TIRBinding::Name(name) => name.clone(),
            TIRBinding::Discard => "_".to_string(),
            TIRBinding::SelfRecv(..) => "self".to_string(),
        };
        for step in &place.path {
            match step {
                Step::Field(i) => out.push_str(&format!(".{}", i)),
                Step::Tuple(i) => out.push_str(&format!(".{}", i)),
                Step::Index => out.push_str("[..]"),
                // A reference is transparent, so nothing is written for one and
                // nothing is shown for one either.
                Step::Deref => {}
            }
        }
        out
    }

    pub(super) fn say(&mut self, d: Diagnostic) {
        if !self.quiet {
            self.errors.push(d);
        }
    }
}
