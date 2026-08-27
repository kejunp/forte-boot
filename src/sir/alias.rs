// Whether two addresses may be the same address.
//
// Everything a pass wants to do with memory turns on this one question and
// cannot be done without an answer to it. Lifting a load out of a loop is only
// sound if nothing in the loop writes where it reads; putting the value a
// store wrote into the load below it is only sound if nothing between them
// wrote there instead; and running two turns of a loop at once is only sound
// if neither writes what the other reads. Before this file, `sir::opt`
// answered all three the only way a pass with no analysis can: a loop that
// wrote anywhere was a loop that might have written everywhere.
//
// The answer here has two halves, and each is worth about as much as the
// other.
//
// The first is the shape of the address. An address in the SIR is a root and a
// path into it: `Addr` names a slot of the frame, `ItemAddr` a global,
// `SelfAddr` the receiver, and the three `*Addr` projections step into
// whichever it was. Two addresses off different roots are different addresses,
// and two off one root are different as soon as their paths part -- `p.x` and
// `p.y` are two places whatever `p` is, and so are `xs[0]` and `xs[1]`. That
// much is structural and needs nothing but the instructions.
//
// The second is what an address that this body did not build might be. A value
// handed in as a parameter, found by a load, or given back by a call is an
// address with no root here, and it could be anything -- except a slot of this
// frame whose address never went anywhere it could have been kept. That is an
// *escape* analysis, and it is what gives the whole thing teeth: a local array
// nobody took a reference to is a place no call and no unknown pointer can
// reach, so a loop over it may be reasoned about even where it calls out.
//
// Which is not the same rule `sir::promote` applies, though it reads like it.
// That pass asks whether a slot is ever reached by anything but a load or a
// store, and a projection is such a thing -- so every slot with a field or an
// element read out of it stays in the frame and arrives here. This asks the
// narrower question: whether the address is ever *kept*. A projection is not
// keeping it, and neither is loading through it, so the slots this can still
// say something about are exactly the ones that pass had to give up on.
//
// Everything unproven is an alias. `may` says yes wherever it cannot say no,
// which is what makes a pass built on it correct before it is clever.

use crate::tir::ttir_nodes::TTIRItemId;

use super::sir_nodes::*;

// How deep a projection may be followed before this gives up and calls the
// address unknown. A path is as deep as `a.b.c[i].d` is long; the bound is for
// a graph that is not a graph.
const DEEP: usize = 32;

// Where an address starts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base {
    Slot(SIRSlotId),
    Item(TTIRItemId),
    Receiver,
    // An address this body did not build: a parameter, what a load found, what
    // a call handed back, what a phi joined. Two of them are one address only
    // if they are one value.
    Elsewhere(SIRValueId),
}

// One step into it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    Field(usize),
    Tuple(u64),
    // An element, by the value that says which -- and by the number, where
    // that value is a literal. The number is what makes `xs[0]` and `xs[1]`
    // two places; the value is what makes `xs[i]` and `xs[i]` one.
    At(Option<i64>, SIRValueId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Place {
    pub base: Base,
    pub path: Vec<Step>,
}

pub struct Alias {
    // Every value read as an address, by the address it is. A value that is
    // not one gets a place too -- `Elsewhere` and no path -- because asking is
    // cheaper than knowing which values are addresses, and nothing asks about
    // a value that is not one.
    places:  Vec<Place>,
    // By slot: whether the address of it ever reaches somewhere it could be
    // kept, which is what stops this saying anything about it.
    escapes: Vec<bool>,
}

impl Alias {
    pub fn of(body: &SIRBody) -> Alias {
        let lits = literals(body);
        let made = made(body);
        let places: Vec<Place> =
            (0..body.values.len()).map(|value| place_of(&made, &lits, value)).collect();
        let escapes = escapes(body, &places);
        Alias { places, escapes }
    }

    pub fn place(&self, value: SIRValueId) -> Option<&Place> {
        self.places.get(value)
    }

    // Whether the slot the address is off is one nothing else can reach: a
    // local nobody kept the address of, which a call cannot write and an
    // unknown pointer cannot be. The one question a pass asks about a call.
    pub fn own(&self, value: SIRValueId) -> bool {
        match self.places.get(value).map(|p| p.base) {
            Some(Base::Slot(slot)) => !self.escapes[slot],
            _ => false,
        }
    }

    // Whether the two may be the same address. Yes wherever it cannot be shown
    // that they are not.
    pub fn may(&self, a: SIRValueId, b: SIRValueId) -> bool {
        if a == b {
            return true;
        }
        let (Some(x), Some(y)) = (self.places.get(a), self.places.get(b)) else {
            return true;
        };
        if !self.roots(x.base, y.base) {
            return false;
        }
        // Off one root, and apart as soon as one step says so. A path that
        // runs out first is the other's prefix, which is one place holding the
        // other -- and holding it is enough to be written by a write to it.
        for (step, held) in x.path.iter().zip(y.path.iter()) {
            if apart(step, held) {
                return false;
            }
        }
        true
    }

    // And whether they are certainly the one address, which is what putting
    // the value of a store into the load below it needs. Nothing is `must`
    // unless every step of it is known.
    pub fn must(&self, a: SIRValueId, b: SIRValueId) -> bool {
        if a == b {
            return true;
        }
        let (Some(x), Some(y)) = (self.places.get(a), self.places.get(b)) else {
            return false;
        };
        if x.base != y.base || x.path.len() != y.path.len() {
            return false;
        }
        x.path.iter().zip(y.path.iter()).all(|(step, held)| together(step, held))
    }

    // Whether two roots may be the one place.
    fn roots(&self, a: Base, b: Base) -> bool {
        match (a, b) {
            // A slot is a place in this frame, and two of them are two places.
            (Base::Slot(x), Base::Slot(y)) => x == y,
            (Base::Item(x), Base::Item(y)) => x == y,
            (Base::Receiver, Base::Receiver) => true,
            // A global is not in the frame, and the receiver is the caller's:
            // it was handed over before this frame's slots existed, so it is
            // none of them.
            (Base::Slot(_), Base::Item(_) | Base::Receiver) => false,
            (Base::Item(_) | Base::Receiver, Base::Slot(_)) => false,
            // `GLOBAL.method()` is a receiver that is a global's address, so
            // these two are not two places.
            (Base::Item(_), Base::Receiver) | (Base::Receiver, Base::Item(_)) => true,
            // An address from elsewhere may be anything -- except a slot of
            // this frame that nothing ever kept the address of.
            (Base::Slot(slot), Base::Elsewhere(_)) | (Base::Elsewhere(_), Base::Slot(slot)) => {
                self.escapes[slot]
            }
            // Two addresses from elsewhere may be the one address whether or
            // not they are the one value, so there is nothing to compare.
            (Base::Elsewhere(_), _) | (_, Base::Elsewhere(_)) => true,
        }
    }
}

// Whether one step and another are certainly into different places.
fn apart(a: &Step, b: &Step) -> bool {
    match (a, b) {
        (Step::Field(x), Step::Field(y)) => x != y,
        (Step::Tuple(x), Step::Tuple(y)) => x != y,
        (Step::At(Some(x), _), Step::At(Some(y), _)) => x != y,
        // Two steps of different kinds are two ways of reaching into one
        // thing, and nothing here says a type could not be reached into both
        // ways. Saying nothing is the safe half of the answer.
        _ => false,
    }
}

// And whether they are certainly into the one place.
fn together(a: &Step, b: &Step) -> bool {
    match (a, b) {
        (Step::Field(x), Step::Field(y)) => x == y,
        (Step::Tuple(x), Step::Tuple(y)) => x == y,
        (Step::At(Some(x), _), Step::At(Some(y), _)) => x == y,
        // The same value indexing twice is the same element both times: a
        // value is made once and holds one thing.
        (Step::At(_, x), Step::At(_, y)) => x == y,
        _ => false,
    }
}

// The address a value is, followed down to whatever it starts at.
fn place_of(made: &[Option<SIRInstKind>], lits: &[Option<i64>], value: SIRValueId) -> Place {
    let mut path = Vec::new();
    let mut at = value;
    for _ in 0..DEEP {
        let base = match made.get(at) {
            Some(Some(SIRInstKind::Addr(slot))) => Base::Slot(*slot),
            Some(Some(SIRInstKind::ItemAddr(item))) => Base::Item(*item),
            Some(Some(SIRInstKind::SelfAddr)) => Base::Receiver,
            Some(Some(SIRInstKind::FieldAddr { base, index })) => {
                path.push(Step::Field(*index));
                at = *base;
                continue;
            }
            Some(Some(SIRInstKind::TupleAddr { base, index })) => {
                path.push(Step::Tuple(*index));
                at = *base;
                continue;
            }
            Some(Some(SIRInstKind::IndexAddr { base, index })) => {
                path.push(Step::At(lits.get(*index).copied().flatten(), *index));
                at = *base;
                continue;
            }
            _ => Base::Elsewhere(at),
        };
        path.reverse();
        return Place { base, path };
    }
    Place { base: Base::Elsewhere(value), path: Vec::new() }
}

// Which slots have an address that goes somewhere it could be kept.
//
// Three uses do not keep one: reading through it, writing through it, and
// stepping into it. Everything else does -- handing it to a call, storing it
// somewhere, joining it at a phi, giving it back -- and a projection carries
// the answer to whatever it was a projection of, which is what the second
// half of this closes over.
fn escapes(body: &SIRBody, places: &[Place]) -> Vec<bool> {
    let mut leaked = vec![false; body.values.len()];
    // A projection and the address it is into: if the projection is kept, so
    // is what it was a projection of.
    let mut steps: Vec<(SIRValueId, SIRValueId)> = Vec::new();
    let leak = |value: SIRValueId, leaked: &mut Vec<bool>| {
        if value < leaked.len() {
            leaked[value] = true;
        }
    };

    for block in &body.blocks {
        // A phi joins addresses this analysis stops being able to tell apart,
        // so what goes into one is treated as kept. Nothing the lowering
        // writes puts an address in a phi -- an `Addr` is made afresh at every
        // use -- so this costs nothing and closes the one hole that would
        // otherwise let a slot look unreachable while its address was still
        // in hand.
        for phi in &block.phis {
            for (_, value) in &phi.edges {
                leak(*value, &mut leaked);
            }
        }
        for inst in &block.insts {
            match &inst.kind {
                SIRInstKind::Load { .. } => {}
                SIRInstKind::Store { value, .. } => leak(*value, &mut leaked),
                SIRInstKind::FieldAddr { base, .. } | SIRInstKind::TupleAddr { base, .. } => {
                    if let Some(def) = inst.def {
                        steps.push((def, *base));
                    }
                }
                SIRInstKind::IndexAddr { base, index } => {
                    if let Some(def) = inst.def {
                        steps.push((def, *base));
                    }
                    leak(*index, &mut leaked);
                }
                other => {
                    for value in SIRBody::uses(other) {
                        leak(value, &mut leaked);
                    }
                }
            }
        }
        match &block.term {
            SIRTerm::Branch { cond, .. } => leak(*cond, &mut leaked),
            SIRTerm::Return(Some(value)) => leak(*value, &mut leaked),
            _ => {}
        }
    }

    // And down every projection to what it was into.
    let mut moved = true;
    while moved {
        moved = false;
        for &(def, base) in &steps {
            if leaked[def] && !leaked[base] {
                leaked[base] = true;
                moved = true;
            }
        }
    }

    let mut out = vec![false; body.slots.len()];
    for (value, kept) in leaked.iter().enumerate() {
        if !kept {
            continue;
        }
        if let Base::Slot(slot) = places[value].base {
            out[slot] = true;
        }
    }
    out
}

// What made each value, which is what a path is followed down.
fn made(body: &SIRBody) -> Vec<Option<SIRInstKind>> {
    let mut out = vec![None; body.values.len()];
    for block in &body.blocks {
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = Some(inst.kind.clone());
                }
            }
        }
    }
    out
}

// And which of them are numbers, which is what makes two elements two places.
fn literals(body: &SIRBody) -> Vec<Option<i64>> {
    let mut out = vec![None; body.values.len()];
    for block in &body.blocks {
        for inst in &block.insts {
            if let (Some(def), SIRInstKind::Literal(crate::tir::tir_nodes::TIRLit::Int(n))) =
                (inst.def, &inst.kind)
            {
                if def < out.len() {
                    out[def] = Some(*n);
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests;
