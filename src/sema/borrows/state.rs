// What the walk carries with it.
//
// Five small types, and each of them is a fact the walk needs at a point in
// the program rather than a fact about the program. What is still in a place
// (`State`, `Gone`); which borrows are in hand and until when (`Held`);
// whether the path being walked came back at all (`Flow`); and what a use of
// something was doing, which is the four names §2 gives (`Use`).
//
// `Maybe` is the one worth reading twice. Two paths of an `if` may disagree
// about whether a move happened, and that disagreement is its own answer: it
// is not "moved" and it is not "there", and guessing either would turn down a
// program that is fine or let through one that is not.

use std::collections::HashMap;

use crate::error::Span;
use crate::tir::tir_nodes::TIRRefOp;
use crate::tir::ttir_nodes::TTIRExprId;

use super::place::Place;

// Whether the value in a place is still the place's. A move takes it away, and
// the two paths of an `if` may disagree about whether one happened -- which is
// its own answer and not a guess at one of the other two.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum State {
    Moved { line: usize, col: usize },
    Maybe { line: usize, col: usize },
}

impl State {
    pub(super) fn at(self) -> Span {
        match self {
            State::Moved { line, col } | State::Maybe { line, col } => Span::at(line, col),
        }
    }

    pub(super) fn certain(self) -> bool {
        matches!(self, State::Moved { .. })
    }
}

// What has gone, and from where. A place not in here is still whole: the map
// holds what is unusual, so an untouched body carries nothing.
#[derive(Debug, Clone, Default, PartialEq)]
pub(super) struct Gone(HashMap<Place, State>);

impl Gone {
    // What is known about a place, taking the nearest thing that covers it: `p`
    // having gone is `p.x` having gone, since the value `p.x` was part of went
    // with it.
    pub(super) fn of(&self, place: &Place) -> Option<State> {
        if let Some(&held) = self.0.get(place) {
            return Some(held);
        }
        // A prefix of this place, which is a move of something this was part of.
        self.0
            .iter()
            .filter(|(held, _)| {
                held.root == place.root
                    && held.path.len() < place.path.len()
                    && held.path[..] == place.path[..held.path.len()]
            })
            .map(|(_, &state)| state)
            .max_by_key(|state| state.certain())
    }

    pub(super) fn moved(&mut self, place: Place, line: usize, col: usize) {
        self.0.insert(place, State::Moved { line, col });
    }

    // Filled again. A moved-from local may be given another value, and what was
    // reached through it is whole again with it.
    pub(super) fn filled(&mut self, place: &Place) {
        self.0.retain(|held, _| !held.conflicts(place));
    }

    // Two paths met. A place gone down one of them and not the other is gone
    // for neither and whole for neither, which is what `Maybe` is for.
    pub(super) fn join(&mut self, other: &Gone) {
        for (place, &there) in &other.0 {
            match self.0.get(place).copied() {
                None => {
                    let (line, col) = (there.at().line, there.at().col);
                    self.0.insert(place.clone(), State::Maybe { line, col });
                }
                Some(here) if here.certain() && !there.certain() => {
                    self.0.insert(place.clone(), there);
                }
                Some(_) => {}
            }
        }
        // And a place gone here but not there is only a maybe now.
        let elsewhere: Vec<Place> = self
            .0
            .keys()
            .filter(|place| !other.0.contains_key(*place))
            .cloned()
            .collect();
        for place in elsewhere {
            if let Some(State::Moved { line, col }) = self.0.get(&place).copied() {
                self.0.insert(place, State::Maybe { line, col });
            }
        }
    }
}

// ---- Borrows in hand ------------------------------------------------------

// One reference, held from where it was taken to the end of the block that took
// it. There is no region here: how long a reference is good for is another
// pass's, and the block it stands in is what this has instead.
#[derive(Debug, Clone)]
pub(super) struct Held {
    pub(super) place: Place,
    pub(super) op:    TIRRefOp,
    pub(super) line:  usize,
    pub(super) col:   usize,
    // The last moment anything can reach through it. A borrow bound to a slot
    // dies where that slot is last used, which is what makes this sharper than
    // "the end of the block": `let r = &x; let n = r; let m = *x` is three
    // lines of which only the first two are about `r`.
    //
    // `usize::MAX` for one that reached no slot: nothing can read it, so
    // nothing says when it stops being read, and the block is the answer.
    pub(super) until: usize,
    // The expression that took it, which is how `reaching` says whether it got
    // as far as the slot a `let` was filling.
    pub(super) at:    TTIRExprId,
}

// ---- Where the walk got to ------------------------------------------------

// Whether what was walked came back. `return`, `break` and `continue` do not,
// and neither does anything after them -- which is what makes them expressions
// of type `never` (§3) and what keeps a path that left out of a join.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Flow {
    Normal,
    Left,
}

impl Flow {
    pub(super) fn left(self) -> bool {
        self == Flow::Left
    }
}

// What a use of a moved value was doing, which is the four §2 names: "reading a
// after that is refused where it is written, and so is passing it, returning it
// or assigning through it".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Use {
    Read,
    Pass,
    Return,
    Assign,
}

impl Use {
    pub(super) fn word(self) -> &'static str {
        match self {
            Use::Read => "this reads it",
            Use::Pass => "this passes it",
            Use::Return => "this returns it",
            Use::Assign => "this assigns through it",
        }
    }
}
