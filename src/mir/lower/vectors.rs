// The four that are about several values at once.
//
// These come down almost unchanged, and that is the point rather than a
// shortcut. `sir::opt` built them by asking `sir::target` what the machine
// could do to several at a time, so a `Pack` that exists is one a machine has
// an instruction for -- the deciding was done there, against the same
// description this stage allocates against. Lowering them is putting the same
// four in the machine's vocabulary.
//
// The one that changes is `Lanes`. In the SIR it reads a run of neighbouring
// elements out of an aggregate *value*; here that is a load of several widths
// at once from an address, which is what the machine actually does. `sir::opt`
// says as much in its own notes -- "a run read straight out of memory would
// need the load and the extraction to be one instruction" -- and this is where
// the two become one, because here there is an address to load from.

use crate::sir::sir_nodes::*;

use super::super::mir_nodes::*;
use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn vector(&mut self, inst: &SIRInst) {
        let (line, col) = (inst.line, inst.col);

        // The write makes nothing. Not a `Store` with a wide value: a store
        // writes one place and this writes a run of them, which is the
        // difference every pass that asks what it wrote has to see.
        if let SIRInstKind::VecStore { to, value } = &inst.kind {
            let (to, value) = (self.of(*to), self.of(*value));
            self.effect(MIRInstKind::VecStore { to, value }, line, col);
            return;
        }

        let Some(value) = inst.def else { return };
        let def = self.of(value);

        match &inst.kind {
            // Several values side by side, and the way a scalar joins them: the
            // same register named as many times as there are lanes.
            SIRInstKind::Pack(held) => {
                let held: Vec<MIRRegId> = held.iter().map(|&of| self.of(of)).collect();
                self.making(def, MIRInstKind::Pack(held), line, col);
            }

            // And one back out, for a use that was not part of the group.
            SIRInstKind::Lane { of, at } => {
                let of = self.of(*of);
                self.making(def, MIRInstKind::Lane { of, at: *at }, line, col);
            }

            // A run of neighbouring elements, read at once. `at` is the first
            // of them and `lanes` says how many, so what is read starts a
            // stride times `at` along and is that many widths wide.
            SIRInstKind::Lanes { of, at, lanes } => {
                let (of, at, lanes) = (*of, *at, *lanes);
                let want = self.ty_of(value);
                let one = self.bytes_of(want).max(1);
                let base = self.of(of);
                let from = self.push(
                    MIRInstKind::Offset { base, bytes: (at as usize * one) as i64 },
                    line,
                    col,
                );
                self.making(
                    def,
                    MIRInstKind::VecLoad { from, bytes: one, lanes },
                    line,
                    col,
                );
            }

            _ => self.making(def, MIRInstKind::Undef, line, col),
        }
    }
}
