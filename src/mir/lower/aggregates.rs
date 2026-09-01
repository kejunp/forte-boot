// The things built out of several values, and the two questions a match asks
// of one.
//
// Every literal here comes to the same three steps: take room in the frame, put
// each part where the layout says it goes, and hand back the address. There is
// no other way to build one -- a structure of three words is not a thing a
// register holds -- so the only difference between a struct literal, a tuple, an
// array and a range is which offsets the parts go to, and all four of those
// come from `mir::layout`.
//
// An enum is the one with anything else to it. It is a tag and then a payload,
// and the payload of every variant begins at the same offset, so writing one is
// writing the tag and then the fields of that variant. Reading it back is the
// other two instructions here: `Discriminant` is a load of the tag, and
// `Payload` is a load at the offset for that variant's field -- which is only
// ever reached after the discriminant has already said it is that variant.

use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::TIRRangeOp;
use crate::tir::ttir_nodes::{TTIRItemKind, TyId};

use super::super::mir_nodes::*;
use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn aggregate(&mut self, inst: &SIRInst) {
        let (line, col) = (inst.line, inst.col);
        let Some(value) = inst.def else { return };
        let def = self.of(value);
        let ty = self.ty_of(value);

        match &inst.kind {
            // ---- Built out of parts ----------------------------------------

            SIRInstKind::StructLit { fields, .. } => {
                let held: Vec<SIRValueId> = fields.clone();
                self.built(def, ty, &held, line, col);
            }

            SIRInstKind::TupleLit(parts) => {
                let held = parts.clone();
                self.built(def, ty, &held, line, col);
            }

            // Every element the same width, so the offsets are a stride apart
            // rather than one per element -- an array of a thousand is a
            // thousand stores and not a thousand layout questions.
            SIRInstKind::ArrayLit(elems) => {
                let held = elems.clone();
                let stride = match self.laid(ty).shape {
                    super::Shape::Elements { stride, .. } => stride,
                    _ => held.first().map(|&e| self.ty_of(e)).map(|t| self.stride_of(t)).unwrap_or(1),
                };
                self.room_for(def, ty, line, col);
                for (at, &elem) in held.iter().enumerate() {
                    let bytes = (at * stride) as i64;
                    let to = self.push(MIRInstKind::Offset { base: def, bytes }, line, col);
                    self.put(to, elem, line, col);
                }
            }

            // A range is a structure the source has literal syntax for, so it
            // is built like one. Which of the four it was written as says only
            // which ends are there; the two that are get written and the two
            // that are not are left alone.
            SIRInstKind::Range { op, start, end } => {
                let (op, start, end) = (*op, *start, *end);
                self.room_for(def, ty, line, col);
                let mut at = 0i64;
                for held in [start, end].into_iter().flatten() {
                    let bytes = self.bytes_of(self.ty_of(held)).max(1);
                    let to = self.push(MIRInstKind::Offset { base: def, bytes: at }, line, col);
                    self.put(to, held, line, col);
                    at += bytes as i64;
                }
                let _ = op_of(op);
            }

            // ---- The one with a tag ----------------------------------------

            SIRInstKind::VariantLit { item, variant, fields } => {
                let (item, variant, fields) = (*item, *variant, fields.clone());
                self.room_for(def, ty, line, col);

                // The number is the checker's: `TTIRVariant::value` is worked
                // out whether it was written or not, and it is the same number
                // a `Discriminant` reads back.
                let tag = self.tag_of(ty);
                let number = self.number_of(item, variant);
                let held = self.push(MIRInstKind::Const(MIRConst::Int(number)), line, col);
                self.effect(MIRInstKind::Store { to: def, value: held, bytes: tag }, line, col);

                for (index, &field) in fields.iter().enumerate() {
                    let bytes = self.payload_at(ty, variant, index);
                    let to = self.push(MIRInstKind::Offset { base: def, bytes }, line, col);
                    self.put(to, field, line, col);
                }
            }

            // ---- And the two that read it back -----------------------------

            SIRInstKind::Discriminant(of) => {
                let held = self.ty_of(*of);
                let bytes = self.tag_of(held);
                let from = self.of(*of);
                self.making(def, MIRInstKind::Load { from, bytes }, line, col);
            }

            // Read once the discriminant has already said it is that variant.
            // Reading it before the test would be reading a field that is not
            // there, which is why the SIR keeps the two apart and why this can
            // be a plain offset.
            SIRInstKind::Payload { of, variant, index } => {
                let held = self.ty_of(*of);
                let bytes = self.payload_at(held, *variant, *index);
                let base = self.of(*of);
                let ty = self.ty_of(value);
                let at = self.push(MIRInstKind::Offset { base, bytes }, line, col);
                self.take(def, at, ty, line, col);
            }

            _ => self.making(def, MIRInstKind::Undef, line, col),
        }
    }

    // Room of its own, with the address in the register the value was given.
    fn room_for(&mut self, def: MIRRegId, ty: TyId, line: usize, col: usize) {
        let held = self.laid(ty);
        let name = format!("${}", self.frame_len());
        let slot = self.slot(name, held.bytes, held.align);
        self.making(def, MIRInstKind::Frame(slot), line, col);
    }

    // One field after another, each where the layout says. What a structure and
    // a tuple both are: the only thing that told them apart was whether the
    // fields had names, and by here neither has.
    fn built(
        &mut self,
        def: MIRRegId,
        ty: TyId,
        fields: &[SIRValueId],
        line: usize,
        col: usize,
    ) {
        self.room_for(def, ty, line, col);
        for (index, &field) in fields.iter().enumerate() {
            let bytes = self.field_at(ty, index);
            let to = self.push(MIRInstKind::Offset { base: def, bytes }, line, col);
            self.put(to, field, line, col);
        }
    }

    // What number stands for one variant. Worked out by the checker, so this
    // only fetches it.
    fn number_of(&self, item: usize, variant: usize) -> i64 {
        let Some(TTIRItemKind::Enum { variants, .. }) =
            self.made.ttir.items.get(item).map(|held| &held.kind)
        else {
            return variant as i64;
        };
        variants.get(variant).map(|held| held.value).unwrap_or(variant as i64)
    }
}

// Which of the four a range was written as. Nothing is done with it: both ends
// are written wherever they are there, and whether the far end is included is a
// question for whatever walks the range rather than for how it is stored.
fn op_of(op: TIRRangeOp) -> TIRRangeOp {
    op
}
