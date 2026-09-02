// Addresses, and what is read out of them and written into them.
//
// This is where a field stops being a name. The SIR reaches into a value with
// `FieldAddr { base, index }` and the index is the field's place in the
// declaration; here it is a number of bytes, and `mir::layout` is what turned
// the one into the other. After this nothing knows there was a field.
//
// The SIR draws a line this file has to keep: a *place* is an address and a
// *value* is what is at one. `FieldAddr` says where the field is; `Field` makes
// a copy of it. The two lower to the same offset, and then one stops and the
// other reads -- which is the only difference between them and is worth seeing
// written twice.
//
// What the header of `lower.rs` calls the one decision shows up here more than
// anywhere: whether a value is in a register or in the frame. `take` and `put`
// are where it is asked, and every read and write goes through one of them, so
// no case in this file has to remember which kind it has in hand.

use crate::sir::sir_nodes::*;

use super::super::mir_nodes::*;
use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn place(&mut self, inst: &SIRInst, at: SIRBlockId, i: usize) {
        let (line, col) = (inst.line, inst.col);

        // The two that write rather than make something.
        if let SIRInstKind::Store { to, value } = &inst.kind {
            let to = self.of(*to);
            self.put(to, *value, line, col);
            return;
        }

        let Some(value) = inst.def else { return };
        let def = self.of(value);

        match &inst.kind {
            // ---- Where something starts ------------------------------------

            // A slot of this frame. `sir::promote` has already taken out every
            // slot whose address went nowhere but a load or a store, so what is
            // left here is the ones that really need an address.
            SIRInstKind::Addr(slot) => {
                let slot = self.slot_of(*slot);
                self.making(def, MIRInstKind::Frame(slot), line, col);
            }

            // A global, or a declaration named as a place. Neither is a slot of
            // this frame, and both are things the linker knows.
            SIRInstKind::ItemAddr(_) => {
                let name = self.symbol_at(at, i).unwrap_or_default();
                self.making(def, MIRInstKind::Symbol(name), line, col);
            }

            SIRInstKind::SelfAddr => match self.receiver() {
                Some(held) => self.making(def, MIRInstKind::Move(held), line, col),
                None => self.making(def, MIRInstKind::Undef, line, col),
            },

            // ---- Reaching into one -----------------------------------------

            // A fixed number of bytes along, which is what a field is once the
            // layout has been worked out.
            SIRInstKind::FieldAddr { base, index } => {
                let bytes = self.offset_of(*base, *index);
                let base = self.of(*base);
                self.making(def, MIRInstKind::Offset { base, bytes }, line, col);
            }
            SIRInstKind::TupleAddr { base, index } => {
                let bytes = self.offset_of(*base, *index as usize);
                let base = self.of(*base);
                self.making(def, MIRInstKind::Offset { base, bytes }, line, col);
            }

            // And a number of bytes along that is not known until it runs. The
            // scale is the element's stride and not its size: three bytes with
            // a four-byte alignment sit four apart, and multiplying by three
            // would walk into the middle of the second one.
            // Where the elements begin, and then the index. The first half is
            // not `self.of(base)`: an array is its elements and a run is a
            // pointer to them, so a run indexed off its own address would read
            // the pointer and the length as the first two elements.
            SIRInstKind::IndexAddr { base, index } => {
                let scale = self.element_of(*base);
                let held = self.elements(*base, line, col);
                let index = self.of(*index);
                self.making(
                    def,
                    MIRInstKind::Scaled { base: held, index, scale },
                    line,
                    col,
                );
            }

            // ---- What is at one --------------------------------------------

            SIRInstKind::Load { from } => {
                let ty = self.ty_of(value);
                let from = self.of(*from);
                self.take(def, from, ty, line, col);
            }

            // The three reads out of a *value*. A value big enough to have
            // fields is one held by its address, so each is the offset above
            // and then a read -- the same two instructions the `*Addr` pair and
            // a `Load` would have been, written as one because the SIR wrote
            // them as one.
            SIRInstKind::Field { base, index } => {
                let bytes = self.offset_of(*base, *index);
                let base = self.of(*base);
                let ty = self.ty_of(value);
                let held = self.push(MIRInstKind::Offset { base, bytes }, line, col);
                self.take(def, held, ty, line, col);
            }
            SIRInstKind::TupleIndex { base, index } => {
                let bytes = self.offset_of(*base, *index as usize);
                let base = self.of(*base);
                let ty = self.ty_of(value);
                let held = self.push(MIRInstKind::Offset { base, bytes }, line, col);
                self.take(def, held, ty, line, col);
            }
            SIRInstKind::Index { base, index } => {
                let scale = self.element_of(*base);
                let from = self.elements(*base, line, col);
                let index = self.of(*index);
                let ty = self.ty_of(value);
                let held = self.push(
                    MIRInstKind::Scaled { base: from, index, scale },
                    line,
                    col,
                );
                self.take(def, held, ty, line, col);
            }

            // A slot read on a path that never wrote it. `sema` is where a read
            // of an unset name is turned down, so there is nothing to refuse
            // here and nothing to invent either.
            SIRInstKind::Undef => self.making(def, MIRInstKind::Undef, line, col),

            _ => self.making(def, MIRInstKind::Undef, line, col),
        }
    }

    // Where one field of whatever `base` points at begins.
    //
    // `base` is a place, so its type is a reference or a pointer to the thing
    // with the fields -- or is the thing itself, where the value was already
    // one held by its address. Both are followed, because which of the two the
    // SIR left depends on how the place was reached and neither is wrong.
    fn offset_of(&mut self, base: SIRValueId, index: usize) -> i64 {
        let ty = self.through(self.ty_of(base));
        self.field_at(ty, index)
    }

    // The stride of what a run holds, which is what an index is multiplied by.
    fn element_of(&mut self, base: SIRValueId) -> usize {
        // A pointer is asked before anything is stripped off it. It is the
        // front of a run of its own elements, so what an index steps by is the
        // element's stride -- and `through` below would have taken the `ptr`
        // away and left the element, which has no stride of its own and would
        // have been stepped over a word at a time.
        let held = self.ty_of(base);
        if let Some(crate::tir::ttir_nodes::Ty::Ptr(elem)) =
            self.made.ttir.types.get(held).cloned()
        {
            return self.stride_of(elem);
        }
        let ty = self.through(held);
        match self.laid(ty).shape {
            super::Shape::Elements { stride, .. } => stride,
            // A run and a string are a pointer and a length rather than the
            // elements themselves, so what is stepped through is whatever the
            // pointer half points at.
            _ => match self.elem_of(ty) {
                Some(elem) => self.stride_of(elem),
                None => self.word(),
            },
        }
    }

    // What a reference or a pointer is to. One layer and not all of them: `&&T`
    // is a reference to a reference, and reaching into it reaches into the
    // reference.
    fn through(&self, ty: crate::tir::ttir_nodes::TyId) -> crate::tir::ttir_nodes::TyId {
        use crate::tir::ttir_nodes::Ty;
        match self.made.ttir.types.get(ty) {
            Some(Ty::Ref { inner, .. }) | Some(Ty::Ptr(inner)) => *inner,
            _ => ty,
        }
    }

    // What a run, an array or a pointer holds one of.
    fn elem_of(
        &self,
        ty: crate::tir::ttir_nodes::TyId,
    ) -> Option<crate::tir::ttir_nodes::TyId> {
        use crate::tir::ttir_nodes::Ty;
        match self.made.ttir.types.get(ty)? {
            Ty::Run(elem) | Ty::Array { elem, .. } | Ty::Ptr(elem) => Some(*elem),
            Ty::Ref { inner, .. } => self.elem_of(*inner),
            _ => None,
        }
    }
}
