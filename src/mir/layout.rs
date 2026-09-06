// What a type takes, and where each of its parts sits.
//
// This is the question `sir::target` names and declines: "what a structure or a
// run takes is a layout question nothing in this compiler has answered yet"
// (`size`, in that file). Nothing needed the answer before, because nothing
// before this reached for a field by anything but its number. A machine has no
// numbers for fields -- it has an address and a displacement -- so the number
// has to become a count of bytes, and that is what is worked out here.
//
// Nothing in the language says how. There is no `%repr`, so no declaration
// asks for an order, and that leaves the choice free. It is made the dull way:
// **fields stay in the order they were written**, each at the next offset its
// own alignment allows. Reordering them to pack tighter is a real saving and a
// real cost -- the layout stops being something a reader can work out from the
// declaration -- and the cost is the one that matters while there is nothing to
// measure the saving with.
//
// The answers are `Option`, and the reason is a single one: a type parameter
// with nothing to say what it stands for. `mir::mono` is what leaves none, and
// until it has run a generic body is full of them. `None` is that and nothing
// else, so a caller that has monomorphised may say so by unwrapping -- which is
// the same shape `sir::target::size` already has, and for a milder version of
// the same reason.
//
// The one other way to get `None` is a type that holds itself. `struct A { a: A }`
// has no size, and the walk below would look for it forever, so the types being
// worked out are kept on a stack and one that comes round again is refused.

use std::collections::HashMap;

use crate::sir::target;
use crate::tir::tir_nodes::TIRPrim;
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRPayload, TTIRProgram, Ty, TyId};

use super::machine::Machine;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub bytes: usize,
    pub align: usize,
    pub shape: Shape,
}

// How the bytes are arranged, for the lowering that has to reach into them.
// The size and the alignment are enough to *hold* a value; this is what is
// needed to read a piece of one out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    // One value, in one register.
    Scalar,
    // Nothing to hold: `null`, `never`, and a structure with no fields.
    Empty,
    // A pointer and a length side by side -- a run, a string -- or a pointer
    // and a second pointer, which is what a fn value and a trait both are.
    Fat,
    // One offset per field, in the order the declaration wrote them. A tuple
    // is this too: a tuple is a structure whose fields are numbered.
    Fields(Vec<usize>),
    // Every element the same, so one stride answers for all of them rather
    // than an offset each. A run of a thousand is one entry here.
    Elements { stride: usize, len: u64 },
    // A tag saying which variant, then the payload. The offsets are from the
    // start of the whole value and not from the start of the payload, because
    // an address is what the lowering has in hand and one addition is fewer
    // than two.
    Tagged {
        tag:      usize,
        variants: Vec<Vec<usize>>,
    },
}

pub struct Layouts<'a> {
    ttir:    &'a TTIRProgram,
    machine: Machine,
    // Worked out once. Only the types asked with nothing standing in for a
    // parameter go in: a `Held<T>` laid out against one argument and against
    // another are two answers under one `TyId`, and caching either would be
    // wrong for the other.
    held:    HashMap<TyId, Layout>,
    // What is being worked out, innermost last. A type that holds itself comes
    // round again, and coming round again is the only way it can.
    doing:   Vec<TyId>,
}

impl<'a> Layouts<'a> {
    pub fn new(ttir: &'a TTIRProgram, machine: Machine) -> Layouts<'a> {
        Layouts { ttir, machine, held: HashMap::new(), doing: Vec::new() }
    }

    // What one of `ty` takes and how it is arranged.
    pub fn of(&mut self, ty: TyId) -> Option<Layout> {
        self.of_in(ty, &[])
    }

    pub fn bytes(&mut self, ty: TyId) -> Option<usize> {
        Some(self.of(ty)?.bytes)
    }

    pub fn align(&mut self, ty: TyId) -> Option<usize> {
        Some(self.of(ty)?.align)
    }

    // How far apart two of them are in a run of them, which is the size rounded
    // up to the alignment. It is what an index is multiplied by and it is not
    // always the size: three bytes with a four-byte alignment sit four apart.
    pub fn stride(&mut self, ty: TyId) -> Option<usize> {
        let held = self.of(ty)?;
        Some(up(held.bytes, held.align))
    }

    // Where one field of a structure or a tuple begins.
    pub fn field(&mut self, ty: TyId, index: usize) -> Option<usize> {
        match self.of(ty)?.shape {
            Shape::Fields(at) => at.get(index).copied(),
            _ => None,
        }
    }

    // How wide the number saying which variant is. The number itself is the
    // checker's -- `TTIRVariant::value` is "worked out by the checker whether
    // it was written or not" -- so nothing here invents one; what is chosen is
    // only how much room it needs.
    pub fn tag(&mut self, ty: TyId) -> Option<usize> {
        match self.of(ty)?.shape {
            Shape::Tagged { tag, .. } => Some(tag),
            _ => None,
        }
    }

    // Where one field of one variant's payload begins, from the start of the
    // whole value.
    pub fn payload(&mut self, ty: TyId, variant: usize, index: usize) -> Option<usize> {
        match self.of(ty)?.shape {
            Shape::Tagged { variants, .. } => variants.get(variant)?.get(index).copied(),
            _ => None,
        }
    }

    // ---- The walk ----------------------------------------------------------

    // `env` is what the type parameters in hand stand for, by their index. It
    // is the declaration's argument list where one is being reached through and
    // empty everywhere else, which is what makes a `Param` with an empty `env`
    // the one thing that has no answer.
    // `pub(super)` for `mir::shape`, which walks the same types looking for a
    // different answer -- where the pointers are rather than how big it is --
    // and has to walk them in the same environment or a generic's field would
    // come out at the wrong offset.
    pub(super) fn of_in(&mut self, ty: TyId, env: &[TyId]) -> Option<Layout> {
        if env.is_empty() {
            if let Some(held) = self.held.get(&ty) {
                return Some(held.clone());
            }
            // Only worth guarding where the answer is cached, which is the same
            // condition: a type reaches itself through its own declaration, and
            // a declaration is reached with no environment of its own until its
            // fields are.
            if self.doing.contains(&ty) {
                return None;
            }
            self.doing.push(ty);
        }
        let made = self.work_out(ty, env);
        if env.is_empty() {
            self.doing.pop();
            if let Some(made) = &made {
                self.held.insert(ty, made.clone());
            }
        }
        made
    }

    fn work_out(&mut self, ty: TyId, env: &[TyId]) -> Option<Layout> {
        match self.ttir.types.get(ty)?.clone() {
            Ty::Prim(p) => Some(self.primitive(p)),

            // A parameter stands for whatever the declaration was handed. With
            // nothing in hand there is no answer, and that is the `None` the
            // header is about.
            Ty::Param { index, .. } => {
                let stands = *env.get(index)?;
                self.of_in(stands, &[])
            }

            // A reference to a trait object is two words: where the value is,
            // and where the routines that answer for it are. It is the one
            // reference that is not one address, for the reason a run is not:
            // what it refers to has no width of its own, so something has to
            // travel beside the address, and for a run that is the length and
            // here it is the table.
            Ty::Ref { inner, .. } | Ty::Ptr(inner)
                if matches!(self.ttir.types.get(inner), Some(Ty::Dyn(_))) =>
            {
                Some(self.fat())
            }

            // A reference and a pointer are one address. So is a `gc` value:
            // what the collector hands out is a handle, and how wide a handle
            // is is the one thing about the collector this has to agree with.
            Ty::Ref { .. } | Ty::Ptr(_) | Ty::GC(_) => Some(self.word()),

            // And a trait object on its own has no layout at all, which is
            // what makes it a thing nothing can hold: how wide one is is not
            // a question with an answer. `sema` refuses it where a value is
            // wanted, so reaching here is a program already turned down.
            Ty::Dyn(_) => None,

            // A run is a pointer and a length; a fn value is a pointer to the
            // code and a pointer to what it captured. Two words either way.
            Ty::Run(_) | Ty::Fn { .. } => Some(self.fat()),

            Ty::Array { elem, len } => {
                let one = self.of_in(elem, env)?;
                let stride = up(one.bytes, one.align);
                Some(Layout {
                    bytes: stride.checked_mul(len as usize)?,
                    align: one.align,
                    shape: Shape::Elements { stride, len },
                })
            }

            Ty::Tuple(parts) => self.fields(&parts, env),

            Ty::Named { item, args, .. } => self.named(item, &args, env),

            // Neither survives a program the checker accepted: a hole is filled
            // or reported by `sema::types::Types::finish`, and an `Error` is
            // what a body that was refused holds. Reaching one here means an
            // earlier pass let a refused program through, so there is nothing
            // to lay out and saying so is the honest answer.
            Ty::Var(_) | Ty::Error => None,
        }
    }

    fn named(&mut self, item: usize, args: &[TyId], env: &[TyId]) -> Option<Layout> {
        // The arguments are written where the *use* is, so they are worked out
        // in the environment of the use and become the environment of the
        // declaration. `Held<T>` inside `Pair<T>` is what needs this: the `T`
        // handed on is the outer one.
        let handed: Vec<TyId> = args
            .iter()
            .map(|&arg| match self.ttir.types.get(arg) {
                Some(Ty::Param { index, .. }) => env.get(*index).copied().unwrap_or(arg),
                _ => arg,
            })
            .collect();

        match &self.ttir.items.get(item)?.kind {
            TTIRItemKind::Struct { fields, .. } => {
                let tys: Vec<TyId> = fields.iter().map(|f| f.ty).collect();
                self.fields(&tys, &handed)
            }
            TTIRItemKind::Enum { variants, .. } => {
                let payloads: Vec<Vec<TyId>> =
                    variants.iter().map(|v| payload_types(&v.payload)).collect();
                let values: Vec<i64> = variants.iter().map(|v| v.value).collect();
                self.tagged(&payloads, &values, &handed)
            }
            // A trait as a type is what it points at and what answers for it.
            TTIRItemKind::Trait { .. } => Some(self.fat()),
            // Everything else a name can be is not a type, so nothing names one
            // here and reaching this is a bug further up rather than a shape.
            _ => None,
        }
    }

    // One after another, each at the next offset its own alignment allows, and
    // the whole rounded up so that a run of them keeps every one of them
    // aligned.
    fn fields(&mut self, tys: &[TyId], env: &[TyId]) -> Option<Layout> {
        let mut at = 0usize;
        let mut align = 1usize;
        let mut offsets = Vec::with_capacity(tys.len());
        for &ty in tys {
            let one = self.of_in(ty, env)?;
            at = up(at, one.align);
            offsets.push(at);
            at = at.checked_add(one.bytes)?;
            align = align.max(one.align);
        }
        let bytes = up(at, align);
        let shape = if tys.is_empty() { Shape::Empty } else { Shape::Fields(offsets) };
        Some(Layout { bytes, align, shape })
    }

    // The tag, then room for the largest variant. Every variant's payload
    // starts at the same place, which is what lets a read of one be an offset
    // that does not depend on which variant it turned out to be -- the
    // discriminant is tested first, and by then the address is already worked
    // out.
    fn tagged(
        &mut self,
        payloads: &[Vec<TyId>],
        values: &[i64],
        env: &[TyId],
    ) -> Option<Layout> {
        if payloads.is_empty() {
            // No variants, so no value of it exists. Nothing to hold.
            return Some(Layout { bytes: 0, align: 1, shape: Shape::Empty });
        }
        let tag = tag_bytes(values);

        // Every variant laid out on its own first, so that the widest
        // alignment among all of them is known before any offset is fixed.
        let mut laid = Vec::with_capacity(payloads.len());
        let mut align = tag;
        for fields in payloads {
            let one = self.fields(fields, env)?;
            align = align.max(one.align);
            laid.push(one);
        }

        let at = up(tag, align);
        let mut widest = 0usize;
        let mut variants = Vec::with_capacity(laid.len());
        for one in &laid {
            let offsets = match &one.shape {
                Shape::Fields(offsets) => offsets.iter().map(|off| at + off).collect(),
                // A variant with no payload is the tag and nothing else.
                _ => Vec::new(),
            };
            variants.push(offsets);
            widest = widest.max(one.bytes);
        }

        Some(Layout {
            bytes: up(at.checked_add(widest)?, align),
            align,
            shape: Shape::Tagged { tag, variants },
        })
    }

    // ---- The small ones ----------------------------------------------------

    fn primitive(&self, p: TIRPrim) -> Layout {
        match p {
            // A string is a pointer and a length, like every other run of
            // bytes whose length is not in the type.
            TIRPrim::Str => self.fat(),
            // `null` carries no information and `never` has no values, so
            // neither takes any room. Both still have a type, which is why
            // they are laid out at all rather than refused.
            TIRPrim::Null | TIRPrim::Never => Layout {
                bytes: 0,
                align: 1,
                shape: Shape::Empty,
            },
            _ => {
                // Every other primitive is named after its width (§6), so the
                // language has already answered this and `sir::target` already
                // wrote the answer down.
                let bytes = target::size_of(p).unwrap_or(self.machine.word);
                Layout { bytes, align: bytes, shape: Shape::Scalar }
            }
        }
    }

    fn word(&self) -> Layout {
        Layout {
            bytes: self.machine.word,
            align: self.machine.word,
            shape: Shape::Scalar,
        }
    }

    fn fat(&self) -> Layout {
        Layout {
            bytes: self.machine.word * 2,
            align: self.machine.word,
            shape: Shape::Fat,
        }
    }
}

// The next offset at or after `n` that `a` divides.
fn up(n: usize, a: usize) -> usize {
    if a == 0 { n } else { n.div_ceil(a) * a }
}

// How wide the tag has to be to hold every value the checker gave a variant.
// The narrowest that fits, because an enum of three things should not carry
// eight bytes to say which -- and signed where one was written negative, since
// a written discriminant may be.
fn tag_bytes(values: &[i64]) -> usize {
    let low = values.iter().copied().min().unwrap_or(0);
    let high = values.iter().copied().max().unwrap_or(0);
    for bytes in [1usize, 2, 4] {
        let bits = bytes * 8;
        let (min, max) = if low < 0 {
            (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1)
        } else {
            (0, (1i64 << bits) - 1)
        };
        if low >= min && high <= max {
            return bytes;
        }
    }
    8
}

// What one variant holds, as a list of types. The three payload shapes differ
// in what a reader writes and not in what is stored, so they become one list
// here and nothing downstream asks which was written.
fn payload_types(payload: &TTIRPayload) -> Vec<TyId> {
    match payload {
        TTIRPayload::None => Vec::new(),
        TTIRPayload::Tuple(tys) => tys.clone(),
        TTIRPayload::Named(fields) => fields.iter().map(|f| f.ty).collect(),
    }
}

#[cfg(test)]
mod tests;
