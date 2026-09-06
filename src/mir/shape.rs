// What a type is, written down for the runtime to read.
//
// `layout` answers how big a type is and where its parts sit, which is what
// the lowering needs to emit a load. The runtime needs something else about
// the same type: **which of its words hold pointers**. That is the question a
// collector cannot answer for itself -- an eight-byte word is an address or a
// number depending on nothing that is present at run time -- and it is the
// difference between a heap scanned precisely and a heap scanned by guessing.
//
// So a descriptor is emitted into the constant pool, once per type that needs
// one, under `__T` and the type's spelling. `fortec_rt::shape` reads it, and
// the layout below is written out in both files on purpose: they are compiled
// separately and nothing checks that they agree, so the two tables are meant
// to be read side by side.
//
//      +0   u64   bytes      what one value takes
//      +8   u64   align
//     +16   u64   words      how many words the map below covers
//     +24   u8    kind       how a key is hashed and ordered
//     +25   u8    indirect   whether a register holding one holds its address
//     +26   u8    [6]        nothing, so the map starts on a word
//     +32   u8    []         one bit per word, low bit of byte nought first;
//                            a one means that word holds a pointer
//
// The **kind** is the other half and is for the map and the set rather than
// the collector. Ordering two keys and hashing one are questions about what
// the bytes mean, and an address and a length cannot answer either. The
// general answer is a function pointer per type, and it would mean emitting
// three routines for every key type in the program before a map could hold
// anything. A small closed set of kinds covers what a key can be in this
// language and costs a byte.
//
// **An enum's map is the union over its variants.** Which variant a value
// holds is in the tag, and reading the tag to decide how to read the rest
// would make the map a program rather than a table. So a word that is a
// pointer in one variant and a number in another is called a pointer, and the
// marker reads it and finds it is not an address of anything. That is a real
// loss of precision and it is bounded: the runtime's lookup fails, nothing is
// marked, and the cost is one failed lookup per such word.
//
// **A code pointer is not a heap pointer**, and both are in here anyway. The
// first word of a fn value is the address of a symbol, which no span holds, so
// marking it costs a lookup that fails -- and leaving it out would mean
// knowing here which of a fat value's two words is which for four different
// fat types. The map is deliberately allowed to name more than it must; what
// it may never do is name less.

use crate::sema::names::Mangler;
use crate::tir::tir_nodes::TIRPrim;
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRPayload, TTIRProgram, Ty, TyId};

use super::layout::{Layouts, Shape};
use super::machine::Machine;

// How far the map is from the start.
pub const HEADER: usize = 32;

// What the bytes of a value mean, for the two operations that have to know.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Opaque = 0,
    Signed = 1,
    Unsigned = 2,
    Float = 3,
    Pointer = 4,
    Str = 5,
}

// A type that holds itself has no layout at all, so this cannot loop -- but a
// bound is cheap and a stack overflow in a compiler is a message nobody can
// act on.
const DEEPEST: usize = 32;

// The descriptor for one type, or `None` where the type has no layout: a
// parameter with nothing standing in for it, or a type that holds itself.
// After `mono` there are no parameters left, so a `None` here is the same bug
// `layout` reports.
pub fn describe(
    layouts: &mut Layouts<'_>,
    ttir: &TTIRProgram,
    machine: Machine,
    ty: TyId,
) -> Option<Vec<u8>> {
    let held = layouts.of(ty)?;
    let word = machine.word.max(1);
    let words = held.bytes.div_ceil(word);

    let mut at = Vec::new();
    walk(layouts, ttir, machine, ty, &[], 0, &mut at, 0);

    let mut out = vec![0u8; HEADER + words.div_ceil(8).max(1)];
    out[0..8].copy_from_slice(&(held.bytes as u64).to_le_bytes());
    out[8..16].copy_from_slice(&(held.align as u64).to_le_bytes());
    out[16..24].copy_from_slice(&(words as u64).to_le_bytes());
    out[24] = kind_of(ttir, ty) as u8;
    out[25] = u8::from(indirect(layouts, machine, ty));
    for offset in at {
        let which = offset / word;
        if which < words {
            out[HEADER + which / 8] |= 1 << (which % 8);
        }
    }
    Some(out)
}

// What a descriptor is called. The same construction `runtime::glue` uses for
// a release, for the same reason: the type is in the name because the name is
// the only place a linker can be told which one is meant.
pub fn symbol(mangler: &Mangler, ttir: &TTIRProgram, ty: TyId) -> String {
    let spelled = mangler.spell(ty, ttir);
    let mut out = String::from("__T");
    crate::sema::names::part(&spelled, &mut out);
    out
}

// A descriptor for a closure's environment, which is not a type anything
// declared. It is a run of addresses -- one per capture -- and nothing in the
// TTIR spells it, so it is built here rather than walked to.
//
// Every word is called a pointer, and most of them are not heap pointers at
// all: what a capture holds is the address of a slot in the enclosing frame
// (`mir::lower::calls`, which says why). The marker looks each one up, finds
// no span holds it, and moves on. Naming them costs that; not naming them
// would mean a capture of something on the heap was invisible.
pub fn environment(words: usize, machine: Machine) -> Vec<u8> {
    let word = machine.word.max(1);
    let mut out = vec![0u8; HEADER + words.div_ceil(8).max(1)];
    out[0..8].copy_from_slice(&((words * word) as u64).to_le_bytes());
    out[8..16].copy_from_slice(&(word as u64).to_le_bytes());
    out[16..24].copy_from_slice(&(words as u64).to_le_bytes());
    out[24] = Kind::Opaque as u8;
    out[25] = 1;
    for at in 0..words {
        out[HEADER + at / 8] |= 1 << (at % 8);
    }
    out
}

// ---- Where the pointers are ------------------------------------------------

// Every byte offset at which a word holding an address begins, relative to
// `base`. Written as offsets rather than word numbers because every caller has
// an offset in hand and none of them has a word number.
fn walk(
    layouts: &mut Layouts<'_>,
    ttir: &TTIRProgram,
    machine: Machine,
    ty: TyId,
    env: &[TyId],
    base: usize,
    out: &mut Vec<usize>,
    deep: usize,
) {
    if deep > DEEPEST {
        return;
    }
    let word = machine.word.max(1);
    let Some(held) = ttir.types.get(ty).cloned() else { return };

    match held {
        // A reference to a trait object is two words and only the first of
        // them is one the collector may follow: the second is the table,
        // which the assembler wrote into `.rodata` and no heap holds.
        // Naming it would be naming an address outside the heap as one to
        // walk into, which is the one thing a *precise* descriptor is for
        // not doing -- the roots are guessed at, and this is not a root.
        Ty::Ref { inner, .. } | Ty::Ptr(inner)
            if matches!(ttir.types.get(inner), Some(Ty::Dyn(_))) =>
        {
            out.push(base);
        }

        // The three that are one address, and the whole reason any of this
        // exists.
        Ty::Ref { .. } | Ty::Ptr(_) | Ty::GC(_) => out.push(base),

        // Nothing holds a bare one, so nothing describes one either.
        Ty::Dyn(_) => {}

        // Two words. Which of them is the address differs -- a run and a
        // string keep their data first and their length second, a fn value
        // and a trait keep two pointers -- and naming both is allowed where
        // naming too few is not.
        Ty::Run(_) | Ty::Fn { .. } => {
            out.push(base);
            out.push(base + word);
        }

        Ty::Prim(TIRPrim::Str) => {
            out.push(base);
        }
        Ty::Prim(_) => {}

        Ty::Param { index, .. } => {
            if let Some(&stands) = env.get(index) {
                walk(layouts, ttir, machine, stands, &[], base, out, deep + 1);
            }
        }

        Ty::Array { elem, len } => {
            // Worked out once for one element and then repeated. An array of a
            // million bytes would otherwise be a million walks to conclude
            // that a byte is not a pointer.
            let mut one = Vec::new();
            walk(layouts, ttir, machine, elem, env, 0, &mut one, deep + 1);
            if one.is_empty() {
                return;
            }
            let Some(stride) = layouts.of_in(elem, env).map(|h| up(h.bytes, h.align)) else {
                return;
            };
            for step in 0..len as usize {
                for offset in &one {
                    out.push(base + step * stride + offset);
                }
            }
        }

        Ty::Tuple(parts) => {
            let Some(laid) = layouts.of_in(ty, env) else { return };
            let Shape::Fields(offsets) = laid.shape else { return };
            for (at, part) in parts.iter().enumerate() {
                let Some(off) = offsets.get(at) else { continue };
                walk(layouts, ttir, machine, *part, env, base + off, out, deep + 1);
            }
        }

        Ty::Named { item, args, .. } => {
            named(layouts, ttir, machine, ty, item, &args, env, base, out, deep);
        }

        // Neither survives a program the checker accepted, and `layout` has
        // already said so with a `None`.
        Ty::Var(_) | Ty::Error => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn named(
    layouts: &mut Layouts<'_>,
    ttir: &TTIRProgram,
    machine: Machine,
    ty: TyId,
    item: usize,
    args: &[TyId],
    env: &[TyId],
    base: usize,
    out: &mut Vec<usize>,
    deep: usize,
) {
    // The arguments are written at the use, so they are read in the
    // environment of the use and become the environment of the declaration --
    // which is what `layout::named` does, and the two have to agree or a
    // generic's field is described at the wrong offset.
    let handed: Vec<TyId> = args
        .iter()
        .map(|&arg| match ttir.types.get(arg) {
            Some(Ty::Param { index, .. }) => env.get(*index).copied().unwrap_or(arg),
            _ => arg,
        })
        .collect();

    let Some(laid) = layouts.of_in(ty, env) else { return };
    let Some(kind) = ttir.items.get(item).map(|held| held.kind.clone()) else { return };

    match (kind, laid.shape) {
        (TTIRItemKind::Struct { fields, .. }, Shape::Fields(offsets)) => {
            for (at, field) in fields.iter().enumerate() {
                let Some(off) = offsets.get(at) else { continue };
                walk(layouts, ttir, machine, field.ty, &handed, base + off, out, deep + 1);
            }
        }

        // Every variant, because which one is in there is in the tag and this
        // is a table rather than a program -- see the header.
        (TTIRItemKind::Enum { variants, .. }, Shape::Tagged { variants: at, .. }) => {
            for (which, variant) in variants.iter().enumerate() {
                let Some(offsets) = at.get(which) else { continue };
                for (index, held) in payload_types(&variant.payload).iter().enumerate() {
                    let Some(off) = offsets.get(index) else { continue };
                    walk(layouts, ttir, machine, *held, &handed, base + off, out, deep + 1);
                }
            }
        }

        // What it points at and what answers for it: two words, both
        // addresses.
        (TTIRItemKind::Trait { .. }, _) => {
            out.push(base);
            out.push(base + machine.word.max(1));
        }

        _ => {}
    }
}

fn payload_types(payload: &TTIRPayload) -> Vec<TyId> {
    match payload {
        TTIRPayload::None => Vec::new(),
        TTIRPayload::Tuple(parts) => parts.clone(),
        TTIRPayload::Named(fields) => fields.iter().map(|held| held.ty).collect(),
    }
}

// ---- The other two bytes ---------------------------------------------------

// What the bytes mean, for a map that has to order and hash them.
fn kind_of(ttir: &TTIRProgram, ty: TyId) -> Kind {
    match ttir.types.get(ty) {
        Some(Ty::Prim(p)) => match p {
            TIRPrim::I8 | TIRPrim::I16 | TIRPrim::I32 | TIRPrim::I64 | TIRPrim::I128 => {
                Kind::Signed
            }
            // A boolean is a nought or a one and a `char` is a scalar value.
            // Both order and hash as the numbers they are.
            TIRPrim::U8
            | TIRPrim::U16
            | TIRPrim::U32
            | TIRPrim::U64
            | TIRPrim::U128
            | TIRPrim::Bool
            | TIRPrim::Char => Kind::Unsigned,
            TIRPrim::F32 | TIRPrim::F64 => Kind::Float,
            TIRPrim::Str => Kind::Str,
            TIRPrim::Null | TIRPrim::Never => Kind::Opaque,
        },
        Some(Ty::Ref { .. }) | Some(Ty::Ptr(_)) | Some(Ty::GC(_)) => Kind::Pointer,
        // Everything else is its bytes. That is a decision and the runtime's
        // header argues about it: it says two structures are one key when they
        // are the same bytes, and the language has no equality yet to mean
        // anything else by it.
        _ => Kind::Opaque,
    }
}

// Whether a register holding one of these holds its address rather than its
// value. The same question `Lowerer::indirect` asks and it has to give the
// same answer -- the runtime reads an argument the way the caller wrote it.
fn indirect(layouts: &mut Layouts<'_>, machine: Machine, ty: TyId) -> bool {
    match layouts.of(ty) {
        Some(held) => match held.shape {
            Shape::Scalar => held.bytes > machine.word,
            Shape::Empty => false,
            Shape::Fat | Shape::Fields(_) | Shape::Tagged { .. } | Shape::Elements { .. } => true,
        },
        None => false,
    }
}

fn up(n: usize, to: usize) -> usize {
    if to == 0 { n } else { n.div_ceil(to) * to }
}

#[cfg(test)]
mod tests;
