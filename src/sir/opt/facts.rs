// The questions every rewrite in this pass asks before it makes one.
//
// Six of them, and they are here together rather than beside the rewrite that
// happens to ask first because the answers have to agree. `sweep` may take an
// instruction out when it has no effects; `hoist` may move one onto a path it
// was not on when it has no effects; `wide` may fold four into one when they
// have no effects. Three rewrites, one question, and if they answered it
// three times they would answer it three ways -- and the one that was wrong
// would be wrong quietly, in a program that still compiles.
//
// So `effects` is written once. So is `known`, which is the different question
// of whether two instructions with the same operands make the same value, and
// `shareable`, which is the third: whether naming one value twice is naming
// one *thing* twice, or two things to release.
//
// The rest is reading: what made a value, what a value is a literal of, and
// the two halves of putting one value where another was.

use std::collections::HashMap;

use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRFnUses, TIRLit, TIRPrim};
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRProgram, Ty, TyId};


// What made each value, by the value's id. SSA is what makes this a table
// rather than a walk, and every rewrite below is written against it: "what
// does this operand hold" is `made[operand]`, and there is no second answer.
//
// A phi is not in it. What a phi made depends on the edge, which is the one
// question this table cannot be asked -- `operands` below is what covers both.
pub(super) fn made(body: &SIRBody) -> Vec<Option<SIRInstKind>> {
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

// What whatever made each value reads, phis included. `sweep` walks this
// backwards from the values that have to be worked out to the ones that
// therefore do.
pub(super) fn operands(body: &SIRBody) -> Vec<Vec<SIRValueId>> {
    let mut out = vec![Vec::new(); body.values.len()];
    for block in &body.blocks {
        for phi in &block.phis {
            if phi.def < out.len() {
                out[phi.def] = phi.edges.iter().map(|(_, value)| *value).collect();
            }
        }
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = SIRBody::uses(&inst.kind);
                }
            }
        }
    }
    out
}

pub(super) fn lit_of(made: &[Option<SIRInstKind>], value: SIRValueId) -> Option<&TIRLit> {
    match made.get(value)? {
        Some(SIRInstKind::Literal(held)) => Some(held),
        _ => None,
    }
}

pub(super) fn prim(ttir: &TTIRProgram, ty: TyId) -> Option<TIRPrim> {
    match ttir.types.get(ty)? {
        Ty::Prim(p) => Some(*p),
        _ => None,
    }
}

// Whether two types say the same thing, which is not the same as being the
// same entry.
//
// A `TyId` is not a name for a type: `sema` interns as it infers, so a program
// with three `i32`s written in it can leave three entries that all read
// `Prim(I32)`. Everything here that compares two types wants them one where
// they say the same thing -- an instruction repeated is repeated whichever
// `i32` the checker happened to be holding -- so the comparison is over what
// the entry says. The id is tried first because it usually settles it.
pub(super) fn alike(ttir: &TTIRProgram, a: TyId, b: TyId) -> bool {
    a == b || (ttir.types.get(a).is_some() && ttir.types.get(a) == ttir.types.get(b))
}

pub(super) fn integer(p: TIRPrim) -> bool {
    use TIRPrim::*;
    matches!(p, I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128)
}

// Whether the value has to stay even where nothing reads it.
//
// Three kinds of reason. A call or a store or a release is what the program is
// *for*, and dropping one drops what it did. An index may be past the end, and
// whether that is a trap is not settled anywhere yet (docs/prose.txt says
// nothing about it), so taking one out would be this pass answering a question
// that is not its own. And a division whose divisor is not a literal that is
// plainly not zero is the same: the trap, if there is one, is the thing being
// removed.
pub(super) fn effects(
    values: &[SIRValue],
    ttir: &TTIRProgram,
    made: &[Option<SIRInstKind>],
    kind: &SIRInstKind,
) -> bool {
    match kind {
        SIRInstKind::Call { .. }
        | SIRInstKind::Method { .. }
        | SIRInstKind::Store { .. }
        | SIRInstKind::Drop(_)
        | SIRInstKind::DropSlot(_)
        | SIRInstKind::VecStore { .. } => true,
        SIRInstKind::Index { base, index } | SIRInstKind::IndexAddr { base, index } => {
            !within(values, ttir, made, *base, *index)
        }
        SIRInstKind::Binary { op: TIRBinOp::Div | TIRBinOp::Rem, rhs, .. } => {
            match lit_of(made, *rhs) {
                Some(TIRLit::Int(n)) => *n == 0,
                // A float division by zero is an infinity and not a trap, so
                // there is nothing being kept for.
                Some(TIRLit::Float(_)) => false,
                _ => true,
            }
        }
        _ => false,
    }
}

// Whether the element being asked for is one the thing being indexed certainly
// has. A number for an index and a length in the type is the whole of what can
// be answered here, and it is enough for the shape that matters: a name of this
// frame, declared `T[n]`, reached at a place the unrolling worked out.
//
// Everything else is left as something that might be past the end -- which is
// not the same as saying it traps, only that nothing here knows it does not,
// and moving or dropping it would be answering a question §5 has not.
fn within(
    values: &[SIRValue],
    ttir: &TTIRProgram,
    made: &[Option<SIRInstKind>],
    base: SIRValueId,
    index: SIRValueId,
) -> bool {
    let Some(TIRLit::Int(n)) = lit_of(made, index) else { return false };
    let Some(held) = values.get(base) else { return false };
    let Some(Ty::Array { len, .. }) = ttir.types.get(held.ty) else { return false };
    *n >= 0 && (*n as u128) < *len as u128
}

// Whether two of them with the same operands make the same value.
//
// Not the same question as `effects`. A load has no effects and may still find
// something different the second time, because a store between them is exactly
// the effect the load has not got. A division may trap and is still the same
// answer twice: if the first one trapped there is no second one.
pub(super) fn known(ttir: &TTIRProgram, kind: &SIRInstKind) -> bool {
    // A global is the exception, and it is the same exception a load is. `Item`
    // reads what stands under a name: for a fn that is a value the linker
    // settles and for a `const` it is a constant, but a global is a *place*,
    // and two reads of one with a store between them are two answers. It sat in
    // this list from the beginning and nothing caught it, because until there
    // was a segment to put a global in no program with one ever linked -- so
    // the one pass that would have shown it up could not be run.
    if let SIRInstKind::Item(item) = kind {
        if matches!(
            ttir.items.get(*item).map(|held| &held.kind),
            Some(TTIRItemKind::Global { .. })
        ) {
            return false;
        }
    }
    matches!(
        kind,
        SIRInstKind::Literal(_)
            | SIRInstKind::Item(_)
            | SIRInstKind::SelfValue
            | SIRInstKind::Unary { .. }
            | SIRInstKind::Binary { .. }
            | SIRInstKind::Cast(_)
            | SIRInstKind::Discriminant(_)
            | SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::FieldAddr { .. }
            | SIRInstKind::TupleAddr { .. }
            // Two of these make the one value whether or not either traps: if
            // the first one did, there is no second one to have shared with.
            // Whether a dead one may *go* is `effects`, which is a different
            // question and answered differently.
            | SIRInstKind::Index { .. }
            | SIRInstKind::IndexAddr { .. }
    )
}

// And whether naming one value twice is naming one *thing* twice. It is not,
// wherever the value is something to release: two instructions that each made
// one become one instruction and two releases of it. So sharing is held to the
// types nobody releases, which is the part of `sema::borrows`' answer a `TyId`
// can give on its own -- see `Copies::drops`, which this agrees with and does
// not call, having neither the table nor the body's generics to hand.
pub(super) fn shareable(ttir: &TTIRProgram, ty: TyId) -> bool {
    match ttir.types.get(ty) {
        Some(Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Run(_)) => true,
        Some(Ty::Fn { uses, .. }) => *uses != TIRFnUses::Takes,
        _ => false,
    }
}

// ---- Putting one value where another was ----------------------------------

// What a value came to, following the chain as far as it goes: a value
// replaced by one that is itself replaced later in the same round. Bounded by
// the length of the map, which is what makes a cycle stop rather than spin.
pub(super) fn settle(subst: &HashMap<SIRValueId, SIRValueId>, mut value: SIRValueId) -> SIRValueId {
    for _ in 0..=subst.len() {
        match subst.get(&value) {
            Some(&next) if next != value => value = next,
            _ => return value,
        }
    }
    value
}

// Every operand of the body, rewritten at once. Every rewrite that takes an
// instruction out ends here: what it made is read somewhere, and what it made
// is now something else's.
pub(super) fn replace(body: &mut SIRBody, subst: &HashMap<SIRValueId, SIRValueId>) {
    if subst.is_empty() {
        return;
    }
    for block in &mut body.blocks {
        for phi in &mut block.phis {
            for (_, value) in &mut phi.edges {
                *value = settle(subst, *value);
            }
        }
        for inst in &mut block.insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(subst, *value);
            }
        }
        match &mut block.term {
            SIRTerm::Branch { cond, .. } => *cond = settle(subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(subst, *value),
            _ => {}
        }
    }
}
