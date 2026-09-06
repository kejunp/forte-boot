// An instruction inside a loop whose operands all come from outside it works
// out the same value every turn, so it belongs before the loop rather than in
// it. That is the whole of loop-invariant code motion, and the two words that
// carry it are "all" and "outside" -- which is why it is a fixpoint: the first
// instruction lifted makes its own value one that comes from outside, and the
// instruction that read it becomes liftable in the same walk.
//
// Three things hold it back, and each is a rule about soundness rather than
// about whether the move is worth making.
//
// It runs on a path the loop may not. A loop that turns nought times still
// reaches its preheader, so what is lifted there runs where it would not have
// -- which is why only instructions with nothing to do and nothing to trap on
// may go. `effects` is the same answer `sweep` is held to, and a division that
// might be by zero fails both for the same reason.
//
// It runs once where it ran every turn. A value with something to release is a
// value released every turn by the release the loop already holds, and lifting
// what made it would leave one thing released many times. So the type is held
// to `shareable`, exactly as `share` is, and for exactly that reason.
//
// And it may not be the same value twice. A `Load` finds what is there, and
// what is there is what the last store put there -- so a load may be lifted
// only out of a loop that stores nothing, calls nothing, and releases nothing.
// Anything narrower would need to know which addresses the loop writes, which
// is an alias analysis, and there is not one.

use crate::sir::alias::{Alias, Base};
use crate::sir::dom::Dominators;
use crate::sir::loops::{preheader, Loop};
use crate::sir::sir_nodes::*;
use crate::tir::ttir_nodes::{TTIRProgram, TyId};

use super::facts::*;
use super::Stats;

pub(super) fn hoist(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    // The preheaders first, all of them, and then the loops found again: a
    // block made here belongs to whatever loop stands outside the one it was
    // made for, and a bitmap worked out before it existed does not say so.
    let mut changed = false;
    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        let before = body.blocks.len();
        preheader(body, &held);
        changed |= body.blocks.len() != before;
    }

    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        changed |= lift(body, ttir, &held, stats);
    }
    changed
}

fn lift(body: &mut SIRBody, ttir: &TTIRProgram, held: &Loop, stats: &mut Stats) -> bool {
    let Some(pre) = preheader(body, held) else { return false };
    if held.has(pre) {
        return false;
    }

    // What the loop writes, so that a load can be asked whether any of it
    // lands where it reads. Three kinds: the addresses stored to, the slots
    // released, and whether it calls out at all -- a call writes wherever it
    // can reach, which is everywhere but a name of this frame whose address
    // nothing kept.
    let alias = Alias::of(body);
    let held_made = made(body);
    let mut wrote: Vec<SIRValueId> = Vec::new();
    let mut released: Vec<SIRSlotId> = Vec::new();
    let mut calls = false;
    for &at in &held.blocks {
        for inst in &body.blocks[at].insts {
            match &inst.kind {
                SIRInstKind::Store { to, .. } => wrote.push(*to),
                SIRInstKind::DropSlot(slot) => released.push(*slot),
                SIRInstKind::Call { .. } | SIRInstKind::Method { .. } | SIRInstKind::Drop(_) => {
                    calls = true
                }
                // A vector store reaches further than the address it names, so
                // it is treated as reaching everywhere rather than reasoned
                // about.
                SIRInstKind::VecStore { .. } => calls = true,
                _ => {}
            }
        }
    }
    let quiet = |from: SIRValueId| {
        if wrote.iter().any(|&to| alias.may(to, from)) {
            return false;
        }
        if released.iter().any(|&slot| alias.place(from).map(|p| p.base) == Some(Base::Slot(slot)))
        {
            return false;
        }
        !calls || alias.own(from)
    };

    // What the loop makes, which is what "comes from outside" is the negation
    // of. Cleared as an instruction is lifted, so that what read it is lifted
    // too on the same walk down.
    let mut within = vec![false; body.values.len()];
    for &at in &held.blocks {
        for phi in &body.blocks[at].phis {
            within[phi.def] = true;
        }
        for inst in &body.blocks[at].insts {
            if let Some(def) = inst.def {
                within[def] = true;
            }
        }
    }

    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    let mut moved: Vec<SIRInst> = Vec::new();
    for &at in &held.blocks {
        for index in 0..body.blocks[at].insts.len() {
            let inst = &body.blocks[at].insts[index];
            let Some(def) = inst.def else { continue };
            if !liftable(ttir, &body.values, &held_made, &inst.kind, body.values[def].ty) {
                continue;
            }
            // A read has to be asked whether what it reads stays put for the
            // length of the loop. A `Load` names the address it reads; an
            // `Index` *is* the place it reads (`sir::alias`), so it is asked
            // about itself.
            let reads = match inst.kind {
                SIRInstKind::Load { from } => Some(from),
                SIRInstKind::Index { .. } => Some(def),
                _ => None,
            };
            if let Some(from) = reads {
                if !quiet(from) {
                    continue;
                }
            }
            if SIRBody::uses(&inst.kind).iter().any(|&value| within[value]) {
                continue;
            }
            within[def] = false;
            moved.push(inst.clone());
            gone[at][index] = true;
        }
    }
    if moved.is_empty() {
        return false;
    }

    for &at in &held.blocks {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    // In the order they were met, which is the order they were written in: a
    // lifted instruction whose operand was lifted with it stands below it,
    // because the walk down the loop meets a value before it is read.
    stats.hoisted += moved.len();
    body.blocks[pre].insts.append(&mut moved);
    true
}

fn liftable(
    ttir: &TTIRProgram,
    values: &[SIRValue],
    made: &[Option<SIRInstKind>],
    kind: &SIRInstKind,
    ty: TyId,
) -> bool {
    let place = matches!(
        kind,
        SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::FieldAddr { .. }
            | SIRInstKind::TupleAddr { .. }
            | SIRInstKind::IndexAddr { .. }
    );
    if !place && !shareable(ttir, ty) {
        return false;
    }
    // Nothing that may trap, which is the same list `sweep` is held to and for
    // the mirror of the same reason: a loop that turns nought times still
    // reaches the block this is going into, so a division by something that
    // might be zero, or an index that might be past the end, would be a trap
    // moved onto a path it was not on. `known` is not that question -- `share`
    // puts nothing anywhere new -- which is why both are asked here.
    if effects(values, ttir, made, kind) {
        return false;
    }
    // A read is liftable as far as this is concerned; whether what it reads
    // stays put for the length of the loop is `quiet`'s to say, and the two
    // reads are the only ones of these that have to ask.
    //
    // An `Index` is one of them and is no longer in `known`, where it was
    // being called a value worked out from its operands -- so it came through
    // here without `quiet` ever being asked, and a read the loop wrote could
    // be lifted out above it.
    known(ttir, kind) || matches!(kind, SIRInstKind::Load { .. } | SIRInstKind::Index { .. })
}
