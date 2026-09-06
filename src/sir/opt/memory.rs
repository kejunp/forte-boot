// What is at an address, as far as it can be followed.
//
// Two rewrites, and they are the two directions of one question. A load below
// a store to the same place is the value the store wrote, so it need not go
// and look. A store written over before anything reads it is a store nobody
// could have seen the result of, so it need not happen.
//
// Neither could be written before `sir::alias` was. What is *at* an address is
// not among a load's operands -- the address is -- so `share` cannot help: the
// question is which writes stand between the two, and only an alias analysis
// answers that. It has to be `must` for the pair being matched and `may` for
// everything in between, and having those two the wrong way round is a load
// answered with the wrong value or a store dropped that somebody wanted.
//
// A block at a time, both of them. Following either across a join means
// carrying what is known along every edge and joining it where they meet,
// which is a memory SSA and a larger thing than this.

use std::collections::HashMap;

use crate::sir::alias::{Alias, Base};
use crate::sir::sir_nodes::*;
use crate::tir::ttir_nodes::TTIRProgram;

use super::facts::*;
use super::Stats;

// A load below a store to the same address finds what the store wrote, so it
// need not go and look: the value is already in hand. And a second load of an
// address nothing has written since finds what the first one found.
//
// This is the rewrite `share` cannot make. Two instructions with the same
// operands make the same value, which is why `share` may put one where two
// were -- but a load's operands are an address, and what is *at* an address is
// not among them. What is at it is whatever the last write left, so the
// question is which writes stand between the two, and that is what `alias`
// answers.
//
// Within a block and no further. Following the answer across a join means
// carrying what is known at every edge and joining it where they meet, which
// is a memory SSA and is a larger thing than this; a block at a time catches
// the shape that matters -- a name written and read on the next line -- and
// `hoist` is what carries a load out of a loop.
//
// Three things end what is known. A store to an address that may be the same
// one replaces it. A call, a method or a release may write anywhere it can
// reach, so everything goes but what is rooted in a name of this frame whose
// address nothing kept. And a value with something to release is never
// forwarded at all: the load would be the value the store wrote rather than a
// copy of it, and both would be released.
pub(super) fn forward(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let alias = Alias::of(body);
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        // What is at an address, in the order it was learnt.
        let mut known: Vec<(SIRValueId, SIRValueId)> = Vec::new();
        for index in 0..body.blocks[at].insts.len() {
            match body.blocks[at].insts[index].kind {
                SIRInstKind::Store { to, value } => {
                    known.retain(|(addr, _)| !alias.may(*addr, to));
                    known.push((to, settle(&subst, value)));
                }
                // A read through an address, and a read that *is* one: an
                // `Index` does not name the address it reads, so it stands for
                // both here -- `sir::alias` gives it the place an `IndexAddr`
                // of the same operands would name, which is what lets it be
                // matched against a store and against another read of it.
                //
                // That is also where the sharing of two of them belongs. It
                // used to be `share`'s, which asks whether two instructions
                // have the same operands and nothing about what stands between
                // them -- so `p[0]` read, written, and read again came out as
                // one read, and the second answered with what the first found.
                SIRInstKind::Load { from } | SIRInstKind::Index { base: from, .. } => {
                    let Some(def) = body.blocks[at].insts[index].def else { continue };
                    if !shareable(ttir, body.values[def].ty) {
                        continue;
                    }
                    // A `Load` reads what its operand addresses; an `Index`
                    // reads what it is itself the place of.
                    let from = match body.blocks[at].insts[index].kind {
                        SIRInstKind::Index { .. } => def,
                        _ => from,
                    };
                    let found = known
                        .iter()
                        .rev()
                        .find(|(addr, _)| alias.must(*addr, from))
                        .map(|(_, held)| *held);
                    match found {
                        // The types have to agree as well as the addresses. A
                        // union read back as the other arm is one address and
                        // two values, and this pass is not the place to decide
                        // what that means.
                        Some(held) if alike(ttir, body.values[held].ty, body.values[def].ty) => {
                            subst.insert(def, held);
                            gone[at][index] = true;
                            stats.forwarded += 1;
                        }
                        _ => known.push((from, def)),
                    }
                }
                SIRInstKind::Call { .. }
                | SIRInstKind::Method { .. }
                | SIRInstKind::Drop(_)
                | SIRInstKind::DropSlot(_) => {
                    known.retain(|(addr, _)| alias.own(*addr));
                }
                // A run of places written at once, and only the first of them
                // named. See `overwritten`, where the same answer is given for
                // the same reason.
                SIRInstKind::VecStore { .. } => known.clear(),
                _ => {}
            }
        }
    }

    if subst.is_empty() {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    replace(body, &subst);
    true
}

// ---- Stores nothing will read ---------------------------------------------

// A store whose value is written over before anything reads it is a store that
// need not have happened. The mirror of `forward`, and it reads the block the
// other way round: from the bottom, holding the addresses that are certainly
// written again below, and dropping one as soon as something between might
// read it.
//
// It has to be `must` below and `may` between, and the two are not the same
// question turned round. A store is dead only if what overwrites it certainly
// lands on the same place; it is alive again if anything that might read it
// stands in the way. Getting either the wrong way about is a store dropped
// that somebody wanted.
//
// A block at a time, again, and for the same reason as `forward`: what a store
// is worth past the end of its block is a question about every path out of it.
// Stopping at the end of the block is what makes "nothing reads it" a fact
// about a straight line rather than a claim about the graph.
pub(super) fn overwritten(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let alias = Alias::of(body);
    let live = body.live();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    let mut changed = false;

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        // Addresses written again below without being read in between.
        let mut over: Vec<SIRValueId> = Vec::new();
        for index in (0..body.blocks[at].insts.len()).rev() {
            match body.blocks[at].insts[index].kind {
                SIRInstKind::Store { to, .. } => {
                    if over.iter().any(|&held| alias.must(held, to)) {
                        gone[at][index] = true;
                        stats.dead += 1;
                        changed = true;
                    } else {
                        over.push(to);
                    }
                }
                SIRInstKind::Load { from } => over.retain(|&held| !alias.may(held, from)),
                // And the read that names no address. Without it a store an
                // `Index` was reading was dropped as one nothing had seen:
                // `p[0] = 1`, `let v = p[0]`, `p[0] = 2` left `v` reading
                // whatever stood there before the first store ever ran.
                SIRInstKind::Index { .. } => {
                    if let Some(def) = body.blocks[at].insts[index].def {
                        over.retain(|&held| !alias.may(held, def));
                    }
                }
                // Naming a global reads it, and a `Load` is not how that is
                // written. `Item` is what stands where a declaration was named
                // as a value, and for a global what stands under the name is a
                // *place* -- so this is a read of it, exactly as the `Load`
                // above is a read of an address.
                //
                // It was not in this list, and what that cost was every store
                // to a global but the last: `n = n + 1` twice over kept the
                // second store, dropped the first, and left the second reading
                // the value the first was meant to have written. Nothing caught
                // it because no program with a global linked until there was a
                // segment to put one in.
                //
                // By base rather than through `may`, as `DropSlot` below is and
                // for the same reason: what is being read is named rather than
                // pointed at, so there is an item to compare and no address.
                SIRInstKind::Item(item) => over.retain(|&held| {
                    alias.place(held).map(|p| p.base) != Some(Base::Item(item))
                }),
                // Releasing what is in a name reads what is in it.
                SIRInstKind::DropSlot(slot) => over.retain(|&held| {
                    alias.place(held).map(|p| p.base) != Some(Base::Slot(slot))
                }),
                SIRInstKind::Drop(value) => {
                    over.retain(|&held| alias.own(held) && !alias.may(held, value))
                }
                // A call reads wherever it can reach, which is everywhere but
                // a name of this frame whose address nothing kept.
                SIRInstKind::Call { .. } | SIRInstKind::Method { .. } => {
                    over.retain(|&held| alias.own(held))
                }
                // A vector store writes a run of places and this knows the
                // address of the first of them only. Rather than reason about
                // how far it reaches, nothing is held across one -- which
                // costs nothing worth having: it is written by the last
                // rewrite in the round, after this one has already run.
                SIRInstKind::VecStore { .. } => over.clear(),
                _ => {}
            }
        }
    }

    if !changed {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    true
}
