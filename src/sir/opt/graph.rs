// The graph itself: edges that go one way, blocks that were one block, and
// everything nothing runs.
//
// These four are what keep the other rewrites honest about size. Folding turns
// a condition into a literal and leaves a branch with one edge; taking that
// edge leaves a block with one way in; joining that block to the one above it
// leaves an instruction beside the one it repeats, which is what `share` needs
// to see. Each of them is small and none of them is interesting on its own,
// which is rather the point -- the interesting rewrites make work for these,
// and these make work for the interesting ones.
//
// `repair` is the one thing here that other files call. A phi has one entry
// per way in, so a rewrite that takes a way in away has to say so, and there
// is one place that says it.


use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::TIRLit;
use crate::tir::ttir_nodes::TTIRProgram;

use super::facts::*;
use super::Stats;

// A branch on a literal goes one way, and a branch whose two edges go to one
// block was never a branch. Either way the block that stops being reached has
// to be told: a phi has one entry per way in, and a way in that has gone is an
// entry that has to go with it.
pub(super) fn branches(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let held = made(body);
    let mut changed = false;
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let SIRTerm::Branch { cond, then, els } = body.blocks[at].term else { continue };
        let to = match lit_of(&held, cond) {
            Some(TIRLit::Bool(true)) => then,
            Some(TIRLit::Bool(false)) => els,
            _ if then == els => then,
            _ => continue,
        };
        body.blocks[at].term = SIRTerm::Goto(to);
        stats.blocks += 1;
        changed = true;
    }
    if changed {
        repair(body);
    }
    changed
}

// Phis held to the ways in the block actually has. Only ever fewer: nothing in
// this pass gives a block a way in it had not got, and `merge` renames the one
// edge it moves rather than adding one.
pub(super) fn repair(body: &mut SIRBody) {
    let live = body.live();
    let preds = body.preds();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let ways: Vec<SIRBlockId> =
            preds[at].iter().copied().filter(|&p| live[p]).collect();
        for phi in &mut body.blocks[at].phis {
            let mut kept: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
            for &(from, value) in phi.edges.iter() {
                if ways.contains(&from) && !kept.iter().any(|(held, _)| *held == from) {
                    kept.push((from, value));
                }
            }
            phi.edges = kept;
        }
    }
}

// ---- Blocks folded into the block above them ------------------------------

// A block with one way in, and that way a `Goto`, is the tail of the block
// that goes there. Joining the two is what leaves an instruction next to the
// one it repeats, which is most of what `share` and `fold` need to see.
//
// Only where the block has no phis. A phi with one way in is a phi with one
// answer, which `phis` takes out a round earlier -- so this waits rather than
// working out what a phi means in a block that no longer begins anywhere.
pub(super) fn merge(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let mut changed = false;
    loop {
        let live = body.live();
        let preds = body.preds();
        let mut joined = None;
        for at in 0..body.blocks.len() {
            if !live[at] {
                continue;
            }
            let SIRTerm::Goto(to) = body.blocks[at].term else { continue };
            if to == at || to == body.entry || !body.blocks[to].phis.is_empty() {
                continue;
            }
            if preds[to].iter().filter(|&&p| live[p]).count() != 1 {
                continue;
            }
            joined = Some((at, to));
            break;
        }
        let Some((at, to)) = joined else { return changed };

        let mut moved = std::mem::take(&mut body.blocks[to].insts);
        let term = std::mem::replace(&mut body.blocks[to].term, SIRTerm::Unreachable);
        body.blocks[at].insts.append(&mut moved);
        // Whoever heard from the block that has gone hears from this one now.
        for next in term.targets() {
            for phi in &mut body.blocks[next].phis {
                for (from, _) in &mut phi.edges {
                    if *from == to {
                        *from = at;
                    }
                }
            }
        }
        body.blocks[at].term = term;
        stats.blocks += 1;
        changed = true;
    }
}

// ---- What nothing reads ---------------------------------------------------

// A value nothing reads and nothing needs run is a value that was never worth
// working out. Marked and then swept: an instruction is wanted if what it
// makes is wanted, and what it reads is wanted if it is -- so the walk starts
// at the instructions that have to run whatever else happens, and everything
// it does not reach goes.
//
// Blocks nothing reaches go the same way, and first: an instruction standing
// in one is not run either, and leaving it there would keep alive whatever it
// reads.
pub(super) fn sweep(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut changed = false;
    for at in 0..body.blocks.len() {
        let emptied = body.blocks[at].term == SIRTerm::Unreachable
            && body.blocks[at].insts.is_empty()
            && body.blocks[at].phis.is_empty();
        if live[at] || emptied {
            continue;
        }
        stats.dead += body.blocks[at].insts.len();
        stats.blocks += 1;
        body.blocks[at].phis.clear();
        body.blocks[at].insts.clear();
        body.blocks[at].term = SIRTerm::Unreachable;
        changed = true;
    }

    let held = made(body);
    let reads = operands(body);
    let mut wanted = vec![false; body.values.len()];
    let mut work: Vec<SIRValueId> = Vec::new();
    let want = |value: SIRValueId, wanted: &mut Vec<bool>, work: &mut Vec<SIRValueId>| {
        if value < wanted.len() && !wanted[value] {
            wanted[value] = true;
            work.push(value);
        }
    };

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for inst in &body.blocks[at].insts {
            if effects(&body.values, ttir, &held, &inst.kind) {
                for value in SIRBody::uses(&inst.kind) {
                    want(value, &mut wanted, &mut work);
                }
            }
        }
        match &body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => want(*cond, &mut wanted, &mut work),
            SIRTerm::Return(Some(value)) => want(*value, &mut wanted, &mut work),
            _ => {}
        }
    }
    while let Some(value) = work.pop() {
        for &read in &reads[value] {
            want(read, &mut wanted, &mut work);
        }
    }

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let before = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        body.blocks[at].phis.retain(|phi| wanted[phi.def]);
        // Worked out before the list is touched: what an instruction is for
        // is a question about the whole body, and the answer cannot be asked
        // for while the list it is about is being written to.
        let keep: Vec<bool> = body.blocks[at]
            .insts
            .iter()
            .map(|inst| match inst.def {
                Some(def) => wanted[def] || effects(&body.values, ttir, &held, &inst.kind),
                // An instruction that makes nothing is there for what it does,
                // and one that does nothing either is one nothing put there.
                None => effects(&body.values, ttir, &held, &inst.kind),
            })
            .collect();
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            keep[index - 1]
        });
        let after = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        if after != before {
            stats.dead += before - after;
            changed = true;
        }
    }
    changed
}
