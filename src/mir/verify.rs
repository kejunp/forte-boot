// The rules a MIR body is held to, checked rather than assumed.
//
// The SIR has a file with this name and this shape, and its header says why:
// the properties every later pass leans on are the ones a pass can break
// silently, leaving a graph that still walks and an answer that is wrong
// somewhere else. All of that is true here and one thing more is -- lowering to
// a machine is where a number stops being checked by a type. A field read four
// bytes into a structure whose second field begins at eight is not a shape
// anything downstream can notice.
//
// So the rules are the SSA ones again, because the graph is still SSA:
//
//   - a register is made in one place;
//   - a register is read only where the place that made it stands between the
//     read and the entry;
//   - a phi names every way into its block, once each.
//
// and the ones that are new here, because the arenas are new:
//
//   - every register read is in the register arena;
//   - every block named is in the block arena;
//   - every slot named is in the frame.
//
// The dominator sets are worked out in this file rather than taken from
// `sir::dom`, which answers the same question about a different body type.
// Making that shared would mean a trait over both, and there is not a trait in
// this compiler; if a second pass here ever wants dominance, this moves out
// into `mir/dom.rs` and stops being a private thing a checker does.

use super::mir_nodes::*;

// Everything wrong with the body, in the words a failing test should print.
// Empty is the answer a correct body gives.
pub fn verify(body: &MIRBody) -> Vec<String> {
    let mut wrong = Vec::new();
    let live = body.live();
    let preds = body.preds();

    if body.entry >= body.blocks.len() {
        wrong.push(format!("the entry is block {}, which is not in the arena", body.entry));
        return wrong;
    }

    // ---- Made once, and made somewhere -------------------------------------

    // Where each register is made. A parameter is made by the caller, which is
    // the entry as far as anything here can see.
    let mut made: Vec<Option<MIRBlockId>> = vec![None; body.regs.len()];
    let once = |reg: MIRRegId,
                at: MIRBlockId,
                made: &mut Vec<Option<MIRBlockId>>,
                wrong: &mut Vec<String>| {
        if reg >= made.len() {
            wrong.push(format!("register %{} is not in the arena", reg));
            return;
        }
        if made[reg].is_some() {
            wrong.push(format!("register %{} is made more than once", reg));
        }
        made[reg] = Some(at);
    };

    for &param in &body.params {
        once(param, body.entry, &mut made, &mut wrong);
    }
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for phi in &block.phis {
            once(phi.def, at, &mut made, &mut wrong);
        }
        for inst in &block.insts {
            if let Some(def) = inst.def {
                once(def, at, &mut made, &mut wrong);
            }
        }
    }

    // ---- Every name reaches something --------------------------------------

    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for inst in &block.insts {
            for read in uses(&inst.kind) {
                if read >= body.regs.len() {
                    wrong.push(format!("block {} reads %{}, which is not in the arena", at, read));
                }
            }
            if let MIRInstKind::Frame(slot) = inst.kind {
                if slot >= body.frame.len() {
                    wrong.push(format!("block {} names slot ${}, which is not in the frame", at, slot));
                }
            }
        }
        for read in block.term.uses() {
            if read >= body.regs.len() {
                wrong.push(format!("block {} ends reading %{}, which is not in the arena", at, read));
            }
        }
        for to in block.term.targets() {
            if to >= body.blocks.len() {
                wrong.push(format!("block {} goes to block {}, which is not in the arena", at, to));
            }
        }
    }

    // ---- A phi says where each of its operands came from -------------------

    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for phi in &block.phis {
            let mut named: Vec<MIRBlockId> = phi.edges.iter().map(|(from, _)| *from).collect();
            named.sort_unstable();
            let mut want = preds[at].clone();
            want.sort_unstable();
            if named != want {
                wrong.push(format!(
                    "the phi for %{} in block {} names {:?}, and the ways in are {:?}",
                    phi.def, at, named, want
                ));
            }
        }
    }

    // ---- And a read is only where what it reads has already been made ------

    let doms = dominators(body, &preds, &live);
    let at_of = |reg: MIRRegId, made: &Vec<Option<MIRBlockId>>| -> Option<MIRBlockId> {
        made.get(reg).copied().flatten()
    };

    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        // A phi's operand arrives along the way in, so what has to stand before
        // it is the *predecessor* it came from. A register made in the block
        // the phi is in would not be there yet, and one made in a sibling of
        // the predecessor never arrives at all.
        for phi in &block.phis {
            for (from, reg) in &phi.edges {
                let Some(made_at) = at_of(*reg, &made) else {
                    wrong.push(format!(
                        "the phi for %{} in block {} reads %{}, which nothing makes",
                        phi.def, at, reg
                    ));
                    continue;
                };
                if *from < doms.len() && !doms[*from][made_at] {
                    wrong.push(format!(
                        "the phi for %{} in block {} reads %{} along block {}, which does not reach it",
                        phi.def, at, reg, from
                    ));
                }
            }
        }

        let reads = block
            .insts
            .iter()
            .flat_map(|inst| uses(&inst.kind))
            .chain(block.term.uses());
        for reg in reads {
            let Some(made_at) = at_of(reg, &made) else {
                if reg < body.regs.len() {
                    wrong.push(format!("block {} reads %{}, which nothing makes", at, reg));
                }
                continue;
            };
            if !doms[at][made_at] {
                wrong.push(format!(
                    "block {} reads %{}, which is made in block {} and does not reach it",
                    at, reg, made_at
                ));
            }
        }
    }

    wrong
}

// The second rule, within one block: what a register reads has to have been
// made further up the same block, where it was made in that block at all.
// Dominance says nothing about this -- a block dominates itself -- so it is a
// separate walk, exactly as it is in the SIR.
pub fn verify_order(body: &MIRBody) -> Vec<String> {
    let mut wrong = Vec::new();
    let live = body.live();

    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        // The phis are read before the block begins, so every one of them is
        // already made by the time the first instruction runs.
        let mut standing: Vec<MIRRegId> = block.phis.iter().map(|phi| phi.def).collect();
        if at == body.entry {
            standing.extend(body.params.iter().copied());
        }
        let made_here: Vec<MIRRegId> =
            block.insts.iter().filter_map(|inst| inst.def).collect();

        for inst in &block.insts {
            for reg in uses(&inst.kind) {
                if made_here.contains(&reg) && !standing.contains(&reg) {
                    wrong.push(format!(
                        "block {} reads %{} above the instruction that makes it",
                        at, reg
                    ));
                }
            }
            if let Some(def) = inst.def {
                standing.push(def);
            }
        }
    }

    wrong
}

// Which blocks stand between each block and the entry, as a row of flags per
// block. `doms[b][a]` is "every way to `b` goes through `a`".
//
// The ordinary iterative answer: everything dominates everything to begin with,
// the entry dominates only itself, and each round narrows a block to itself
// plus what all its ways in agree on. It settles because a set only ever
// shrinks.
fn dominators(body: &MIRBody, preds: &[Vec<MIRBlockId>], live: &[bool]) -> Vec<Vec<bool>> {
    let n = body.blocks.len();
    let mut doms = vec![vec![true; n]; n];
    for at in 0..n {
        if !live[at] {
            // A block nothing reaches dominates nothing and is dominated by
            // nothing. Leaving it full would make it stand in every
            // intersection it appears in.
            doms[at] = vec![false; n];
        }
    }
    if body.entry < n {
        doms[body.entry] = vec![false; n];
        doms[body.entry][body.entry] = true;
    }

    let mut again = true;
    while again {
        again = false;
        for at in 0..n {
            if !live[at] || at == body.entry {
                continue;
            }
            let mut held = vec![true; n];
            let mut any = false;
            for &from in &preds[at] {
                if !live[from] {
                    continue;
                }
                any = true;
                for b in 0..n {
                    held[b] &= doms[from][b];
                }
            }
            if !any {
                held = vec![false; n];
            }
            held[at] = true;
            if held != doms[at] {
                doms[at] = held;
                again = true;
            }
        }
    }
    doms
}

#[cfg(test)]
mod tests;
