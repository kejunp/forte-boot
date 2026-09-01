// The second shape: the graph written out as one run of instructions.
//
//     MIR (graph) -> linear -> MIR (linear) -> regalloc -> text
//                     ^^^^^^
//
// Two things stop being true here, and both of them are what the graph was for.
//
// **An edge becomes an order.** A block has to come somewhere, and once it does
// its terminator is a jump to a label rather than an edge to a block. The order
// chosen is reverse postorder from the entry, which is the order a reader
// follows: a block comes after everything that must have run to reach it, and
// the body of a loop comes after its head. Nothing here tries to make jumps
// fall through -- that is a saving to be measured, and there is nothing to
// measure with.
//
// **A phi becomes moves.** A phi says which value came along which edge, and an
// edge is exactly what has just stopped existing. So each one is written as a
// move at the end of each block it names: the value is put into the phi's
// register on the way out, and by the time the block with the phi is reached
// the register holds what that path put there.
//
// Two things make that harder than it sounds, and both are handled below.
//
// A block's phis all read the values as they stood at the *end* of the
// predecessor -- all at once, not one after another. Writing them as moves in
// sequence breaks that when one phi's register is another phi's operand:
// `a = b; b = a` written in order leaves both holding what `b` held. Where that
// can happen every value is copied to a fresh register first and then into
// place, which is always right and costs a move that is usually not needed.
//
// And a move at the end of a block runs whenever that block runs -- which is
// wrong if the block has two ways out and only one of them leads here. That is
// a critical edge, and the answer is the usual one: put a block on it, with
// nothing in it but the moves and a jump. It is the only thing in this pass
// that adds a block, and every block it adds has exactly one way in and one way
// out.

use std::collections::HashMap;

use super::mir_nodes::*;

// A body with its blocks in an order and its phis gone.
#[derive(Debug, Clone, PartialEq)]
pub struct Linear {
    pub symbol: String,
    pub regs:   Vec<MIRReg>,
    pub frame:  Vec<MIRSlot>,
    pub params: Vec<MIRRegId>,
    pub lines:  Vec<Line>,
}

// One line of it. A label is where a jump lands and takes no time; the other
// two are what runs.
#[derive(Debug, Clone, PartialEq)]
pub enum Line {
    Label(MIRBlockId),
    Inst(MIRInst),
    Term(MIRTerm),
}

pub fn all(p: &MIRProgram) -> Vec<Linear> {
    p.bodies.iter().map(linearise).collect()
}

pub fn linearise(body: &MIRBody) -> Linear {
    let mut held = body.clone();
    split(&mut held);
    unphi(&mut held);

    let mut lines = Vec::new();
    for at in order(&held) {
        lines.push(Line::Label(at));
        for inst in &held.blocks[at].insts {
            lines.push(Line::Inst(inst.clone()));
        }
        lines.push(Line::Term(held.blocks[at].term.clone()));
    }

    Linear {
        symbol: held.symbol,
        regs:   held.regs,
        frame:  held.frame,
        params: held.params,
        lines,
    }
}

// ---- Putting a block on the edges that need one ----------------------------

// A block with two ways out, going to a block with phis, has to have somewhere
// of its own to put the moves for this edge. Without it the moves would run
// down the other way out as well, writing values that path never agreed to.
fn split(body: &mut MIRBody) {
    let live = body.live();
    let preds = body.preds();
    let mut edges: Vec<(MIRBlockId, MIRBlockId)> = Vec::new();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] || block.phis.is_empty() {
            continue;
        }
        for &from in &preds[at] {
            if body.blocks[from].term.targets().len() > 1 {
                edges.push((from, at));
            }
        }
    }

    for (from, to) in edges {
        let new = body.blocks.len();
        let (line, col) = (body.blocks[from].line, body.blocks[from].col);
        body.blocks.push(MIRBlock {
            phis:  Vec::new(),
            insts: Vec::new(),
            term:  MIRTerm::Goto(to),
            line,
            col,
        });
        for target in body.blocks[from].term.targets_mut() {
            if *target == to {
                *target = new;
            }
        }
        // What used to arrive from `from` now arrives from the block on the
        // edge, which is where its moves will go.
        for phi in &mut body.blocks[to].phis {
            for (edge, _) in &mut phi.edges {
                if *edge == from {
                    *edge = new;
                }
            }
        }
    }
}

// ---- Phis into moves -------------------------------------------------------

fn unphi(body: &mut MIRBody) {
    let live = body.live();

    // What each block has to put where on the way out, gathered before anything
    // is written: a block may be the way in to more than one block with phis.
    let mut out: HashMap<MIRBlockId, Vec<(MIRRegId, MIRRegId)>> = HashMap::new();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for phi in &block.phis {
            for &(from, src) in &phi.edges {
                out.entry(from).or_default().push((phi.def, src));
            }
        }
    }

    for (at, pairs) in out {
        if at >= body.blocks.len() {
            continue;
        }
        let (line, col) = (body.blocks[at].line, body.blocks[at].col);

        // All at once, not one after another. Where nothing being written is
        // also being read, in order is the same thing and is a move each.
        let reads: Vec<MIRRegId> = pairs.iter().map(|&(_, src)| src).collect();
        let clashes = pairs.iter().any(|&(def, _)| reads.contains(&def));

        if !clashes {
            for (def, src) in pairs {
                body.blocks[at].insts.push(MIRInst {
                    def:  Some(def),
                    kind: MIRInstKind::Move(src),
                    line,
                    col,
                });
            }
            continue;
        }

        // Everything read is put somewhere fresh first, so that what is written
        // afterwards cannot disturb what is still to be read.
        let mut held = Vec::with_capacity(pairs.len());
        for &(_, src) in &pairs {
            let one = body.regs[src];
            body.regs.push(one);
            let temp = body.regs.len() - 1;
            body.blocks[at].insts.push(MIRInst {
                def:  Some(temp),
                kind: MIRInstKind::Move(src),
                line,
                col,
            });
            held.push(temp);
        }
        for (&(def, _), temp) in pairs.iter().zip(held) {
            body.blocks[at].insts.push(MIRInst {
                def:  Some(def),
                kind: MIRInstKind::Move(temp),
                line,
                col,
            });
        }
    }

    for block in &mut body.blocks {
        block.phis.clear();
    }
}

// ---- What order to write them in -------------------------------------------

// Reverse postorder from the entry. A block comes after everything that had to
// run to reach it, which is the order a reader follows and the order a walk
// over live ranges wants -- a value made before a use is a value made earlier
// in the list, wherever the graph allowed it.
//
// Only the blocks the entry reaches. Nothing here shrinks a block arena, so an
// arena holds blocks a rewrite emptied, and writing those out would be writing
// out code nothing can jump to.
fn order(body: &MIRBody) -> Vec<MIRBlockId> {
    let mut seen = vec![false; body.blocks.len()];
    let mut done = Vec::new();
    if body.entry < body.blocks.len() {
        // Iterative, because a body deep enough to matter is deep enough to
        // run a recursive walk out of stack.
        let mut stack = vec![(body.entry, 0usize)];
        seen[body.entry] = true;
        while let Some((at, next)) = stack.pop() {
            let targets = body.blocks[at].term.targets();
            if next < targets.len() {
                stack.push((at, next + 1));
                let to = targets[next];
                if to < seen.len() && !seen[to] {
                    seen[to] = true;
                    stack.push((to, 0));
                }
            } else {
                done.push(at);
            }
        }
    }
    done.reverse();
    done
}

#[cfg(test)]
mod tests;
