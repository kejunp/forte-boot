// The loops a body holds, found in the graph rather than remembered from the
// source.
//
// `sir::lower` knew which blocks a `for` was made of -- it built them -- and
// said nothing, because by the time the SIR exists a loop is a shape and not a
// statement. A `while`, a `for` and a `match` arm that jumps backwards are the
// same thing here, and a pass that wanted only the ones spelled `for` would be
// asking about the source through the wrong window.
//
// What makes it a shape is dominance. An edge `b -> h` where `h` dominates `b`
// is a *back edge*: control has arrived somewhere it has already been, and it
// got there through `h` both times. The loop that edge closes is `h` together
// with every block that reaches `b` without going back through `h` -- which is
// the natural loop, and is the standard construction because it is the only
// set with one way in. One way in is what every later question needs: where to
// put something lifted out of the loop, and which values arrive from before it
// rather than from the turn before.
//
// Two headers can be the same block -- a loop with a `continue` in it closes
// two back edges -- and that is one loop and not two, so the sets are merged
// by header as they are found.
//
// What is *not* here is anything irreducible: a loop entered at two different
// blocks has no header, and this finds none. A language with no `goto` cannot
// write one, so the case is not handled rather than being handled wrongly.

use std::collections::HashMap;

use super::dom::Dominators;
use super::sir_nodes::*;

pub struct Loop {
    pub head:    SIRBlockId,
    // By block id, whether the block is one of the loop's. A bitmap and not a
    // set because every question asked of it is "is this one", asked once per
    // operand of every instruction in the body.
    pub holds:   Vec<bool>,
    // The same, listed, header first and the rest in reverse postorder -- so a
    // walk down it meets a value's definition before any use of it, which is
    // what lets one pass lift a chain of instructions in one go.
    pub blocks:  Vec<SIRBlockId>,
    // The ways round: the blocks inside that go back to the head.
    pub back:    Vec<SIRBlockId>,
    // And the ways in: the blocks outside that go to it. Structured source
    // leaves exactly one, `while` and `for` alike.
    pub entries: Vec<SIRBlockId>,
}

impl Loop {
    pub fn all(body: &SIRBody, doms: &Dominators) -> Vec<Loop> {
        let live = body.live();
        let preds = body.preds();

        // One bitmap per header, grown as the back edges into it are found.
        let mut found: HashMap<SIRBlockId, Vec<bool>> = HashMap::new();
        for (at, block) in body.blocks.iter().enumerate() {
            if !live[at] {
                continue;
            }
            for to in block.term.targets() {
                if !live[to] || !doms.dominates(to, at) {
                    continue;
                }
                let held = found.entry(to).or_insert_with(|| {
                    let mut seed = vec![false; body.blocks.len()];
                    seed[to] = true;
                    seed
                });
                // Backwards from the block that goes round, stopping at the
                // head: everything met on the way is inside, and the head
                // being marked already is what stops the walk leaving.
                let mut stack = vec![at];
                while let Some(b) = stack.pop() {
                    if held[b] {
                        continue;
                    }
                    held[b] = true;
                    stack.extend(preds[b].iter().copied().filter(|&p| live[p]));
                }
            }
        }

        let mut out: Vec<Loop> = found
            .into_iter()
            .map(|(head, holds)| {
                let mut blocks = vec![head];
                blocks.extend(doms.order.iter().copied().filter(|&b| holds[b] && b != head));
                let mut back = Vec::new();
                let mut entries = Vec::new();
                for &p in &preds[head] {
                    if !live[p] {
                        continue;
                    }
                    if holds[p] {
                        back.push(p);
                    } else {
                        entries.push(p);
                    }
                }
                Loop { head, holds, blocks, back, entries }
            })
            .collect();
        // Innermost first, so that a pass which lifts something out of a loop
        // lifts it out of the tightest one first and finds it again, one round
        // later, standing in the loop outside that. The head breaks a tie:
        // they were gathered in a map, and two loops of a size would otherwise
        // be given in whatever order it held them, which is an order that can
        // differ between two runs over the one program.
        out.sort_by_key(|held| (held.blocks.len(), held.head));
        out
    }

    pub fn has(&self, at: SIRBlockId) -> bool {
        self.holds.get(at).copied().unwrap_or(false)
    }

    // Every edge that leaves, as the block it leaves from and the block it
    // goes to. A loop with one of them is one whose end is the head's own
    // test; a loop with more has a `break` in it somewhere.
    pub fn ways_out(&self, body: &SIRBody) -> Vec<(SIRBlockId, SIRBlockId)> {
        let mut out = Vec::new();
        for &at in &self.blocks {
            for to in body.blocks[at].term.targets() {
                if !self.has(to) && !out.contains(&(at, to)) {
                    out.push((at, to));
                }
            }
        }
        out
    }
}

// A block that stands between everything outside the loop and the head, made
// if there is not one already.
//
// This is what anything lifted out of a loop is lifted *into*, and the reason
// it has to exist rather than being any block above the head: what is put
// there must run once before the loop and must not run at all on a path that
// does not reach it. A block whose only business is to go to the head is the
// only place both hold.
//
// Only where there is one way in. Two ways in would mean the phis at the head
// have two answers from outside, and a preheader would have to join them with
// phis of its own -- which is a rewrite worth writing when something needs it,
// and nothing does: `while` and `for` both leave one way in, and a language
// with no `goto` has no third way to enter a loop.
pub fn preheader(body: &mut SIRBody, held: &Loop) -> Option<SIRBlockId> {
    if held.entries.len() != 1 {
        return None;
    }
    let from = held.entries[0];
    // Already one: it goes to the head and nowhere else, so nothing else can
    // reach what is put in it.
    if matches!(body.blocks[from].term, SIRTerm::Goto(to) if to == held.head) {
        return Some(from);
    }

    let (line, col) = (body.blocks[held.head].line, body.blocks[held.head].col);
    let made = body.blocks.len();
    body.blocks.push(SIRBlock {
        phis:  Vec::new(),
        insts: Vec::new(),
        term:  SIRTerm::Goto(held.head),
        line,
        col,
    });
    for to in body.blocks[from].term.targets_mut() {
        if *to == held.head {
            *to = made;
        }
    }
    // The head hears from the new block now, and what arrives along that edge
    // is what arrived along the old one.
    for phi in &mut body.blocks[held.head].phis {
        for (edge, _) in &mut phi.edges {
            if *edge == from {
                *edge = made;
            }
        }
    }
    Some(made)
}

#[cfg(test)]
mod tests;
