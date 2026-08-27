// Which blocks stand between the entry and a block, which is the question
// every phi is placed by answering.
//
// A block `a` dominates a block `b` when no path from the entry reaches `b`
// without going through `a`. That is what makes a value usable: an instruction
// may read a value only where the block that made it dominates the block that
// reads it, because anywhere else there is a path in that never made it.
//
// The *frontier* is the other half. `a`'s dominance frontier is every block
// `a` does not dominate but reaches -- the first blocks past where `a`'s reach
// stops. A store in `a` is the last word on that name everywhere `a`
// dominates, and stops being so exactly at the frontier, so the frontier is
// where the phi goes. That is `sir::promote`'s whole placement rule.
//
// The algorithm is Cooper, Harvey and Kennedy's: walk the blocks in reverse
// postorder, intersect the predecessors' immediate dominators, and repeat
// until nothing moves. It is quadratic in the worst case and faster than the
// asymptotically better ones on the graphs a compiler actually sees, which is
// the paper's point.
//
// A block the entry cannot reach has no immediate dominator -- not the entry,
// which does not reach it either. It is `None` here rather than a number, and
// every caller has to say what it does about one.

use super::sir_nodes::{SIRBlockId, SIRBody};

pub struct Dominators {
    // The blocks the entry reaches, deepest last: a block always stands after
    // every block that dominates it, which is what lets one walk fill a stack
    // and the next unwind it.
    pub order: Vec<SIRBlockId>,
    // The nearest block that dominates it and is not it. `None` where the
    // entry does not reach the block, and for the entry itself -- which
    // dominates everything and is dominated by nothing.
    pub idom:  Vec<Option<SIRBlockId>>,
}

impl Dominators {
    pub fn of(body: &SIRBody) -> Dominators {
        let n = body.blocks.len();
        let preds = body.preds();
        let order = reverse_postorder(body);

        // Where a block stands in that order, so intersecting can walk two
        // chains towards the entry by always moving the one that is deeper.
        let mut rank = vec![usize::MAX; n];
        for (at, &block) in order.iter().enumerate() {
            rank[block] = at;
        }

        let mut idom: Vec<Option<SIRBlockId>> = vec![None; n];
        // The entry is its own, for the length of the fixpoint only: it is the
        // value the intersection needs a chain to end at, and it is taken back
        // out below so that "the entry has no dominator" is what a reader sees.
        idom[body.entry] = Some(body.entry);

        let mut changed = true;
        while changed {
            changed = false;
            for &block in &order {
                if block == body.entry {
                    continue;
                }
                // The first predecessor already settled. One always is: a
                // block in reverse postorder that is not the entry is reached
                // from somewhere earlier, unless every way in is a back edge,
                // and then the loop goes round again.
                let mut new: Option<SIRBlockId> = None;
                for &p in &preds[block] {
                    if idom[p].is_none() {
                        continue;
                    }
                    new = Some(match new {
                        None => p,
                        Some(held) => intersect(&idom, &rank, held, p),
                    });
                }
                if new.is_some() && new != idom[block] {
                    idom[block] = new;
                    changed = true;
                }
            }
        }

        idom[body.entry] = None;
        Dominators { order, idom }
    }

    // Whether `a` dominates `b`, by walking `b` up to the entry. Every block
    // dominates itself, which is what makes "the block that made it dominates
    // the block that reads it" true of two uses in the one block.
    pub fn dominates(&self, a: SIRBlockId, b: SIRBlockId) -> bool {
        if a == b {
            return true;
        }
        let mut at = self.idom[b];
        while let Some(up) = at {
            if up == a {
                return true;
            }
            at = self.idom[up];
        }
        false
    }

    // The blocks each block immediately dominates, which is the dominator tree
    // read downwards. `sir::promote` walks it, and a walk wants children.
    pub fn children(&self) -> Vec<Vec<SIRBlockId>> {
        let mut out = vec![Vec::new(); self.idom.len()];
        for (block, up) in self.idom.iter().enumerate() {
            if let Some(up) = up {
                out[*up].push(block);
            }
        }
        out
    }

    // Where each block's reach stops. A block with one predecessor is on
    // nobody's frontier -- there is no other way in, so whatever held before it
    // still holds -- which is why only the joins are walked.
    pub fn frontiers(&self, body: &SIRBody) -> Vec<Vec<SIRBlockId>> {
        let preds = body.preds();
        let mut out = vec![Vec::new(); body.blocks.len()];
        for block in 0..body.blocks.len() {
            // Only the ways in that are ways in. A block nothing reaches
            // reaches nothing either, and counting it would make a join out of
            // somewhere only one live path arrives at.
            let live: Vec<SIRBlockId> = preds[block]
                .iter()
                .copied()
                .filter(|&p| p == body.entry || self.idom[p].is_some())
                .collect();
            if live.len() < 2 {
                continue;
            }
            for &p in &live {
                // Up from the predecessor until the block's own dominator is
                // reached: everything passed on the way reaches this join
                // without dominating it.
                let mut at = p;
                while Some(at) != self.idom[block] {
                    if !out[at].contains(&block) {
                        out[at].push(block);
                    }
                    match self.idom[at] {
                        Some(up) => at = up,
                        None => break,
                    }
                }
            }
        }
        out
    }
}

// The nearest block that dominates both, found by walking the deeper of the two
// up until they meet. "Deeper" is later in reverse postorder, which is what the
// ranks are for.
fn intersect(
    idom: &[Option<SIRBlockId>],
    rank: &[usize],
    mut a: SIRBlockId,
    mut b: SIRBlockId,
) -> SIRBlockId {
    while a != b {
        while rank[a] > rank[b] {
            match idom[a] {
                Some(up) if up != a => a = up,
                _ => return b,
            }
        }
        while rank[b] > rank[a] {
            match idom[b] {
                Some(up) if up != b => b = up,
                _ => return a,
            }
        }
        if rank[a] == rank[b] && a != b {
            // Two blocks at one rank cannot both be reachable, so this is a
            // graph the walk has already left. Stopping beats looping.
            return a;
        }
    }
    a
}

// Postorder from the entry, reversed: every block stands before the blocks it
// reaches, except across a back edge. Iterative rather than recursive -- a
// body's graph is as deep as its source is long, and a deep one should not
// take the stack with it.
fn reverse_postorder(body: &SIRBody) -> Vec<SIRBlockId> {
    let mut seen = vec![false; body.blocks.len()];
    let mut post = Vec::new();
    // The block, and how many of its successors have been started.
    let mut stack: Vec<(SIRBlockId, usize)> = vec![(body.entry, 0)];
    seen[body.entry] = true;
    while let Some((block, next)) = stack.pop() {
        let targets = body.blocks[block].term.targets();
        if next < targets.len() {
            stack.push((block, next + 1));
            let to = targets[next];
            if !seen[to] {
                seen[to] = true;
                stack.push((to, 0));
            }
        } else {
            post.push(block);
        }
    }
    post.reverse();
    post
}

#[cfg(test)]
mod tests;
