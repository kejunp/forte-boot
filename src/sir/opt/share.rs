// Two values that turn out to be one value.
//
// Two rewrites and one idea. A phi whose edges all name one value is a join
// where nothing was decided, and it *is* that value. Two instructions with the
// same operands doing the same thing make the same value, so the second may be
// the first -- wherever the first stands before it on every path, which is
// dominance and nothing weaker.
//
// What neither of them may do is turn one thing into two names for it. A value
// with something to release is released once per name, so `shareable` is what
// both are held to, and the addresses are the exception it is worth making:
// two names for one place are one name whatever is kept there.

use std::collections::HashMap;

use crate::sir::dom::Dominators;
use crate::sir::sir_nodes::*;
use crate::tir::ttir_nodes::{TTIRProgram, TyId};

use super::facts::*;
use super::Stats;

// A phi whose edges all name one value is a join where nothing was decided:
// every way in brought the same thing, so the phi *is* that thing. Its own
// name among the edges does not count -- a loop's phi naming itself along the
// back edge still has one answer, which is what came in the first time round.
pub(super) fn phis(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        body.blocks[at].phis.retain(|phi| {
            let mut one: Option<SIRValueId> = None;
            for (_, value) in &phi.edges {
                if *value == phi.def {
                    continue;
                }
                match one {
                    None => one = Some(*value),
                    Some(held) if held == *value => {}
                    // Two answers, so the phi is what says which.
                    Some(_) => return true,
                }
            }
            match one {
                Some(value) => {
                    subst.insert(phi.def, value);
                    false
                }
                // Every edge named the phi itself, which is a value with no
                // first answer at all. Nothing here can invent one.
                None => true,
            }
        });
    }
    stats.shared += subst.len();
    let changed = !subst.is_empty();
    replace(body, &subst);
    changed
}

// ---- One value for two instructions ---------------------------------------

// Two instructions that read the same values and do the same thing to them
// make the same value, so the second can be the first -- but only where the
// first stands before it on every path, which is dominance and nothing weaker.
// So the walk is down the dominator tree: what a block adds is visible to
// everything below it and taken back off on the way out, which is exactly the
// set of instructions that stand before the block being walked.
pub(super) fn share(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let doms = Dominators::of(body);
    let children = doms.children();
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    // What is in hand, deepest last, and how much of it each block added. A
    // list and not a map: `SIRInstKind` holds an f64 and so cannot be hashed,
    // and the lists a block's worth of instructions makes are short.
    let mut seen: Vec<(SIRInstKind, TyId, SIRValueId)> = Vec::new();
    let mut added = vec![0usize; body.blocks.len()];

    let mut work = vec![(body.entry, false)];
    while let Some((at, leaving)) = work.pop() {
        if leaving {
            seen.truncate(added[at]);
            continue;
        }
        added[at] = seen.len();
        work.push((at, true));

        for index in 0..body.blocks[at].insts.len() {
            let Some(def) = body.blocks[at].insts[index].def else { continue };
            let mut kind = body.blocks[at].insts[index].kind.clone();
            for value in SIRBody::uses_mut(&mut kind) {
                *value = settle(&subst, *value);
            }
            if !known(&kind) {
                continue;
            }
            let ty = body.values[def].ty;
            // An address is a place and not a thing: two names for one place
            // are one name whatever is kept there, which is why the addresses
            // do not go through `shareable` and everything else does.
            let place = matches!(
                kind,
                SIRInstKind::Addr(_)
                    | SIRInstKind::ItemAddr(_)
                    | SIRInstKind::SelfAddr
                    | SIRInstKind::FieldAddr { .. }
                    | SIRInstKind::TupleAddr { .. }
            );
            if !place && !shareable(ttir, ty) {
                continue;
            }
            match seen.iter().find(|(held, of, _)| alike(ttir, *of, ty) && *held == kind) {
                Some((_, _, held)) => {
                    subst.insert(def, *held);
                    gone[at][index] = true;
                    stats.shared += 1;
                }
                None => seen.push((kind, ty, def)),
            }
        }

        for &child in &children[at] {
            if live[child] {
                work.push((child, false));
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
