// What being in SSA form comes to, checked rather than assumed.
//
// Two rules carry the whole of it. A value is made in one place, and a value
// is read only where the place that made it stands between the read and the
// entry. Everything a later pass wants to do -- ask what a name holds, move an
// instruction, fold two into one -- leans on both, and a pass that breaks one
// of them breaks it silently: the graph still walks, and the answer is wrong
// somewhere else.
//
// So this is here from the start rather than after the first bug. It is run by
// the tests of both passes over every body they build, which is what makes a
// test that only looks at one instruction still say something about the rest.
//
// A phi is checked against the edge and not against the block. Its operands
// arrive along the way in, so what has to dominate is the *predecessor* the
// operand came from -- a value made in the block the phi stands in would not
// be there yet, and one made in a sibling of the predecessor never arrives.

use super::dom::Dominators;
use super::sir_nodes::*;

// Everything wrong with the body, in the words a failing test should print.
// Empty is the answer a correct body gives.
pub fn verify(body: &SIRBody) -> Vec<String> {
    let mut wrong = Vec::new();
    let doms = Dominators::of(body);
    let live = body.live();
    let preds = body.preds();

    // Where each value is made. A parameter is made by the caller, which is
    // the entry as far as anything here can see.
    let mut made: Vec<Option<SIRBlockId>> = vec![None; body.values.len()];
    let twice = |value: SIRValueId, at: SIRBlockId, made: &mut Vec<Option<SIRBlockId>>,
                     wrong: &mut Vec<String>| {
        if value >= made.len() {
            wrong.push(format!("value %{} is not in the arena", value));
            return;
        }
        if made[value].is_some() {
            wrong.push(format!("value %{} is made more than once", value));
        }
        made[value] = Some(at);
    };
    for &param in &body.params {
        twice(param, body.entry, &mut made, &mut wrong);
    }
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for phi in &block.phis {
            twice(phi.def, at, &mut made, &mut wrong);
        }
        for inst in &block.insts {
            if let Some(def) = inst.def {
                twice(def, at, &mut made, &mut wrong);
            }
        }
    }

    // And where each is read, which has to be somewhere its maker reaches.
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }

        let live_preds: Vec<SIRBlockId> =
            preds[at].iter().copied().filter(|&p| live[p]).collect();
        for phi in &block.phis {
            if phi.edges.len() != live_preds.len() {
                wrong.push(format!(
                    "phi %{} in b{} has {} edges and b{} has {} ways in",
                    phi.def,
                    at,
                    phi.edges.len(),
                    at,
                    live_preds.len()
                ));
            }
            for &(from, value) in &phi.edges {
                if !live_preds.contains(&from) {
                    wrong.push(format!(
                        "phi %{} in b{} names b{}, which is not a way in",
                        phi.def, at, from
                    ));
                }
                reaches(&doms, &made, value, from, &format!(
                    "phi %{} in b{} along b{}", phi.def, at, from
                ), &mut wrong);
            }
        }

        for (index, inst) in block.insts.iter().enumerate() {
            for value in SIRBody::uses(&inst.kind) {
                reaches(&doms, &made, value, at, &format!("b{}, instruction {}", at, index),
                        &mut wrong);
            }
            if let SIRInstKind::Addr(slot) | SIRInstKind::DropSlot(slot) = inst.kind {
                if slot >= body.slots.len() {
                    wrong.push(format!("b{} names slot ${}, which is not there", at, slot));
                }
            }
        }

        match &block.term {
            SIRTerm::Branch { cond, .. } => {
                reaches(&doms, &made, *cond, at, &format!("the branch out of b{}", at),
                        &mut wrong);
            }
            SIRTerm::Return(Some(value)) => {
                reaches(&doms, &made, *value, at, &format!("the return out of b{}", at),
                        &mut wrong);
            }
            _ => {}
        }
        for to in block.term.targets() {
            if to >= body.blocks.len() {
                wrong.push(format!("b{} goes to b{}, which is not there", at, to));
            }
        }
    }
    wrong
}

// Whether the value read in `at` was made somewhere that stands before it.
// Which block, only: two instructions in the one block are both dominated by
// it, and which of them comes first is `verify_order`'s -- a phi's operands
// have no place in a block at all, so one function cannot answer both.
fn reaches(
    doms: &Dominators,
    made: &[Option<SIRBlockId>],
    value: SIRValueId,
    at: SIRBlockId,
    what: &str,
    wrong: &mut Vec<String>,
) {
    let Some(&Some(from)) = made.get(value) else {
        wrong.push(format!("{} reads %{}, which nothing makes", what, value));
        return;
    };
    if !doms.dominates(from, at) {
        wrong.push(format!(
            "{} reads %{}, made in b{}, which does not stand before it",
            what, value, from
        ));
    }
}

// The same, and the order within a block as well: a value read above the
// instruction that makes it is the one way a use can be in the right block and
// still be wrong. Kept apart from `reaches` because it needs the block's list
// and `reaches` is also asked about phis, which have none.
pub fn verify_order(body: &SIRBody) -> Vec<String> {
    let mut wrong = Vec::new();
    let live = body.live();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        // A phi's value counts as made before anything else in the block, and
        // an instruction's where it stands.
        let mut seen: Vec<Option<usize>> = vec![None; body.values.len()];
        for phi in &block.phis {
            if phi.def < seen.len() {
                seen[phi.def] = Some(0);
            }
        }
        for (index, inst) in block.insts.iter().enumerate() {
            for value in SIRBody::uses(&inst.kind) {
                if let Some(Some(made)) = seen.get(value) {
                    if *made > index {
                        wrong.push(format!(
                            "b{}, instruction {} reads %{}, which b{} makes below it",
                            at, index, value, at
                        ));
                    }
                }
            }
            if let Some(def) = inst.def {
                if def < seen.len() {
                    seen[def] = Some(index + 1);
                }
            }
        }
    }
    wrong
}
