// Taking the names back out of the frame: the slots become values, and the
// joins they cross become phis.
//
// `sir::lower` puts every local in a slot and reaches it through a `Load` and
// a `Store`, which is correct and says nothing. What a name *holds* is the
// question every pass after this one asks, and asking it of memory means
// asking what else might have written there. This pass answers it once, for
// the names where the answer is knowable, and leaves the rest alone.
//
// Which names those are is one rule: a slot comes out when its address never
// goes anywhere but the `from` of a load or the `to` of a store. An address
// that reaches anything else -- handed to a call, kept in a structure, reached
// into by a field projection -- is an address something else may write
// through, and there is then no one instruction that made what the slot holds.
// That is why the lowering put *every* local in a slot first: the rule is
// about all the uses, and no pass that is still building them can apply it.
//
// The placement is Cytron, Ferrante, Rosen, Wegman and Zadeck's. A store is
// the last word on that name everywhere the storing block dominates, and stops
// being so exactly at that block's dominance frontier -- so a phi goes at the
// frontier of every block that stores, and then at the frontier of every block
// that got one, until nothing moves. See `dom.rs` for what a frontier is.
//
// The renaming is the other half, and it is a walk down the dominator tree
// with a stack per slot: entering a block pushes what it stores, leaving pops
// it, and a load reads whatever is on top. That works because the dominator
// tree is exactly the shape of "what is still in scope" -- a store reaches a
// use when its block dominates the use's, which is when it is still on the
// stack.
//
// What a load finds on an empty stack is `Undef`. `let x: T;` and then a jump
// over the line that fills it is a slot read on a path that never wrote it;
// `sema` is where that is refused, and inventing a zero here would be this
// pass answering a question that is not its own.

use std::collections::HashMap;

use super::dom::Dominators;
use super::sir_nodes::*;

// Every body, and how many slots came out. The count is what the driver
// prints; nothing else reads it.
pub fn promote(program: &mut SIRProgram) -> usize {
    program.bodies.iter_mut().map(one).sum()
}

fn one(body: &mut SIRBody) -> usize {
    // A block nothing reaches holds nothing this pass can be asked about. It
    // is emptied first rather than skipped everywhere below, because leaving
    // it standing gets two things wrong at once: an address escaping in dead
    // code would keep a name in the frame that nothing reads, and a `DropSlot`
    // there would still name a slot after the renumbering took it away.
    let live = body.live();
    for (at, block) in body.blocks.iter_mut().enumerate() {
        if live[at] {
            continue;
        }
        block.phis.clear();
        block.insts.clear();
        block.term = SIRTerm::Unreachable;
    }

    let owners = owners(body);
    let out = promotable(body, &owners);
    let taken = out.iter().filter(|ok| **ok).count();
    if taken == 0 {
        return 0;
    }

    let doms = Dominators::of(body);
    let undef = seed(body, &out);
    let of = place(body, &doms, &out, &owners);
    rename(body, &doms, &out, &owners, &of, &undef);
    compact(body, &out);
    prune(body);
    taken
}

// Which slot each address value is the address of. Every `Addr` makes one, and
// `sir::lower` makes a fresh one per use -- so this is a map from a value to
// the slot it names, and a value that is not in it is not a slot's address.
fn owners(body: &SIRBody) -> HashMap<SIRValueId, SIRSlotId> {
    let mut out = HashMap::new();
    for block in &body.blocks {
        for inst in &block.insts {
            if let (SIRInstKind::Addr(slot), Some(def)) = (&inst.kind, inst.def) {
                out.insert(def, *slot);
            }
        }
    }
    out
}

// The one rule, applied to every use in the body. Optimistic to start with:
// a slot is out unless something is found that keeps it in, which is the
// shape that lets a slot nothing touches at all disappear.
fn promotable(body: &SIRBody, owners: &HashMap<SIRValueId, SIRSlotId>) -> Vec<bool> {
    let mut out = vec![true; body.slots.len()];
    let keep = |value: &SIRValueId, out: &mut Vec<bool>| {
        if let Some(slot) = owners.get(value) {
            out[*slot] = false;
        }
    };
    for block in &body.blocks {
        for inst in &block.insts {
            match &inst.kind {
                // The two uses that are not an escape. A load reads what is
                // there and a store writes it; neither lets the address itself
                // go anywhere it could be read from again.
                SIRInstKind::Load { .. } => {}
                SIRInstKind::Store { value, .. } => keep(value, &mut out),
                other => {
                    for value in SIRBody::uses(other) {
                        keep(&value, &mut out);
                    }
                }
            }
        }
        // An address that leaves by an edge is an address this pass cannot
        // follow. Neither terminator can carry one out of a program that type
        // checks, and saying so costs two lines.
        match &block.term {
            SIRTerm::Branch { cond, .. } => keep(cond, &mut out),
            SIRTerm::Return(Some(value)) => keep(value, &mut out),
            _ => {}
        }
    }
    out
}

// An `Undef` per slot at the top of the entry, which is what a stack starts
// with. Made for every slot coming out and pruned again at the end, so a name
// that is always written before it is read leaves no trace of this.
fn seed(body: &mut SIRBody, out: &[bool]) -> HashMap<SIRSlotId, SIRValueId> {
    let (line, col) = (body.blocks[body.entry].line, body.blocks[body.entry].col);
    let mut made = HashMap::new();
    let mut insts = Vec::new();
    for (slot, ok) in out.iter().enumerate() {
        if !ok {
            continue;
        }
        let ty = body.slots[slot].ty;
        let of = body.slots[slot].of;
        body.values.push(SIRValue { ty, of, line, col });
        let def = body.values.len() - 1;
        insts.push(SIRInst {
            def:       Some(def),
            kind:      SIRInstKind::Undef,
            is_unsafe: false,
            line,
            col,
        });
        made.insert(slot, def);
    }
    let entry = body.entry;
    insts.append(&mut body.blocks[entry].insts);
    body.blocks[entry].insts = insts;
    made
}

// A phi at the frontier of everything that stores, and at the frontier of
// everything that gets one. Answers which slot each phi is for, in the order
// the phis stand in their block -- `SIRPhi` does not carry it, because once the
// renaming is done a phi is a value like any other and which slot it came out
// of is only this pass's business.
fn place(
    body: &mut SIRBody,
    doms: &Dominators,
    out: &[bool],
    owners: &HashMap<SIRValueId, SIRSlotId>,
) -> Vec<Vec<SIRSlotId>> {
    let frontiers = doms.frontiers(body);
    let live = body.live();
    let mut of: Vec<Vec<SIRSlotId>> = vec![Vec::new(); body.blocks.len()];

    // Where each slot is stored to, gathered once rather than per slot.
    let mut stores: HashMap<SIRSlotId, Vec<SIRBlockId>> = HashMap::new();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for inst in &block.insts {
            let SIRInstKind::Store { to, .. } = &inst.kind else { continue };
            let Some(slot) = owners.get(to) else { continue };
            if !out[*slot] {
                continue;
            }
            let held = stores.entry(*slot).or_default();
            if !held.contains(&at) {
                held.push(at);
            }
        }
    }

    for (slot, blocks) in stores {
        let mut work = blocks.clone();
        // Two sets, and they are not the same one. `has` stops a second phi
        // for one slot in one block; `ever` stops a block being walked from
        // twice. A block that stores *and* gets a phi is in both.
        let mut has: Vec<bool> = vec![false; body.blocks.len()];
        let mut ever: Vec<bool> = vec![false; body.blocks.len()];
        for &at in &blocks {
            ever[at] = true;
        }
        while let Some(at) = work.pop() {
            for &y in &frontiers[at] {
                if has[y] {
                    continue;
                }
                has[y] = true;
                let ty = body.slots[slot].ty;
                let held = body.slots[slot].of;
                let (line, col) = (body.blocks[y].line, body.blocks[y].col);
                body.values.push(SIRValue { ty, of: held, line, col });
                let def = body.values.len() - 1;
                body.blocks[y].phis.push(SIRPhi { def, edges: Vec::new() });
                of[y].push(slot);
                if !ever[y] {
                    ever[y] = true;
                    work.push(y);
                }
            }
        }
    }
    of
}

// The walk down the dominator tree. Iterative rather than recursive: the tree
// is as deep as the source is long, and a deep one should not take the stack
// with it.
fn rename(
    body: &mut SIRBody,
    doms: &Dominators,
    out: &[bool],
    owners: &HashMap<SIRValueId, SIRSlotId>,
    of: &[Vec<SIRSlotId>],
    undef: &HashMap<SIRSlotId, SIRValueId>,
) {
    let children = doms.children();
    let live = body.live();
    let mut stacks: Vec<Vec<SIRValueId>> = vec![Vec::new(); body.slots.len()];
    for (slot, value) in undef {
        stacks[*slot].push(*value);
    }
    // What a deleted load's value turned out to be. Filled as the walk goes
    // and applied to every operand at the end, because a use may stand in a
    // block the walk has not reached when the load it reads is taken out.
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    // What each block pushed, so leaving it can pop exactly that.
    let mut pushed: Vec<Vec<SIRSlotId>> = vec![Vec::new(); body.blocks.len()];

    let mut work = vec![(body.entry, false)];
    while let Some((at, leaving)) = work.pop() {
        if leaving {
            for slot in std::mem::take(&mut pushed[at]) {
                stacks[slot].pop();
            }
            continue;
        }
        work.push((at, true));

        let mut mine: Vec<SIRSlotId> = Vec::new();
        for (index, phi) in body.blocks[at].phis.iter().enumerate() {
            let slot = of[at][index];
            stacks[slot].push(phi.def);
            mine.push(slot);
        }

        let mut gone = vec![false; body.blocks[at].insts.len()];
        for index in 0..body.blocks[at].insts.len() {
            let kind = body.blocks[at].insts[index].kind.clone();
            match kind {
                SIRInstKind::Addr(slot) if out[slot] => gone[index] = true,
                SIRInstKind::Load { from } => {
                    let Some(&slot) = owners.get(&from) else { continue };
                    if !out[slot] {
                        continue;
                    }
                    let Some(def) = body.blocks[at].insts[index].def else { continue };
                    let held = *stacks[slot].last().expect("a stack is seeded");
                    subst.insert(def, held);
                    gone[index] = true;
                }
                SIRInstKind::Store { to, value } => {
                    let Some(&slot) = owners.get(&to) else { continue };
                    if !out[slot] {
                        continue;
                    }
                    // Resolved as it is pushed. What is stored may itself be a
                    // load this walk has already taken out, and a stack
                    // holding the name of something that no longer exists is
                    // what would leak out through a phi.
                    stacks[slot].push(settle(&subst, value));
                    mine.push(slot);
                    gone[index] = true;
                }
                // A promoted name is released as the value it is. Loading it
                // first would release a copy and leave the original, which is
                // why this is a rewrite and not two instructions.
                SIRInstKind::DropSlot(slot) if out[slot] => {
                    let held = *stacks[slot].last().expect("a stack is seeded");
                    body.blocks[at].insts[index].kind = SIRInstKind::Drop(held);
                }
                _ => {}
            }
        }
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[index - 1]
        });

        // What this block hands each of its successors, which is whatever is
        // on top now that the block is done.
        for to in body.blocks[at].term.targets() {
            for index in 0..body.blocks[to].phis.len() {
                let slot = of[to][index];
                let held = *stacks[slot].last().expect("a stack is seeded");
                body.blocks[to].phis[index].edges.push((at, held));
            }
        }

        pushed[at] = mine;
        for &child in &children[at] {
            if live[child] {
                work.push((child, false));
            }
        }
    }

    // And every operand that read a load which is no longer there.
    for block in &mut body.blocks {
        for phi in &mut block.phis {
            for (_, value) in &mut phi.edges {
                *value = settle(&subst, *value);
            }
        }
        for inst in &mut block.insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(&subst, *value);
            }
        }
        match &mut block.term {
            SIRTerm::Branch { cond, .. } => *cond = settle(&subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(&subst, *value),
            _ => {}
        }
    }
    for param in &mut body.params {
        *param = settle(&subst, *param);
    }
}

// What a value came to, following the chain as far as it goes. A load of a
// slot may be stored into a second slot and loaded back out, so one step is
// not always enough; the bound is the length of the map, which is what makes
// a cycle stop rather than spin.
fn settle(subst: &HashMap<SIRValueId, SIRValueId>, mut value: SIRValueId) -> SIRValueId {
    for _ in 0..=subst.len() {
        match subst.get(&value) {
            Some(&next) if next != value => value = next,
            _ => return value,
        }
    }
    value
}

// The slots that came out are gone, and the ones left are renumbered. Nothing
// still names a promoted one: every `Addr` of one was taken out and every
// `DropSlot` of one became a `Drop`.
fn compact(body: &mut SIRBody, out: &[bool]) {
    let mut map = vec![usize::MAX; body.slots.len()];
    let mut kept = Vec::new();
    for (slot, held) in body.slots.iter().enumerate() {
        if !out[slot] {
            map[slot] = kept.len();
            kept.push(held.clone());
        }
    }
    body.slots = kept;
    for block in &mut body.blocks {
        for inst in &mut block.insts {
            match &mut inst.kind {
                SIRInstKind::Addr(slot) | SIRInstKind::DropSlot(slot) => {
                    *slot = map[*slot];
                }
                _ => {}
            }
        }
    }
}

// The seeds nothing read. A slot written before every read of it needs no
// `Undef`, and leaving one behind would say there is a path that reads it
// unwritten when there is not.
fn prune(body: &mut SIRBody) {
    let mut read = vec![false; body.values.len()];
    for block in &body.blocks {
        for phi in &block.phis {
            for (_, value) in &phi.edges {
                read[*value] = true;
            }
        }
        for inst in &block.insts {
            for value in SIRBody::uses(&inst.kind) {
                read[value] = true;
            }
        }
        match &block.term {
            SIRTerm::Branch { cond, .. } => read[*cond] = true,
            SIRTerm::Return(Some(value)) => read[*value] = true,
            _ => {}
        }
    }
    for block in &mut body.blocks {
        block.insts.retain(|inst| match (&inst.kind, inst.def) {
            (SIRInstKind::Undef, Some(def)) => read[def],
            _ => true,
        });
    }
}

#[cfg(test)]
mod tests;
