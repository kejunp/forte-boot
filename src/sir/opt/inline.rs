// A call written out where it was called.
//
// It is the rewrite that makes the rest of them worth running. A call carries
// its arguments into a body that cannot see where they came from, so a
// literal argument and the operator that would fold it are in two bodies and
// neither pass can see both; writing the body out puts them next to each
// other, and then everything else in this pass has something to do.
//
// It is also the only rewrite here that can make a program bigger without
// bound, so it is bounded three ways: by how big a callee may be, by how many
// calls one body may take in a round, and by refusing outright wherever the
// callee can reach itself. The last is the one that matters -- the others are
// guesses about what is worth doing and that one is the difference between a
// rewrite that stops and one that does not.

use std::collections::HashMap;

use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::TIRInline;
use crate::tir::ttir_nodes::{TTIRItemId, TTIRItemKind, TTIRProgram};

use super::facts::*;
use super::{Level, Stats};

// Which body each declaration is, and which bodies each body can reach. The
// first is what a call has to be looked up in -- a `Call` names a value, the
// value is an `Item`, and the item is where the body is written -- and the
// second is what says whether writing one out would ever stop.
pub(super) struct Calls {
    // By item, the body it is the body of. Only the fns that have one and take
    // no generic parameters: a generic body is one body for every type it is
    // called at, and nothing has monomorphised it, so the body written out
    // would be the wrong one for all but one caller.
    of:    HashMap<TTIRItemId, (SIRBodyId, TIRInline)>,
    // By body, the bodies it can reach through a call or a closure. Reachable
    // and not just called: a body that makes a closure may call it, and
    // whether it does is not a question this has to answer to be safe.
    reach: Vec<Vec<SIRBodyId>>,
}

impl Calls {
    pub(super) fn of(program: &SIRProgram, ttir: &TTIRProgram) -> Calls {
        let mut of = HashMap::new();
        for (id, item) in ttir.items.iter().enumerate() {
            let TTIRItemKind::Fn(f) = &item.kind else { continue };
            let Some(body) = f.body else { continue };
            if !f.generics.is_empty() || body >= program.bodies.len() {
                continue;
            }
            of.insert(id, (body, f.attrs.inline));
        }

        // One step first, then closed over: reaching is the transitive
        // closure, and a body that can reach the body it stands in is one
        // nothing may be written into.
        let mut reach: Vec<Vec<SIRBodyId>> = vec![Vec::new(); program.bodies.len()];
        for (id, body) in program.bodies.iter().enumerate() {
            for block in &body.blocks {
                for inst in &block.insts {
                    let to = match &inst.kind {
                        SIRInstKind::Item(item) => of.get(item).map(|(body, _)| *body),
                        SIRInstKind::Closure { body, .. } => Some(*body),
                        _ => None,
                    };
                    if let Some(to) = to {
                        if to < reach.len() && !reach[id].contains(&to) {
                            reach[id].push(to);
                        }
                    }
                }
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for id in 0..reach.len() {
                let held = reach[id].clone();
                for to in held {
                    for &far in &reach[to].clone() {
                        if !reach[id].contains(&far) {
                            reach[id].push(far);
                            changed = true;
                        }
                    }
                }
            }
        }
        Calls { of, reach }
    }

    // Whether writing this callee into this caller is a rewrite there would
    // be no end to. Three ways, and the third is the one that is easy to miss:
    // a body written into itself, a body that can reach the one it would be
    // written into -- and a body that can reach *itself*, which is bounded
    // only by how many times this pass is willing to go round, and is a loop
    // unrolled by accident rather than a call written out.
    fn cycles(&self, callee: SIRBodyId, caller: SIRBodyId) -> bool {
        callee == caller
            || self.reach[callee].contains(&caller)
            || self.reach[callee].contains(&callee)
    }
}

// Where one call stands and what it was handed.
struct Site {
    at:     SIRBlockId,
    index:  usize,
    callee: SIRBodyId,
    args:   Vec<SIRValueId>,
    def:    Option<SIRValueId>,
}

pub(super) fn inline(program: &mut SIRProgram, graph: &Calls, level: Level, stats: &mut Stats) -> bool {
    let mut changed = false;
    for caller in 0..program.bodies.len() {
        for _ in 0..level.inline_each() {
            let Some(site) = pick(program, graph, caller, level) else { break };
            let callee = program.bodies[site.callee].clone();
            written_out(&mut program.bodies[caller], &callee, &site);
            stats.inlined += 1;
            changed = true;
        }
    }
    changed
}

// The first call in the body worth writing out. First and not best: the ones
// refused are refused on a rule, and among the rest one call is much like
// another at this size.
fn pick(program: &SIRProgram, graph: &Calls, caller: SIRBodyId, level: Level) -> Option<Site> {
    let body = &program.bodies[caller];
    let held = made(body);
    let live = body.live();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for (index, inst) in body.blocks[at].insts.iter().enumerate() {
            let SIRInstKind::Call { callee, args } = &inst.kind else { continue };
            let Some(Some(SIRInstKind::Item(item))) = held.get(*callee) else { continue };
            let Some(&(callee, asked)) = graph.of.get(item) else { continue };
            // `%noinline` is a promise and not a preference (§1): whatever
            // this pass would have made of the size, it has been answered.
            if asked == TIRInline::Never || graph.cycles(callee, caller) {
                continue;
            }
            if !worth(&program.bodies[callee], inst, args, asked, level) {
                continue;
            }
            return Some(Site {
                at,
                index,
                callee,
                args: args.clone(),
                def: inst.def,
            });
        }
    }
    None
}

// Whether this body may stand where this call did.
fn worth(
    callee: &SIRBody,
    call: &SIRInst,
    args: &[SIRValueId],
    asked: TIRInline,
    level: Level,
) -> bool {
    if callee.params.len() != args.len() {
        return false;
    }
    let live = callee.live();
    let mut size = 0;
    for (at, block) in callee.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        size += block.insts.len();
        for inst in &block.insts {
            // A receiver is a value the caller has not got. A method is
            // called through `Method` rather than `Call` and so is not
            // reached here at all, but a fn body that names `self` would
            // be one written out with nothing to put in its place.
            if matches!(inst.kind, SIRInstKind::SelfValue | SIRInstKind::SelfAddr) {
                return false;
            }
        }
        // What the call makes has to come from somewhere on every path that
        // gets back, so a body that returns without a value cannot stand where
        // a call that makes one did.
        if call.def.is_some() && matches!(block.term, SIRTerm::Return(None)) {
            return false;
        }
    }
    // The size is this pass's guess at what a call is worth, and `%inline` is
    // the source saying it has a better one. Everything above this line is a
    // rule about whether the rewrite is *sound*, and a hint waives none of it.
    asked == TIRInline::Always || size <= level.inline_max()
}

// The callee written into the caller at the call.
//
// Four things move, and the ids of all four are the caller's now: the values,
// the slots, the blocks, and the edges between them. The parameters are the
// exception -- they are made by no instruction, being what the caller handed
// over, so they are not copied at all and every read of one reads the argument
// instead.
//
// The call's own block is cut in two at the call. What stood above it stays;
// what stood below it, and the terminator, become a block the callee's returns
// go to. That block is where the call's value is made, by a phi over the
// blocks that returned one -- which is the one place the value can be made,
// there being as many answers as there are ways back.
fn written_out(caller: &mut SIRBody, callee: &SIRBody, site: &Site) {
    let vbase = caller.values.len();
    let sbase = caller.slots.len();
    let bbase = caller.blocks.len();
    let back = bbase + callee.blocks.len();

    caller.values.extend(callee.values.iter().cloned());
    caller.slots.extend(callee.slots.iter().cloned());

    // A parameter is the argument; everything else is itself, one arena
    // further along.
    let value = |v: SIRValueId| match callee.params.iter().position(|&p| p == v) {
        Some(index) => site.args[index],
        None => v + vbase,
    };

    let live = callee.live();
    let mut edges: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
    for (at, block) in callee.blocks.iter().enumerate() {
        let mut moved = block.clone();
        for phi in &mut moved.phis {
            phi.def += vbase;
            for (from, held) in &mut phi.edges {
                *from += bbase;
                *held = value(*held);
            }
        }
        for inst in &mut moved.insts {
            if let Some(def) = &mut inst.def {
                *def += vbase;
            }
            for held in SIRBody::uses_mut(&mut inst.kind) {
                *held = value(*held);
            }
            match &mut inst.kind {
                SIRInstKind::Addr(slot) | SIRInstKind::DropSlot(slot) => *slot += sbase,
                _ => {}
            }
        }
        match &mut moved.term {
            SIRTerm::Return(held) => {
                if live[at] {
                    if let Some(held) = held {
                        edges.push((at + bbase, value(*held)));
                    }
                }
                moved.term = SIRTerm::Goto(back);
            }
            term => {
                for to in term.targets_mut() {
                    *to += bbase;
                }
                if let SIRTerm::Branch { cond, .. } = term {
                    *cond = value(*cond);
                }
            }
        }
        caller.blocks.push(moved);
    }

    // The call's block, cut. The call itself goes: what it made is made by the
    // phi below instead.
    let tail = caller.blocks[site.at].insts.split_off(site.index + 1);
    caller.blocks[site.at].insts.pop();
    let term = std::mem::replace(
        &mut caller.blocks[site.at].term,
        SIRTerm::Goto(bbase + callee.entry),
    );
    let (line, col) = (caller.blocks[site.at].line, caller.blocks[site.at].col);

    // And whoever heard from that block hears from the block below the call.
    for to in term.targets() {
        for phi in &mut caller.blocks[to].phis {
            for (from, _) in &mut phi.edges {
                if *from == site.at {
                    *from = back;
                }
            }
        }
    }

    let mut phis = Vec::new();
    if let Some(def) = site.def {
        if !edges.is_empty() {
            phis.push(SIRPhi { def, edges });
        }
    }
    caller.blocks.push(SIRBlock { phis, insts: tail, term, line, col });
}
