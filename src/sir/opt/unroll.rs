// A loop whose number of turns is known before it starts is a straight line
// with the body written down that many times, and no test between the copies
// because there is nothing left for a test to decide.
//
// It is worth more here than the instructions it saves. `for i in 0..4` walks
// a cursor nothing can see into, and the value `i` takes is a question only
// the loop can answer -- until the turns are written out, and then `i` is 0 in
// the first copy and 1 in the second, and every operator over it folds. What
// unrolling really does in this pass is hand the four rewrites above something
// to work on.
//
// Which loops those are is the closed set `sir::lower` walks (§5: "the
// language has no iterator protocol, so what may be run through is a closed
// set"), asked one question: how many. A range between two literals runs the
// difference between them; an array of `T[n]` runs n. A run, a set and a map
// have a length nobody has worked out yet and are left alone.
//
// Three things are required of the shape, and the third is the one that
// refuses the most:
//
//   - the head ends in the walk's own test, and the arm it fails to is
//     outside the loop -- which is what makes the test the thing being taken
//     out;
//   - the copies fit: the turns are few and the body is small, because this
//     is the one rewrite here that makes a program bigger on purpose, and how
//     few and how small is what a `Level` says;
//   - and nothing the loop worked out is read past it except through a phi.
//     A phi is answered by giving it one entry per copy, which the rewrite
//     does anyway; anything else wanted one block standing before it, and
//     after this there are as many blocks as there were turns. With the head's
//     failing test as the only way out that never bites -- what the head made
//     is taken from the last head, which is the one that ran -- so it is only
//     a `break` that this ever turns down, and only a `break` that carries a
//     value out without a phi to carry it.
// How many turns, and what the loop variable is on each of them.

use std::collections::HashMap;

use crate::sir::dom::Dominators;
use crate::sir::loops::Loop;
use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRLit, TIRPrim, TIRRangeOp};
use crate::tir::ttir_nodes::{TTIRProgram, Ty};

use super::facts::*;
use super::fold::fits;
use super::graph::repair;
use super::{Level, Stats};

struct Turns {
    count: usize,
    // The first value and the type it is held in, where the walk is over a
    // range between two literals: then the element of turn `i` is `first + i`
    // and no cursor need survive. `None` for an array, whose elements are
    // whatever is in it and are still read one at a time.
    first: Option<(i64, TIRPrim)>,
}

pub(super) fn unroll(body: &mut SIRBody, ttir: &TTIRProgram, level: Level, stats: &mut Stats) -> bool {
    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        let Some((elem, exit)) = walked(body, &held) else { continue };
        let Some(turns) = counted(body, ttir, &held, elem, level) else { continue };
        let size: usize = held.blocks.iter().map(|&at| body.blocks[at].insts.len()).sum();
        if turns.count > level.unroll_turns() || size * (turns.count + 1) > level.unroll_insts() {
            continue;
        }
        // A second way out is a `break`, and it is allowed as long as nothing
        // the loop worked out is read past it other than through a phi. With
        // one way out that is not a limit at all -- what the head made can be
        // taken from the last head, which is the one that ran -- but a break
        // reaches the code after the loop without passing through the head, so
        // there is no one copy to take it from.
        if held.ways_out(body) != vec![(held.head, exit)] && reaches_out(body, &held) {
            continue;
        }
        written_round(body, &held, &turns, exit);
        stats.unrolled += 1;
        return true;
    }
    false
}

// Whether anything the loop makes is read outside it by something other than a
// phi. A phi is answered by giving it one edge per copy; anything else needs
// one block standing before it, and after this rewrite there are as many
// blocks as there were turns.
fn reaches_out(body: &SIRBody, held: &Loop) -> bool {
    let live = body.live();
    let mut within = vec![false; body.values.len()];
    for &at in &held.blocks {
        for phi in &body.blocks[at].phis {
            within[phi.def] = true;
        }
        for inst in &body.blocks[at].insts {
            if let Some(def) = inst.def {
                within[def] = true;
            }
        }
    }
    for at in 0..body.blocks.len() {
        if !live[at] || held.has(at) {
            continue;
        }
        for inst in &body.blocks[at].insts {
            if SIRBody::uses(&inst.kind).iter().any(|&value| within[value]) {
                return true;
            }
        }
        match &body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => {
                if within[*cond] {
                    return true;
                }
            }
            SIRTerm::Return(Some(value)) => {
                if within[*value] {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

// Whether the head is the top of a walk, and where it goes when the walk is
// done. The test is what `sir::lower` put there and nothing else looks like
// it: a branch on an `IterValid`, one arm inside the loop and one outside.
fn walked(body: &SIRBody, held: &Loop) -> Option<(SIRValueId, SIRBlockId)> {
    let SIRTerm::Branch { cond, then, els } = body.blocks[held.head].term else { return None };
    if !held.has(then) || held.has(els) {
        return None;
    }
    let made = made(body);
    let Some(SIRInstKind::IterValid { iter, .. }) = made.get(cond)? else { return None };
    Some((*iter, els))
}

// How many turns the walk takes, worked out from the thing being walked.
fn counted(
    body: &SIRBody,
    ttir: &TTIRProgram,
    held: &Loop,
    iter: SIRValueId,
    level: Level,
) -> Option<Turns> {
    let made = made(body);
    // The element type, which is what a range's values have to fit in.
    let elem = held.blocks.iter().find_map(|&at| {
        body.blocks[at].insts.iter().find_map(|inst| match inst.kind {
            SIRInstKind::IterElem { .. } => inst.def.map(|def| body.values[def].ty),
            _ => None,
        })
    });

    if let Some(SIRInstKind::Range { op, start: Some(from), end: Some(to) }) = made.get(iter)? {
        let (Some(TIRLit::Int(from)), Some(TIRLit::Int(to))) =
            (lit_of(&made, *from), lit_of(&made, *to))
        else {
            return None;
        };
        // In i128, where a range between the two ends of an i64 is still a
        // number: how many turns it takes is asked before anything decides
        // whether that is few enough to write out.
        let last = match op {
            TIRRangeOp::Inclusive => *to as i128,
            TIRRangeOp::Exclusive => *to as i128 - 1,
        };
        let count = usize::try_from((last - *from as i128 + 1).max(0)).ok()?;
        if count > level.unroll_turns() {
            return None;
        }
        // The values the loop variable takes are written as literals, so every
        // one of them has to be one the type can hold. The two ends answer for
        // all of them: what lies between them lies between them.
        let p = elem.and_then(|ty| prim(ttir, ty)).filter(|p| integer(*p))?;
        if count > 0 {
            fits(p, *from as i128)?;
            fits(p, *from as i128 + count as i128 - 1)?;
        }
        return Some(Turns { count, first: Some((*from, p)) });
    }
    // An array's length is in its type. What is in it is not, so the cursor
    // stays and only the tests go.
    if let Some(Ty::Array { len, .. }) = ttir.types.get(body.values[iter].ty) {
        return Some(Turns { count: usize::try_from(*len).ok()?, first: None });
    }
    None
}

// The loop, written out.
//
// One copy per turn, and one more of the head alone: the last head is where
// the test would have failed, and it is the block the code after the loop
// hears from -- so it has to be there, even though everything it works out is
// about a turn that does not happen.
//
// Every copy is a copy of the whole loop, values and all. What a copy reads
// that the loop made is that copy's; what it reads from before the loop is
// still the one value there always was. The edges are the only thing that
// differs: a copy's way round goes to the next copy's head rather than back to
// its own, which is what leaves a chain where there was a circle.
fn written_round(body: &mut SIRBody, held: &Loop, turns: &Turns, exit: SIRBlockId) {
    let n = turns.count;
    // By turn, then by block, what each block and each value became. The last
    // turn holds the head alone.
    let mut blocks: Vec<HashMap<SIRBlockId, SIRBlockId>> = Vec::new();
    let mut values: Vec<HashMap<SIRValueId, SIRValueId>> = Vec::new();

    for turn in 0..=n {
        let mut mine = HashMap::new();
        let mut made = HashMap::new();
        for &at in &held.blocks {
            if turn == n && at != held.head {
                continue;
            }
            let copy = body.blocks.len();
            body.blocks.push(body.blocks[at].clone());
            mine.insert(at, copy);
            for index in 0..body.blocks[copy].phis.len() {
                let def = body.blocks[copy].phis[index].def;
                body.values.push(body.values[def].clone());
                let fresh = body.values.len() - 1;
                body.blocks[copy].phis[index].def = fresh;
                made.insert(def, fresh);
            }
            for index in 0..body.blocks[copy].insts.len() {
                let Some(def) = body.blocks[copy].insts[index].def else { continue };
                body.values.push(body.values[def].clone());
                let fresh = body.values.len() - 1;
                body.blocks[copy].insts[index].def = Some(fresh);
                made.insert(def, fresh);
            }
        }
        blocks.push(mine);
        values.push(made);
    }

    let mine = |turn: usize, value: SIRValueId| {
        values[turn].get(&value).copied().unwrap_or(value)
    };

    for turn in 0..=n {
        // Down the loop's own list rather than the map's: what a map hands
        // back is in no order in particular, and two runs over one program
        // should not differ in what they write.
        for at in held.blocks.clone() {
            let Some(&copy) = blocks[turn].get(&at) else { continue };
            // The phis first. What arrives at a head arrives from the turn
            // before it, so its operands are that turn's and not this one's;
            // everywhere else the ways in are all inside the one turn.
            for index in 0..body.blocks[copy].phis.len() {
                let edges = body.blocks[copy].phis[index].edges.clone();
                let mut kept = Vec::new();
                for (from, value) in edges {
                    if at != held.head {
                        let Some(&edge) = blocks[turn].get(&from) else { continue };
                        kept.push((edge, mine(turn, value)));
                        continue;
                    }
                    match (held.has(from), turn) {
                        // The way in from before the loop, which only the
                        // first turn is reached by.
                        (false, 0) => kept.push((from, value)),
                        (false, _) => {}
                        (true, 0) => {}
                        (true, _) => {
                            if let Some(&edge) = blocks[turn - 1].get(&from) {
                                kept.push((edge, mine(turn - 1, value)));
                            }
                        }
                    }
                }
                body.blocks[copy].phis[index].edges = kept;
            }

            for index in 0..body.blocks[copy].insts.len() {
                for value in SIRBody::uses_mut(&mut body.blocks[copy].insts[index].kind) {
                    *value = mine(turn, *value);
                }
                // The element of this turn, where the walk is over a range
                // between two literals: it is `first + turn`, and saying so is
                // what leaves the loop variable a literal for `fold` to work
                // with.
                if let (SIRInstKind::IterElem { .. }, Some((first, p))) =
                    (&body.blocks[copy].insts[index].kind, turns.first)
                {
                    if turn < n {
                        let held = fits(p, first as i128 + turn as i128)
                            .expect("the turns were checked before the copies were made");
                        body.blocks[copy].insts[index].kind =
                            SIRInstKind::Literal(TIRLit::Int(held));

// How many turns, and what the loop variable is on each of them.
                    }
                }
            }

            // And where it goes. The head's test is settled -- every copy but
            // the last takes the arm that carries on, and the last takes the
            // one that leaves -- and a way round becomes the way into the turn
            // after it.
            let mut term = body.blocks[copy].term.clone();
            if at == held.head {
                let SIRTerm::Branch { then, .. } = term else { unreachable!() };
                term = if turn == n { SIRTerm::Goto(exit) } else { SIRTerm::Goto(then) };
            }
            if let SIRTerm::Branch { cond, .. } = &mut term {
                *cond = mine(turn, *cond);
            }
            for to in term.targets_mut() {
                if !held.has(*to) {
                    continue;
                }
                let next = if *to == held.head { turn + 1 } else { turn };
                if let Some(&edge) = blocks.get(next).and_then(|held| held.get(to)) {
                    *to = edge;
                }
            }
            body.blocks[copy].term = term;
        }
    }

    // What the blocks after the loop hear, and who from. Every edge that used
    // to leave the loop leaves a copy of it now, so the phis they land in take
    // one entry per copy that still goes there -- and the copies that no
    // longer do are answered by `repair`, which holds a phi to the ways in the
    // block actually has.
    let mut outside: Vec<(SIRBlockId, SIRBlockId, usize)> = Vec::new();
    for turn in 0..=n {
        for &at in &held.blocks {
            let Some(&copy) = blocks[turn].get(&at) else { continue };
            for to in body.blocks[copy].term.targets() {
                if !held.has(to) && to < body.blocks.len() {
                    outside.push((at, to, turn));
                }
            }
        }
    }
    for (at, to, turn) in outside {
        let copy = blocks[turn][&at];
        for phi in &mut body.blocks[to].phis {
            let Some(&(_, value)) = phi.edges.iter().find(|(from, _)| *from == at) else {
                continue;
            };
            let held = mine(turn, value);
            if !phi.edges.iter().any(|(from, _)| *from == copy) {
                phi.edges.push((copy, held));
            }
        }
    }
    for at in 0..body.blocks.len() {
        if held.has(at) {
            continue;
        }
        for phi in &mut body.blocks[at].phis {
            phi.edges.retain(|(from, _)| !held.has(*from));
        }
    }

    // The ways in, which go to the first turn now. The loop's own blocks are
    // left standing and unreachable, which is what `sweep` is for.
    for &from in &held.entries {
        for to in body.blocks[from].term.targets_mut() {
            if *to == held.head {
                *to = blocks[0][&held.head];
            }
        }
    }

    // And what the head worked out, read from after the loop: the last head is
    // the one that ran, so it is the one that answers. Nothing else inside can
    // be read out there -- the head's failing test is the only way out, so no
    // other block of the loop stands before anything after it.
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    for (value, held) in &values[n] {
        subst.insert(*value, *held);
    }
    for at in 0..body.blocks.len() {
        if held.has(at) || blocks.iter().any(|turn| turn.values().any(|&copy| copy == at)) {
            continue;
        }
        // The phis as well: an edge into a block after the loop may carry
        // what the head worked out, and the block it comes along is not one
        // of the copies -- the copies were given their own values above.
        for phi in &mut body.blocks[at].phis {
            for (_, value) in &mut phi.edges {
                *value = settle(&subst, *value);
            }
        }
        for inst in &mut body.blocks[at].insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(&subst, *value);
            }
        }
        match &mut body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => *cond = settle(&subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(&subst, *value),
            _ => {}
        }
    }
    repair(body);
}
