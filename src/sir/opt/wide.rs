// The same thing done to four neighbouring places, done once.
//
// This is superword-level parallelism, and it is here rather than a loop
// vectorizer because of the order the rewrites above happen in. `unroll` has
// already written a counted loop out as its turns, so what would have been a
// loop to widen is a straight run of instructions in one block, each doing to
// element `k + j` what the one before did to `k + j - 1`. Finding that is a
// matter of looking at a list, which is a much smaller thing than reasoning
// about a loop -- and everything the loop version would have had to prove has
// already been proved by the passes that got here.
//
// It starts at the writes and works upwards. A run of stores to consecutive
// elements of one thing is the seed: whatever they store is a group of four
// values that want to be one, and what made those is a group of instructions
// that want to be one instruction. Upwards from there until it reaches
// something it cannot group, and then that is packed as it stands.
//
// Four things have to hold, and three of them are answered by work already
// done:
//
//   - the elements have to be neighbours, which needs the numbers indexing
//     them to be literals -- which is what `unroll` leaves behind when it
//     writes out a walk over a range;
//   - the writes have to be able to happen together, which means nothing
//     between them may read or write where they do: `sir::alias`;
//   - nothing being grouped may trap or have an effect, because a vector
//     instruction is one instruction and cannot trap for the third lane only:
//     `effects`, the same answer `sweep` and `hoist` are held to;
//   - and the machine has to be able to do it: as many at once as fit in one
//     of its registers, and an instruction that exists over that many. That is
//     `sir::target`, which is a description of a machine rather than a guess
//     about one -- there is no integer divide over a vector on anything, so
//     four divisions stay four however neatly they line up.
//
// And then, having found a group it *may* make, it asks whether it should.
// Four instructions become one, which is a saving; four values that have to be
// put into a register one at a time are four instructions, which is not. See
// `pays`, where the two are counted against each other, and where an
// instruction something else still reads counts as no saving at all.
//
// Nothing is taken out. The scalar instructions are left where they are and
// `sweep` removes the ones nothing reads any more, which is what makes this
// safe to do to a group whose values are also read by something that was not
// part of it: that use still reads the scalar, and the scalar is still there.

use crate::sir::alias::{Alias, Base};
use crate::sir::sir_nodes::*;
use crate::sir::target::{self, Target};
use crate::tir::tir_nodes::TIRLit;
use crate::tir::ttir_nodes::{TTIRProgram, TyId};

use super::facts::*;
use super::Stats;

// How deep a group is followed before what is left is packed as it stands.
const WIDE_DEEP: usize = 4;

// What a lane of a group is made of.
struct Group {
    ty:   TyId,
    // The values it stands for, one per lane. What the cost of leaving them
    // alone is worked out from.
    vals: Vec<SIRValueId>,
    plan: Plan,
}

enum Plan {
    // The same value in every lane.
    Splat(SIRValueId),
    // Neighbouring elements of one aggregate, read at once.
    Run { of: SIRValueId, at: u64 },
    // The same instruction in every lane, over groups.
    Same { kind: SIRInstKind, args: Vec<Group> },
    // And anything else: the values as they are, side by side.
    Gather(Vec<SIRValueId>),
}

pub(super) fn vectorize(
    body: &mut SIRBody,
    ttir: &TTIRProgram,
    target: Target,
    stats: &mut Stats,
) -> bool {
    if target.bytes == 0 {
        return false;
    }
    let live = body.live();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let alias = Alias::of(body);
        let held = made(body);
        let counted = counts(body);
        for run in runs(body, ttir, &alias, &held, target, at) {
            let vals: Vec<SIRValueId> = run
                .at
                .iter()
                .map(|&index| match body.blocks[at].insts[index].kind {
                    SIRInstKind::Store { value, .. } => value,
                    _ => unreachable!("a run is a run of stores"),
                })
                .collect();
            let group = grouped(body, ttir, &alias, &held, &vals, 0);
            if !target_does(ttir, target, &group, run.lanes) {
                continue;
            }
            if !pays(target, &counted, &group, run.lanes) {
                continue;
            }
            // One at a time: widening a run rewrites the block's list, and the
            // next is looked for in what that left.
            widen(body, at, &run, &group, stats);
            return true;
        }
    }
    false
}

// Where each of a run's stores stands, in the order they were written.
struct Run {
    // The instruction each store is, by its place in the block.
    at:    Vec<usize>,
    // And the address each writes to, in the same order.
    addrs: Vec<SIRValueId>,
    // How many of them there are, which is what the target said fits.
    lanes: usize,
}

// Every run of stores in the block that writes neighbouring elements of one
// thing, as many of them at a time as the machine holds, with nothing between
// them that may read or write where they do.
fn runs(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    held: &[Option<SIRInstKind>],
    target: Target,
    at: SIRBlockId,
) -> Vec<Run> {
    // Every store in the block that writes an element whose number is known.
    let mut writes: Vec<(usize, SIRValueId, i64, SIRValueId, SIRValueId)> = Vec::new();
    for (index, inst) in body.blocks[at].insts.iter().enumerate() {
        let SIRInstKind::Store { to, value } = inst.kind else { continue };
        let Some(Some(SIRInstKind::IndexAddr { base, index: which })) = held.get(to) else {
            continue;
        };
        let Some(TIRLit::Int(n)) = lit_of(held, *which) else { continue };
        writes.push((index, *base, *n, to, value));
    }

    let mut out = Vec::new();
    for start in 0..writes.len() {
        // How many fit is a question about what is being written, so it is
        // asked of the first of them and the rest are held to that.
        let Some(width) = target::size(ttir, body.values[writes[start].4].ty) else { continue };
        // As many as the register holds, and then half as many, and so on
        // down to two. A register filled halfway is still a register: what a
        // machine holds is a ceiling and not a quota, and refusing to write
        // four of something out on a machine that could have held eight would
        // leave every short array alone on the widest machines.
        let mut lanes = target.lanes(width);
        while lanes >= 2 {
            if start + lanes <= writes.len() {
                let group = &writes[start..start + lanes];
                let neighbours = (1..lanes).all(|j| {
                    group[j].2 == group[0].2 + j as i64 && alias.must(group[j].1, group[0].1)
                });
                let addrs: Vec<SIRValueId> = group.iter().map(|w| w.3).collect();
                let places: Vec<usize> = group.iter().map(|w| w.0).collect();
                if neighbours && settled(body, ttir, alias, at, &places, &addrs) {
                    out.push(Run { at: places, addrs, lanes });
                    break;
                }
            }
            lanes /= 2;
        }
    }
    out
}

// Whether the machine has an instruction for every step of the plan.
//
// Without this a group of four field reads would be written out as a "wide
// field read", which is not a thing: `grouped` will happily find that four
// instructions are the same instruction, and being the same is not the same as
// being one the machine can do at once.
fn target_does(ttir: &TTIRProgram, target: Target, group: &Group, lanes: usize) -> bool {
    let Some(p) = target::prim(ttir, group.ty) else { return false };
    if target::size_of(p).is_none() {
        return false;
    }
    match &group.plan {
        // Moving values about, which every machine with vectors can do.
        Plan::Splat(_) | Plan::Gather(_) | Plan::Run { .. } => true,
        Plan::Same { kind, args } => {
            target.does(kind, p, lanes)
                && args.iter().all(|arg| target_does(ttir, target, arg, lanes))
        }
    }
}

// Whether the wide instructions cost less than the narrow ones they stand for.
//
// The narrow side counts only what would actually go. An instruction whose
// value something outside the group also reads is an instruction that stays
// where it is however the group is written, so counting it as saved would be
// counting a saving that does not happen -- which is the way a cost model
// talks itself into a rewrite that makes things worse.
//
// The wide side counts what has to be built. A group whose operands were
// already lined up -- neighbouring elements, or one value in every lane --
// costs one instruction to read; a group whose operands have to be fetched one
// at a time costs an insert each, and that is usually the whole difference
// between a group worth making and one that is not.
fn pays(target: Target, counted: &[usize], group: &Group, lanes: usize) -> bool {
    // The stores themselves: `lanes` of them become one.
    let (narrow, wide) = costs(target, counted, group, lanes);
    narrow + lanes > wide + 1
}

fn costs(target: Target, counted: &[usize], group: &Group, lanes: usize) -> (usize, usize) {
    // How many of the lanes are read by nothing but this group, and so go.
    let goes = || group.vals.iter().filter(|&&v| counted.get(v) == Some(&1)).count();
    match &group.plan {
        // Already worked out, and staying: nothing is saved, and putting them
        // side by side costs an insert each.
        Plan::Gather(_) => (0, lanes * target.insert),
        // One value in every lane is one broadcast.
        Plan::Splat(_) => (0, 1),
        Plan::Run { .. } => (goes(), 1),
        Plan::Same { kind, args } => {
            let mut narrow = goes();
            let mut wide = target.cost(kind);
            for arg in args {
                let (n, w) = costs(target, counted, arg, lanes);
                narrow += n;
                wide += w;
            }
            (narrow, wide)
        }
    }
}

// How many times each value is read, which is what says whether taking one
// instruction out would take it out.
fn counts(body: &SIRBody) -> Vec<usize> {
    let mut out = vec![0; body.values.len()];
    let count = |value: SIRValueId, out: &mut Vec<usize>| {
        if value < out.len() {
            out[value] += 1;
        }
    };
    for block in &body.blocks {
        for phi in &block.phis {
            for (_, value) in &phi.edges {
                count(*value, &mut out);
            }
        }
        for inst in &block.insts {
            for value in SIRBody::uses(&inst.kind) {
                count(value, &mut out);
            }
        }
        match &block.term {
            SIRTerm::Branch { cond, .. } => count(*cond, &mut out),
            SIRTerm::Return(Some(value)) => count(*value, &mut out),
            _ => {}
        }
    }
    out
}

// Whether the stores may be brought together at the last of them: nothing
// standing between may read or write where any of them writes.
fn settled(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    at: SIRBlockId,
    places: &[usize],
    addrs: &[SIRValueId],
) -> bool {
    let held = made(body);
    let first = places[0];
    let last = places[places.len() - 1];
    for index in first..=last {
        if places.contains(&index) {
            continue;
        }
        let kind = &body.blocks[at].insts[index].kind;
        let touches = match kind {
            SIRInstKind::Load { from } => addrs.iter().any(|&a| alias.may(a, *from)),
            // The read that names no address, which `other` below would have
            // asked `effects` about -- and `effects` answers whether it may
            // *trap*, not whether it reads any of these. An in-range one
            // answers false there, so a read standing between the loads being
            // widened looked like a value being worked out.
            SIRInstKind::Index { .. } => match body.blocks[at].insts[index].def {
                Some(def) => addrs.iter().any(|&a| alias.may(a, def)),
                None => false,
            },
            // Naming a global reads it, which is a read like the one above and
            // is not written as a `Load`. Nothing has been shown to reach here
            // -- what is widened is a run of loads and stores, and a global
            // read among them would have to be one of the addresses -- but the
            // omission is the same one that cost `overwritten` every store to
            // a global but the last, and answering it costs a comparison.
            SIRInstKind::Item(item) => addrs
                .iter()
                .any(|&a| alias.place(a).map(|p| p.base) == Some(Base::Item(*item))),
            SIRInstKind::Store { to, .. } | SIRInstKind::VecStore { to, .. } => {
                addrs.iter().any(|&a| alias.may(a, *to))
            }
            SIRInstKind::DropSlot(slot) => addrs
                .iter()
                .any(|&a| alias.place(a).map(|p| p.base) == Some(Base::Slot(*slot))),
            SIRInstKind::Call { .. } | SIRInstKind::Method { .. } | SIRInstKind::Drop(_) => {
                !addrs.iter().all(|&a| alias.own(a))
            }
            // Anything else works a value out, and a value is not somewhere
            // anything can have been written.
            other => effects(&body.values, ttir, &held, other),
        };
        if touches {
            return false;
        }
    }
    true
}

// What the lanes of a group are, worked out from the values that fill them.
fn grouped(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    held: &[Option<SIRInstKind>],
    vals: &[SIRValueId],
    depth: usize,
) -> Group {
    let ty = body.values[vals[0]].ty;
    let gather = || Group { ty, vals: vals.to_vec(), plan: Plan::Gather(vals.to_vec()) };

    // The same value in every lane, which is how a thing that does not vary
    // with the turn joins a group of things that do.
    if vals.iter().all(|&v| v == vals[0]) {
        return Group { ty, vals: vals.to_vec(), plan: Plan::Splat(vals[0]) };
    }
    if depth >= WIDE_DEEP {
        return gather();
    }

    // Neighbouring elements of one aggregate.
    let elems: Option<Vec<(SIRValueId, i64)>> = vals
        .iter()
        .map(|&v| match held.get(v) {
            Some(Some(kind @ SIRInstKind::Index { base, index })) => {
                match (lit_of(held, *index), effects(&body.values, ttir, held, kind)) {
                    (Some(TIRLit::Int(n)), false) => Some((*base, *n)),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect();
    if let Some(elems) = elems {
        let run = (1..elems.len()).all(|j| {
            elems[j].1 == elems[0].1 + j as i64 && alias.must(elems[j].0, elems[0].0)
        });
        if run {
            if let Ok(first) = u64::try_from(elems[0].1) {
                return Group {
                    ty,
                    vals: vals.to_vec(),
                    plan: Plan::Run { of: elems[0].0, at: first },
                };
            }
        }
    }

    // Or the same instruction in every lane. `shape` is what "the same" means:
    // the instruction with its operands blanked, so that two adds are one
    // shape and an add and a subtract are two.
    let kinds: Option<Vec<SIRInstKind>> = vals
        .iter()
        .map(|&v| match held.get(v) {
            Some(Some(kind)) if !effects(&body.values, ttir, held, kind) => Some(kind.clone()),
            _ => None,
        })
        .collect();
    let Some(kinds) = kinds else { return gather() };
    let first = shape(&kinds[0]);
    if !kinds.iter().all(|kind| shape(kind) == first) {
        return gather();
    }
    let width = SIRBody::uses(&kinds[0]).len();
    // Nothing to group under it, and nothing above it either: an instruction
    // with no operands is the same instruction in every lane only if it is
    // literally the same value, which the splat above has already answered.
    if width == 0 {
        return gather();
    }
    let mut args = Vec::new();
    for arg in 0..width {
        let lane: Vec<SIRValueId> = kinds.iter().map(|kind| SIRBody::uses(kind)[arg]).collect();
        args.push(grouped(body, ttir, alias, held, &lane, depth + 1));
    }
    Group { ty, vals: vals.to_vec(), plan: Plan::Same { kind: kinds[0].clone(), args } }
}

// An instruction with its operands blanked, which is what makes two of them
// the same instruction for this purpose.
fn shape(kind: &SIRInstKind) -> SIRInstKind {
    let mut out = kind.clone();
    for value in SIRBody::uses_mut(&mut out) {
        *value = 0;
    }
    out
}

// The group written out, and the run of stores replaced by the one that writes
// all of it.
fn widen(body: &mut SIRBody, at: SIRBlockId, run: &Run, group: &Group, stats: &mut Stats) {
    let last = run.at[run.at.len() - 1];
    let (line, col) = (body.blocks[at].insts[last].line, body.blocks[at].insts[last].col);
    let mut out = Vec::new();
    let value = write(body, group, run.lanes, line, col, &mut out);
    stats.widened += 1;

    // The scalar stores go and the vector one stands where the last of them
    // did -- which is below every value any of them wrote, so nothing it reads
    // is read above where it is made.
    let mut insts = Vec::with_capacity(body.blocks[at].insts.len() + out.len());
    for (index, inst) in body.blocks[at].insts.iter().enumerate() {
        if index == last {
            insts.append(&mut out);
            insts.push(SIRInst {
                def:       None,
                kind:      SIRInstKind::VecStore { to: run.addrs[0], value },
                is_unsafe: inst.is_unsafe,
                line,
                col,
            });
        } else if !run.at.contains(&index) {
            insts.push(inst.clone());
        }
    }
    body.blocks[at].insts = insts;
}

// One group written out, operands first, and the value it comes to.
fn write(
    body: &mut SIRBody,
    group: &Group,
    lanes: usize,
    line: usize,
    col: usize,
    out: &mut Vec<SIRInst>,
) -> SIRValueId {
    let kind = match &group.plan {
        Plan::Splat(value) => SIRInstKind::Pack(vec![*value; lanes]),
        Plan::Gather(values) => SIRInstKind::Pack(values.clone()),
        Plan::Run { of, at } => SIRInstKind::Lanes { of: *of, at: *at, lanes },
        Plan::Same { kind, args } => {
            let held: Vec<SIRValueId> =
                args.iter().map(|arg| write(body, arg, lanes, line, col, out)).collect();
            let mut kind = kind.clone();
            for (slot, value) in SIRBody::uses_mut(&mut kind).into_iter().zip(held) {
                *slot = value;
            }
            kind
        }
    };
    body.values.push(SIRValue { ty: group.ty, lanes, of: None, line, col });
    let def = body.values.len() - 1;
    out.push(SIRInst { def: Some(def), kind, is_unsafe: false, line, col });
    def
}
