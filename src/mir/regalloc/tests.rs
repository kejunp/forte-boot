// Where the registers go, and the two rules that make an answer right rather
// than merely an answer.
//
// A register allocator is easy to test badly. "Everything got a register" says
// nothing -- handing every value the same one would pass it. The properties
// that matter are both about *pairs*: two values wanted at the same time are
// never in one register, and a value wanted after a call is never in a register
// the call may have written. Both are checked below by walking the listing and
// asking what is live where, rather than by reading the allocator's own answer
// back to itself.

use super::super::fixture::*;
use super::super::linear::{linearise, Line, Linear};
use super::super::machine::{self, Class, Reg};
use super::super::mir_nodes::*;
use super::*;

fn run(body: &MIRBody) -> (Linear, Allocation) {
    let mut held = linearise(body);
    let out = allocate(&mut held, machine());
    (held, out)
}

// A machine with almost nothing to hand out, for making it run short on
// purpose. Two integer registers, one of which a call keeps.
fn cramped() -> Machine {
    const INTS: &[Reg] = &[
        Reg { name: "a", class: Class::Int },
        Reg { name: "b", class: Class::Int },
    ];
    const SAVED: &[Reg] = &[Reg { name: "b", class: Class::Int }];
    const GONE: &[Reg] = &[Reg { name: "a", class: Class::Int }];
    Machine {
        ints: INTS,
        floats: &[],
        args: &[],
        fargs: &[],
        saved: SAVED,
        clobbered: GONE,
        ..machine::X86_64
    }
}

// Which registers are live at each line: named at or before it, and again at or
// after it.
fn live_at(held: &Linear) -> Vec<Vec<MIRRegId>> {
    let mut low: Vec<Option<usize>> = vec![None; held.regs.len()];
    let mut high: Vec<Option<usize>> = vec![None; held.regs.len()];
    let mark = |reg: MIRRegId, at: usize, low: &mut Vec<Option<usize>>, high: &mut Vec<Option<usize>>| {
        if reg >= low.len() {
            return;
        }
        low[reg] = Some(low[reg].map_or(at, |h: usize| h.min(at)));
        high[reg] = Some(high[reg].map_or(at, |h: usize| h.max(at)));
    };
    for &reg in &held.params {
        mark(reg, 0, &mut low, &mut high);
    }
    for (at, line) in held.lines.iter().enumerate() {
        match line {
            Line::Inst(inst) => {
                for reg in uses(&inst.kind) {
                    mark(reg, at, &mut low, &mut high);
                }
                if let Some(def) = inst.def {
                    mark(def, at, &mut low, &mut high);
                }
            }
            Line::Term(term) => {
                for reg in term.uses() {
                    mark(reg, at, &mut low, &mut high);
                }
            }
            Line::Label(_) => {}
        }
    }
    (0..held.lines.len())
        .map(|at| {
            (0..held.regs.len())
                .filter(|&reg| match (low[reg], high[reg]) {
                    (Some(from), Some(to)) => from <= at && at <= to,
                    _ => false,
                })
                .collect()
        })
        .collect()
}

// ---- The rule that makes it an allocation ----------------------------------

// Two values wanted at the same time are two registers. This is the whole of
// what an allocator has to be right about, and it is the one thing that cannot
// be seen by reading a single answer.
#[test]
fn nothing_live_at_once_shares_a_register() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let (held, out) = run(body_of(&p, "1f"));
    for (at, live) in live_at(&held).into_iter().enumerate() {
        for (i, &one) in live.iter().enumerate() {
            for &other in &live[i + 1..] {
                if let (Where::In(a), Where::In(b)) = (out.of(one), out.of(other)) {
                    assert_ne!(
                        a.name, b.name,
                        "%{} and %{} are both live at line {} and both in {}",
                        one, other, at, a.name
                    );
                }
            }
        }
    }
}

// The same, on a machine with two registers and more values than that -- so the
// allocator has to spill rather than merely have enough.
#[test]
fn nothing_live_at_once_shares_a_register_when_there_are_not_enough() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let mut held = linearise(body_of(&p, "1f"));
    let out = allocate(&mut held, cramped());
    assert!(out.spills > 0, "it should have run short: {:#?}", out);
    for (at, live) in live_at(&held).into_iter().enumerate() {
        for (i, &one) in live.iter().enumerate() {
            for &other in &live[i + 1..] {
                if let (Where::In(a), Where::In(b)) = (out.of(one), out.of(other)) {
                    assert_ne!(a.name, b.name, "%{} and %{} share {} at line {}", one, other, a.name, at);
                }
            }
        }
    }
}

// ---- The rule about calls --------------------------------------------------

// A value still wanted after a call cannot be in a register the call may
// write: it would be gone when the call came back, and nothing would say so.
#[test]
fn a_value_live_across_a_call_is_kept_somewhere_a_call_keeps() {
    let p = lowered(
        "fn g(x: i32): i32 { x }\n\
         fn f(a: i32, b: i32): i32 { g(a) + b }\n",
    );
    let (held, out) = run(body_of(&p, "1f"));
    let calls: Vec<usize> = held
        .lines
        .iter()
        .enumerate()
        .filter(|(_, line)| {
            matches!(line, Line::Inst(MIRInst { kind: MIRInstKind::Call { .. }, .. }))
        })
        .map(|(at, _)| at)
        .collect();
    assert!(!calls.is_empty(), "there should be a call");

    let live = live_at(&held);
    for &call in &calls {
        // Live before the call and still live after it.
        for &reg in &live[call] {
            let after = live.get(call + 1).map(|held| held.contains(&reg)).unwrap_or(false);
            let before = call > 0 && live[call - 1].contains(&reg);
            if !(before && after) {
                continue;
            }
            if let Where::In(held) = out.of(reg) {
                assert!(
                    machine().keeps(held),
                    "%{} is live across the call at line {} and is in {}, which a call may write",
                    reg,
                    call,
                    held.name
                );
            }
        }
    }
}

// ---- Spilling --------------------------------------------------------------

// Everything spilled gets room of its own, and the room says what it is for.
#[test]
fn everything_spilled_gets_a_slot_marked_as_one() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let mut held = linearise(body_of(&p, "1f"));
    let before = held.frame.len();
    let out = allocate(&mut held, cramped());
    assert!(out.spills > 0);
    assert_eq!(held.frame.len(), before + out.spills, "one slot each");
    assert_eq!(
        held.frame.iter().filter(|slot| slot.spill).count(),
        out.spills,
        "and each of them marked"
    );
}

// Two values are never given the same room, which would be the same mistake as
// sharing a register and is easier to make.
#[test]
fn no_two_spills_share_a_slot() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let mut held = linearise(body_of(&p, "1f"));
    let out = allocate(&mut held, cramped());
    let mut rooms: Vec<MIRFrameId> = out
        .at
        .iter()
        .filter_map(|held| match held {
            Where::Spilled(slot) => Some(*slot),
            _ => None,
        })
        .collect();
    let count = rooms.len();
    rooms.sort_unstable();
    rooms.dedup();
    assert_eq!(rooms.len(), count, "two values in one slot");
}

// A body that fits does not spill at all. That it *stops* spilling is as much
// of the rule as that it starts.
#[test]
fn a_body_that_fits_spills_nothing() {
    let p = lowered("fn f(a: i32, b: i32): i32 { a + b }\n");
    let (_, out) = run(body_of(&p, "1f"));
    assert_eq!(out.spills, 0, "{:#?}", out);
}

// ---- What each answer is ---------------------------------------------------

#[test]
fn every_register_that_is_used_gets_an_answer() {
    let p = lowered("fn f(a: i32, b: i32): i32 { a + b }\n");
    let (held, out) = run(body_of(&p, "1f"));
    for line in &held.lines {
        let reads = match line {
            Line::Inst(inst) => uses(&inst.kind),
            Line::Term(term) => term.uses(),
            Line::Label(_) => Vec::new(),
        };
        for reg in reads {
            assert_ne!(out.of(reg), Where::Nowhere, "%{} is read and went nowhere", reg);
        }
    }
}

// A register is only ever given one out of its own file: an integer in an
// integer register, a float in a float one.
#[test]
fn a_register_is_given_one_of_its_own_class() {
    let p = lowered("fn f(a: f64, b: f64, c: i32): f64 { let _ = c\n a + b }\n");
    let (held, out) = run(body_of(&p, "1f"));
    for (reg, held) in held.regs.iter().enumerate() {
        if let Where::In(given) = out.of(reg) {
            assert_eq!(given.class, held.class, "%{} is in {}", reg, given.name);
        }
    }
}

// The frame register holds the frame for the whole of a body, so an allocator
// that could hand it out would give away what every spill is written against.
#[test]
fn the_frame_register_is_never_given_to_anything() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let (_, out) = run(body_of(&p, "1f"));
    for held in &out.at {
        if let Where::In(reg) = held {
            assert_ne!(reg.name, machine().frame.name);
        }
    }
}

// How many were wanted at once, which is what says whether a machine with more
// registers would have helped. It is at least one wherever anything is live.
#[test]
fn the_worst_point_is_counted() {
    let p = lowered("fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n");
    let (_, out) = run(body_of(&p, "1f"));
    assert!(out.most >= 2, "{:#?}", out);
}

// And round a loop, which is where the linear reading of a span is not the
// truth. A value set before the loop and read at the *top* of the body is
// wanted again on the next turn, so it is live over everything below that read
// -- including a call. Reading the span as the lowest and the highest mention
// stops it at the read, so it comes out not crossing the call and is given a
// caller-saved register.
//
// That is not a shape it comes out in by accident: the multiplier of `i * 3`
// below went into `rcx`, and the callee used `rcx` as its own scratch, so the
// multiplier was a different number every turn and the loop wrote `i * (i - 1)`.
#[test]
fn a_value_live_round_a_loop_is_kept_across_a_call_inside_it() {
    let p = lowered(
        "fn g(x: i64): i64 { x }\n\
         fn f(n: i64): i64 {\n\
         \x20   let step = 3\n    var t = 0\n    var i = 0\n\
         \x20   while i < n {\n        t = t + g(i * step)\n        i = i + 1\n    }\n\
         \x20   t\n}\n",
    );
    let (held, out) = run(body_of(&p, "1f"));

    // The arc a backward jump closes over, which is the loop.
    let mut at: Vec<(MIRBlockId, usize)> = Vec::new();
    for (line, one) in held.lines.iter().enumerate() {
        if let Line::Label(block) = one {
            at.push((*block, line));
        }
    }
    let mut arcs: Vec<(usize, usize)> = Vec::new();
    for (line, one) in held.lines.iter().enumerate() {
        let Line::Term(term) = one else { continue };
        for to in term.targets() {
            match at.iter().find(|(block, _)| *block == to) {
                Some((_, back)) if *back <= line => arcs.push((*back, line)),
                _ => {}
            }
        }
    }
    assert!(!arcs.is_empty(), "there should be a loop: {:#?}", held.lines);

    let live = live_at(&held);
    for (from, to) in arcs {
        let calls: Vec<usize> = (from..=to)
            .filter(|&line| {
                matches!(
                    held.lines[line],
                    Line::Inst(MIRInst { kind: MIRInstKind::Call { .. }, .. })
                )
            })
            .collect();
        if calls.is_empty() {
            continue;
        }
        // Named inside the loop and also outside it, which is what being live
        // round it means whatever the linear order says.
        for reg in 0..held.regs.len() {
            let inside = (from..=to).any(|line| live[line].contains(&reg));
            let outside = (0..held.lines.len())
                .filter(|line| *line < from || *line > to)
                .any(|line| live[line].contains(&reg));
            if !(inside && outside) {
                continue;
            }
            if let Where::In(one) = out.of(reg) {
                assert!(
                    machine().keeps(one),
                    "%{} is live round a loop with a call in it and is in {}",
                    reg,
                    one.name
                );
            }
        }
    }
}
