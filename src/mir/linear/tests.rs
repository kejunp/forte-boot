// The graph written out, and the two things that go wrong when it is.
//
// A phi is the whole difficulty. It says which value came along which edge, and
// linearising is exactly the point at which there are no edges left to say it
// about -- so the moves that replace it have to run in the right place and read
// the right things, and both of those have a way of being subtly wrong on a
// body that still looks fine.

use super::super::fixture::*;
use super::super::mir_nodes::*;
use super::*;

fn moves(held: &Linear) -> Vec<(MIRRegId, MIRRegId)> {
    held.lines
        .iter()
        .filter_map(|line| match line {
            Line::Inst(MIRInst { def: Some(def), kind: MIRInstKind::Move(src), .. }) => {
                Some((*def, *src))
            }
            _ => None,
        })
        .collect()
}

fn labels(held: &Linear) -> Vec<MIRBlockId> {
    held.lines
        .iter()
        .filter_map(|line| match line {
            Line::Label(at) => Some(*at),
            _ => None,
        })
        .collect()
}

// ---- What comes out at all -------------------------------------------------

#[test]
fn every_block_the_entry_reaches_is_written_once() {
    let (f, [entry, ..]) = diamond();
    let held = linearise(&f.body(entry));
    let mut seen = labels(&held);
    let count = seen.len();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), count, "a block was written twice");
    assert_eq!(count, 4, "{:#?}", labels(&held));
}

// Nothing here shrinks a block arena, so an arena holds blocks nothing can jump
// to. Writing those out would be writing out code that cannot run.
#[test]
fn a_block_nothing_reaches_is_not_written_out() {
    let mut f = Fixture::new();
    let (at, orphan) = (f.block(), f.block());
    let one = f.int(at, 1);
    f.term(at, MIRTerm::Return(Some(one)));
    f.int(orphan, 2);
    f.term(orphan, MIRTerm::Unreachable);
    let held = linearise(&f.body(at));
    assert_eq!(labels(&held), vec![at], "{:#?}", labels(&held));
}

// The entry has to be first: it is where the body begins, and a listing that
// began somewhere else would be a listing of a different program.
#[test]
fn the_entry_comes_first() {
    let (f, [entry, ..]) = diamond();
    let held = linearise(&f.body(entry));
    assert_eq!(labels(&held).first(), Some(&entry));
}

// A block comes after everything that had to run to reach it, which is what
// reverse postorder means and what makes the listing readable.
#[test]
fn a_block_comes_after_the_ways_into_it() {
    let (f, [entry, then, els, join]) = diamond();
    let held = linearise(&f.body(entry));
    let at = labels(&held);
    let place = |want: MIRBlockId| at.iter().position(|&held| held == want).expect("a block");
    assert!(place(entry) < place(then));
    assert!(place(entry) < place(els));
    assert!(place(then) < place(join));
    assert!(place(els) < place(join));
}

#[test]
fn every_block_ends_in_its_terminator() {
    let (f, [entry, ..]) = diamond();
    let held = linearise(&f.body(entry));
    let mut label = false;
    for line in &held.lines {
        match line {
            Line::Label(_) => label = true,
            Line::Term(_) => label = false,
            Line::Inst(_) => assert!(label, "an instruction outside a block"),
        }
    }
    assert!(!label, "a block with no terminator");
}

// ---- Phis into moves -------------------------------------------------------

#[test]
fn a_phi_is_gone_and_a_move_stands_where_each_edge_was() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (els, b)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let held = linearise(&f.body(entry));

    assert!(
        held.lines.iter().all(|line| !matches!(line, Line::Inst(MIRInst { kind: MIRInstKind::Move(_), def: None, .. }))),
        "a move that makes nothing"
    );
    let held = moves(&held);
    assert!(held.contains(&(joined, a)), "{:?}", held);
    assert!(held.contains(&(joined, b)), "{:?}", held);
}

// The move has to be at the end of the block the value came from, so that the
// register holds what *that* path put there by the time the join is reached.
#[test]
fn the_move_stands_in_the_block_the_value_came_from() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (els, b)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let held = linearise(&f.body(entry));

    // Which block each line is in, by walking the labels.
    let mut at = None;
    let mut said: Vec<(MIRBlockId, MIRRegId)> = Vec::new();
    for line in &held.lines {
        match line {
            Line::Label(block) => at = Some(*block),
            Line::Inst(MIRInst { kind: MIRInstKind::Move(src), .. }) => {
                said.push((at.expect("a block"), *src))
            }
            _ => {}
        }
    }
    assert!(said.contains(&(then, a)), "{:?}", said);
    assert!(said.contains(&(els, b)), "{:?}", said);
}

// All of a block's phis read what stood at the end of the predecessor, all at
// once. `a = b; b = a` written in that order leaves both holding what `b` held,
// so where one phi's register is another's operand every value is copied
// somewhere fresh first.
#[test]
fn two_phis_that_read_each_other_are_not_written_in_sequence() {
    let mut f = Fixture::new();
    let (entry, head, body, out) = (f.block(), f.block(), f.block(), f.block());
    let a0 = f.int(entry, 1);
    let b0 = f.int(entry, 2);
    f.term(entry, MIRTerm::Goto(head));

    // Two phis that swap: each takes what the other held last turn.
    let a = f.phi(head, vec![(entry, a0), (body, 0)]);
    let b = f.phi(head, vec![(entry, b0), (body, 0)]);
    // Now say the back edge crosses them over.
    f.set_phi_edge(head, 0, body, b);
    f.set_phi_edge(head, 1, body, a);
    let cond = f.less(head, a, b);
    f.term(head, MIRTerm::Branch { cond, then: body, els: out });
    f.term(body, MIRTerm::Goto(head));
    f.term(out, MIRTerm::Return(Some(a)));

    let held = linearise(&f.body(entry));

    // Per block, because the moves for one edge stand together at the end of
    // the block that edge leaves. Two groups written one after another are two
    // separate all-at-once writes, and reading across them would say nothing.
    let mut at = None;
    let mut per: Vec<(MIRBlockId, MIRRegId, MIRRegId)> = Vec::new();
    for line in &held.lines {
        match line {
            Line::Label(block) => at = Some(*block),
            Line::Inst(MIRInst { def: Some(def), kind: MIRInstKind::Move(src), .. }) => {
                per.push((at.expect("a block"), *def, *src))
            }
            _ => {}
        }
    }

    // What the moves have to *come to*, which is the property rather than how
    // many of them there are: after the block's moves have run, each phi's
    // register holds what its operand held when the block began. Counting moves
    // or forbidding a register to be read after it is written would both fail
    // on the temporaries, which are exactly the mechanism.
    //
    // So they are run, over a state where every register holds a name for
    // itself, and the answer is read off.
    let back: Vec<_> = per.iter().filter(|(block, ..)| *block == body).collect();
    let mut state: Vec<MIRRegId> = (0..held.regs.len()).collect();
    for (_, def, src) in &back {
        state[*def] = state[*src];
    }
    assert_eq!(state[a], b, "%{} should hold what %{} held: {:?}", a, b, back);
    assert_eq!(state[b], a, "%{} should hold what %{} held: {:?}", b, a, back);
}

// ---- The edges that need a block of their own ------------------------------

// A move at the end of a block runs whenever that block runs. A block with two
// ways out, one of which reaches a phi, would run the move down both -- so the
// edge gets a block of its own with nothing in it but the move and a jump.
#[test]
fn an_edge_out_of_a_branch_into_a_phi_gets_a_block_of_its_own() {
    let mut f = Fixture::new();
    let (entry, join, other) = (f.block(), f.block(), f.block());
    let a = f.int(entry, 1);
    let cond = f.int(entry, 1);
    f.term(entry, MIRTerm::Branch { cond, then: join, els: other });
    // `join` is reached from `entry`, which has two ways out.
    let joined = f.phi(join, vec![(entry, a)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    f.term(other, MIRTerm::Return(None));

    let body = f.body(entry);
    let before = body.blocks.len();
    let held = linearise(&body);
    assert!(labels(&held).len() > before - 1, "{:#?}", labels(&held));

    // The move is not in the entry, because the entry also goes somewhere else.
    let mut at = None;
    for line in &held.lines {
        match line {
            Line::Label(block) => at = Some(*block),
            Line::Inst(MIRInst { kind: MIRInstKind::Move(_), .. }) => {
                assert_ne!(at, Some(entry), "the move runs down both ways out");
            }
            _ => {}
        }
    }
}

// And an edge that is not critical is left alone: a block with one way out has
// nowhere else for the move to leak to.
#[test]
fn an_edge_out_of_a_single_jump_needs_no_block() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (els, b)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let body = f.body(entry);
    let before = body.blocks.len();
    let held = linearise(&body);
    assert_eq!(labels(&held).len(), before, "a block was added and none was needed");
}

// ---- What it is of ---------------------------------------------------------

// Nothing is allocated yet: the registers are the ones the lowering wanted, and
// meeting a machine is `mir::regalloc`'s.
#[test]
fn the_registers_and_the_frame_come_through_unchanged() {
    let mut f = Fixture::new();
    let at = f.block();
    let slot = f.slot("x", 8);
    let held = f.address(at, slot);
    f.term(at, MIRTerm::Return(Some(held)));
    let body = f.body(at);
    let out = linearise(&body);
    assert_eq!(out.frame, body.frame);
    assert_eq!(out.symbol, body.symbol);
    assert_eq!(out.regs.len(), body.regs.len(), "and no register was added");
}

// ---- A real program --------------------------------------------------------

// A loop is where phis actually come from, so one is run all the way through.
#[test]
fn a_loop_from_a_source_linearises() {
    let p = lowered(
        "fn f(n: i32): i32 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n { t = t + i\n i = i + 1 }\n\
         \x20   t\n\
         }\n",
    );
    let held = linearise(body_of(&p, "1f"));
    assert!(!held.lines.is_empty());
    assert!(
        held.lines.iter().any(|line| matches!(line, Line::Term(MIRTerm::Branch { .. }))),
        "a loop with no branch"
    );
    // Every register a line names is one the body has.
    for line in &held.lines {
        let reads = match line {
            Line::Inst(inst) => uses(&inst.kind),
            Line::Term(term) => term.uses(),
            Line::Label(_) => Vec::new(),
        };
        for reg in reads {
            assert!(reg < held.regs.len(), "%{} is not a register of the body", reg);
        }
    }
}
