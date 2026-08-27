// The graph: a branch with one edge, a block folded into the one above it,
// and everything nothing reads.

use super::*;

// A condition that is already known picks its arm, the other arm goes, and the
// phi that stood where they met has one answer left.
#[test]
fn a_branch_on_a_literal_takes_its_arm_and_leaves_no_phi() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let (at, then, els, join) = (f.block(), f.block(), f.block(), f.block());
    let cond = f.boolean(true);
    f.term(at, GIRTerm::Branch { cond, then, els });
    let one = f.int(1);
    f.set(then, x, one);
    f.term(then, GIRTerm::Goto(join));
    let two = f.int(2);
    f.set(els, x, two);
    f.term(els, GIRTerm::Goto(join));
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(join, hands);
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert!(phis(body).is_empty(), "one arm is left: {:#?}", phis(body));
    assert_eq!(literal(body, handed(body)), TIRLit::Int(1));
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(2)))),
        0,
        "the arm that is not taken goes with it"
    );
    assert_eq!(blocks(body), 1, "and what is left is one straight line");
}

// Blocks joined by nothing but an edge are one block, which is what leaves
// `share` and `fold` able to see one instruction beside another.
#[test]
fn a_block_with_one_way_in_is_folded_into_the_block_above_it() {
    let mut f = Fixture::new();
    let (at, next) = (f.block(), f.block());
    let call = f.call();
    f.eval(at, call);
    f.term(at, GIRTerm::Goto(next));
    let call = f.call();
    f.eval(next, call);
    f.term(next, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(blocks(body), 1, "{:#?}", body.blocks);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Call { .. })), 2, "both calls stay");
}

// Worked out and never asked for.
#[test]
fn a_value_nothing_reads_is_not_worked_out() {
    let mut f = Fixture::new();
    let a = f.param("a", f.int);
    let at = f.block();
    let (x, one) = (f.read(a), f.int(1));
    let sum = f.add(x, one);
    f.eval(at, sum);
    let call = f.call();
    f.eval(at, call);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Binary { .. })), 0);
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Call { .. })),
        1,
        "a call is what the program is for, read or not"
    );
    assert!(stats.dead > 0, "{:#?}", stats);
}

// A release is not a value either, and goes only where the value it releases
// was never made.
#[test]
fn a_release_is_kept_though_nothing_reads_it() {
    let mut f = Fixture::new();
    let x = f.dropping("x", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, x, one);
    f.release(at, x);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Drop(_) | SIRInstKind::DropSlot(_))),
        1,
        "{:#?}",
        kinds(body)
    );
}
