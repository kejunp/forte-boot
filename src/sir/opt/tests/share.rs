// Two instructions that make one value, and the two that may not.

use super::*;

// The same operator over the same values, the second standing under the first.
#[test]
fn an_operator_worked_out_twice_is_worked_out_once() {
    let mut f = Fixture::new();
    let a = f.param("a", f.int);
    let b = f.param("b", f.int);
    let at = f.block();
    let (x, y) = (f.read(a), f.read(b));
    let first = f.add(x, y);
    let hands = f.hands(first);
    f.eval(at, hands);
    let (x, y) = (f.read(a), f.read(b));
    let second = f.add(x, y);
    let hands = f.hands(second);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        1,
        "{:#?}",
        kinds(body)
    );
    assert!(stats.shared > 0, "{:#?}", stats);
}

// Only where the first stands before the second on every path. Two arms of a
// branch reach each other on no path at all, so neither may be the other.
#[test]
fn one_arm_of_a_branch_does_not_share_with_the_other() {
    let mut f = Fixture::new();
    let a = f.param("a", f.int);
    let (at, then, els, join) = (f.block(), f.block(), f.block(), f.block());
    let cond = f.read(a);
    let cond = {
        let ty = f.bool;
        let zero = f.int(0);
        f.expr(GIRExprKind::Binary { op: TIRBinOp::Lt, lhs: cond, rhs: zero }, ty)
    };
    f.term(at, GIRTerm::Branch { cond, then, els });
    for arm in [then, els] {
        let (x, one) = (f.read(a), f.int(1));
        let sum = f.add(x, one);
        let hands = f.hands(sum);
        f.eval(arm, hands);
        f.term(arm, GIRTerm::Goto(join));
    }
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Binary { op: TIRBinOp::Add, .. })),
        2,
        "neither arm stands before the other: {:#?}",
        kinds(body)
    );
}


// ---- What a global is, which is a place and not a value ---------------------

// Two reads of a global with a store between them are two answers, and sharing
// them is reading the old one twice.
//
// `known` had `Item` in its list from the beginning, beside the literals and
// the addresses -- true of a fn and of a `const`, and false of a global, which
// is the one item that is a *place*. Nothing caught it because until there was
// a data segment to put a global in, no program holding one ever linked, so
// the pass that would have shown it up could not be run against one.
//
// Written as a source rather than against the fixture because that is what
// makes it a regression: the shape has to arrive here the way a program does.
#[test]
fn two_reads_of_a_global_across_a_store_are_not_one_read() {
    let (p, _) = compiled(
        "var counter: i64 = 0\n\
         fn bump(): i64 {\n\
             counter = counter + 1\n\
             counter\n\
         }\n",
    );
    let body = p.bodies.iter().find(|b| !b.blocks.is_empty()).expect("a body");
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Item(_))),
        2,
        "the read after the store was shared with the one before it:\n{:#?}",
        kinds(body)
    );
}

// And the other half, so the fix is not simply "never share an item": a `const`
// is not a place, and two reads of one are one read.
#[test]
fn two_reads_of_a_const_are_one_read() {
    let (p, _) = compiled(
        "const N: i64 = 40\n\
         fn twice(): i64 {\n\
             N + N\n\
         }\n",
    );
    let body = p.bodies.iter().find(|b| !b.blocks.is_empty()).expect("a body");
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Item(_))) == 0,
        "a const should have folded before this pass:\n{:#?}",
        kinds(body)
    );
}
