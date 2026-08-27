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
