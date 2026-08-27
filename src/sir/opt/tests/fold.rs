// Operators over what is already worked out, and the operators that are
// left alone: a sum that will not fit the type it was going to be held in,
// and a division by a zero nobody may divide by.

use super::*;

// The operands are both worked out, so the operator is too.
#[test]
fn an_operator_over_two_literals_is_a_literal() {
    let mut f = Fixture::new();
    let at = f.block();
    let (one, two) = (f.int(1), f.int(2));
    let sum = f.add(one, two);
    let hands = f.hands(sum);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(literal(body, handed(body)), TIRLit::Int(3));
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Binary { .. })), 0);
    assert!(stats.folded > 0, "{:#?}", stats);
}

// And a chain of them, which is the fixpoint doing what it is there for: the
// second operator has a literal operand only once the first has folded.
#[test]
fn a_chain_of_operators_folds_all_the_way_down() {
    let mut f = Fixture::new();
    let at = f.block();
    let (one, two, three) = (f.int(1), f.int(2), f.int(3));
    let sum = f.add(one, two);
    let sum = f.add(sum, three);
    let hands = f.hands(sum);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(literal(body, handed(body)), TIRLit::Int(6));
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Binary { .. })), 0);
}

// Not where the answer will not fit the type the checker gave it. Two i32s
// that sum past an i32 sum to something else at run time, and a literal saying
// otherwise would be this pass writing a different program.
#[test]
fn a_sum_that_leaves_the_type_is_not_folded() {
    let mut f = Fixture::new();
    let at = f.block();
    let (a, b) = (f.int(2_000_000_000), f.int(2_000_000_000));
    let sum = f.add(a, b);
    let hands = f.hands(sum);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        1,
        "the operator stays: {:#?}",
        kinds(body)
    );
}

// Nor a division by zero, which is the program's to do and not this pass's to
// answer on its behalf.
#[test]
fn a_division_by_zero_is_left_where_it_was_written() {
    let mut f = Fixture::new();
    let at = f.block();
    let (one, zero) = (f.int(1), f.int(0));
    let ty = f.int;
    let div = f.expr(GIRExprKind::Binary { op: TIRBinOp::Div, lhs: one, rhs: zero }, ty);
    let hands = f.hands(div);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Binary { .. })), 1);
}

// One side is enough where the other cannot matter. `n + 0` is `n` for every
// `n` there is, so the read stands where the operator did.
#[test]
fn an_identity_needs_only_one_side_to_be_a_literal() {
    let mut f = Fixture::new();
    let n = f.param("n", f.int);
    let at = f.block();
    let read = f.read(n);
    let zero = f.int(0);
    let sum = f.add(read, zero);
    let hands = f.hands(sum);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Binary { .. })), 0);
    assert_eq!(handed(body), body.params[0], "the sum is the parameter itself");
}
