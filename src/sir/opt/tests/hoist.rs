// What leaves a loop because it does not vary with the turn, and what stays
// because it does -- including the load, whose answer is the alias analysis's.

use super::*;

// A sum of two parameters is the same sum every turn, so it is worked out
// before the loop rather than in it.
#[test]
fn a_sum_of_two_things_from_outside_is_worked_out_before_the_loop() {
    let mut f = Fixture::new();
    let a = f.param("a", f.int);
    let b = f.param("b", f.int);
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let cond = f.read(c);
    f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
    let (x, y) = (f.read(a), f.read(b));
    let sum = f.add(x, y);
    let hands = f.hands(sum);
    f.eval(inner, hands);
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert!(stats.hoisted > 0, "{:#?}", stats);
    assert!(!loops(body).is_empty(), "the loop is still a loop");
    assert!(
        !inside_a_loop(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        "the sum stands outside: {:#?}",
        kinds(body)
    );
    assert!(
        inside_a_loop(body, |k| matches!(k, SIRInstKind::Call { .. })),
        "and the call it was handed to does not"
    );
}

// What the loop works out itself stays where it is. The sum reads what the
// turn before it made, so there is no turn it is the same on.
#[test]
fn a_sum_of_what_the_loop_makes_stays_in_it() {
    let mut f = Fixture::new();
    let n = f.local("n", f.int);
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    let zero = f.int(0);
    f.set(before, n, zero);
    f.term(before, GIRTerm::Goto(head));
    let cond = f.read(c);
    f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
    let (read, one) = (f.read(n), f.int(1));
    let sum = f.add(read, one);
    f.set(inner, n, sum);
    let read = f.read(n);
    let hands = f.hands(read);
    f.eval(inner, hands);
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let (p, _) = worked(f);
    let body = &p.bodies[0];

    assert!(
        inside_a_loop(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        "the sum is the turn's own: {:#?}",
        kinds(body)
    );
}

// A load may find something different once something has written, so whether
// it may be lifted out of a loop is a question about what the loop writes and
// where -- which is what `sir::alias` is for.
//
// The name is written to through a field before the loop, which keeps it in
// the frame without letting the address out: `sir::promote` gives up on it and
// the analysis does not. That is the shape the whole thing was built for, and
// it is why the call inside the loop does not settle the question on its own.
#[test]
fn a_load_is_lifted_only_out_of_a_loop_that_writes_where_it_reads() {
    let build = |writes: bool| {
        let mut f = Fixture::new();
        let xs = f.local("xs", f.int);
        let c = f.param("c", f.bool);
        let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
        let ty = f.int;
        let base = f.read(xs);
        let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
        let one = f.int(1);
        f.store(before, field, TIRAssignOp::Set, one);
        f.term(before, GIRTerm::Goto(head));
        let cond = f.read(c);
        f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
        let read = f.read(xs);
        let hands = f.hands(read);
        f.eval(inner, hands);
        if writes {
            let base = f.read(xs);
            let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
            let two = f.int(2);
            f.store(inner, field, TIRAssignOp::Set, two);
        }
        f.term(inner, GIRTerm::Goto(head));
        f.term(exit, GIRTerm::Return(None));
        f.body(before);
        worked(f).0
    };

    let quiet = build(false);
    assert!(
        !inside_a_loop(&quiet.bodies[0], |k| matches!(k, SIRInstKind::Load { .. })),
        "the loop calls out, but not to anywhere that could reach this name: {:#?}",
        kinds(&quiet.bodies[0])
    );

    let noisy = build(true);
    assert!(
        inside_a_loop(&noisy.bodies[0], |k| matches!(k, SIRInstKind::Load { .. })),
        "a field of it is written every turn: {:#?}",
        kinds(&noisy.bodies[0])
    );
}
