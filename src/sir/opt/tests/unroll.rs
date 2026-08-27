// Loops written out as the turns they run, and the loops that are not:
// too many turns, a second way out carrying a value, one turn on its own.

use super::*;

// `for x in 0..3`, which runs three times and takes three values nobody has
// to work out at run time.
fn walking_a_range(from: i64, to: i64) -> Fixture {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let (lo, hi) = (f.int(from), f.int(to));
    let ty = f.null;
    let range = f.expr(
        GIRExprKind::Range {
            op:    crate::tir::tir_nodes::TIRRangeOp::Exclusive,
            start: Some(lo),
            end:   Some(hi),
        },
        ty,
    );
    f.term(head, GIRTerm::ForEach { local: x, iter: range, body: inner, exit });
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(inner, hands);
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);
    f
}

// Three turns, three copies, and the cursor gone: what the loop variable holds
// on each turn is a literal, which is the whole point of doing this here.
#[test]
fn a_walk_over_a_literal_range_becomes_the_turns_it_runs() {
    let (p, stats) = worked(walking_a_range(0, 3));
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert!(loops(body).is_empty(), "there is no loop left: {:#?}", body.blocks);
    let handed: Vec<TIRLit> = all_handed(body).into_iter().map(|v| literal(body, v)).collect();
    assert_eq!(
        handed,
        vec![TIRLit::Int(0), TIRLit::Int(1), TIRLit::Int(2)],
        "{:#?}",
        kinds(body)
    );
    assert_eq!(
        count(body, |k| matches!(
            k,
            SIRInstKind::IterStart
                | SIRInstKind::IterStep { .. }
                | SIRInstKind::IterValid { .. }
                | SIRInstKind::IterElem { .. }
        )),
        0,
        "and no cursor is walked at all: {:#?}",
        kinds(body)
    );
}

// A range with nothing in it runs no turns, so what is left is the way past.
#[test]
fn a_walk_over_an_empty_range_leaves_nothing_of_the_body() {
    let (p, stats) = worked(walking_a_range(3, 3));
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert!(loops(body).is_empty());
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Call { .. })), 0, "{:#?}", kinds(body));
}

// More turns than this pass is willing to write out, so it writes none of
// them: the loop is left exactly as it was.
#[test]
fn a_walk_over_too_many_turns_is_left_as_a_loop() {
    let (p, stats) = worked(walking_a_range(0, 500));
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 0, "{:#?}", stats);
    assert_eq!(loops(body).len(), 1, "still a loop");
}

// An array's length is in its type, so the turns are known even though what
// is in it is not. The tests go and the reads stay.
#[test]
fn a_walk_over_an_array_writes_out_the_reads_it_takes() {
    let mut f = Fixture::new();
    let elem = f.int;
    f.ttir.types.push(Ty::Array { elem, len: 3 });
    let array = f.ttir.types.len() - 1;
    let xs = f.param("xs", array);
    let x = f.local("x", f.int);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let read = f.read(xs);
    f.term(head, GIRTerm::ForEach { local: x, iter: read, body: inner, exit });
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(inner, hands);
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert!(loops(body).is_empty(), "{:#?}", body.blocks);
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::IterElem { .. })),
        3,
        "one read per turn: {:#?}",
        kinds(body)
    );
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::IterValid { .. })),
        0,
        "and no test between them"
    );
}

// A `break` is a second way out, and it is allowed: every copy of the block it
// leaves from goes to the same place, and the phis where it lands are given
// one entry per copy like any other way in.
#[test]
fn a_walk_with_a_second_way_out_is_still_written_out() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let (lo, hi) = (f.int(0), f.int(3));
    let ty = f.null;
    let range = f.expr(
        GIRExprKind::Range {
            op:    crate::tir::tir_nodes::TIRRangeOp::Exclusive,
            start: Some(lo),
            end:   Some(hi),
        },
        ty,
    );
    f.term(head, GIRTerm::ForEach { local: x, iter: range, body: inner, exit });
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(inner, hands);
    let cond = f.read(c);
    let again = f.block();
    f.term(inner, GIRTerm::Branch { cond, then: exit, els: again });
    f.term(again, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert!(loops(body).is_empty(), "{:#?}", body.blocks);
    // Three turns, each of which may leave early, so the three still ask.
    let handed: Vec<TIRLit> = all_handed(body).into_iter().map(|v| literal(body, v)).collect();
    assert_eq!(handed, vec![TIRLit::Int(0), TIRLit::Int(1), TIRLit::Int(2)], "{:#?}", kinds(body));
}

// What is turned down is a value carried out of the loop without a phi to
// carry it: the block it was worked out in stood before the block that read
// it, and after this there would be one such block per turn.
#[test]
fn a_value_carried_out_without_a_phi_stops_the_walk_being_written_out() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let held = f.local("held", f.int);
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let (lo, hi) = (f.int(0), f.int(3));
    let ty = f.null;
    let range = f.expr(
        GIRExprKind::Range {
            op:    crate::tir::tir_nodes::TIRRangeOp::Exclusive,
            start: Some(lo),
            end:   Some(hi),
        },
        ty,
    );
    f.term(head, GIRTerm::ForEach { local: x, iter: range, body: inner, exit });
    // Worked out in the loop, and read in a block only this one reaches -- so
    // nothing joins there and nothing put a phi in it.
    let (read, one) = (f.read(x), f.int(1));
    let sum = f.add(read, one);
    f.set(inner, held, sum);
    let cond = f.read(c);
    let (out, again) = (f.block(), f.block());
    f.term(inner, GIRTerm::Branch { cond, then: out, els: again });
    f.term(again, GIRTerm::Goto(head));
    let read = f.read(held);
    let hands = f.hands(read);
    f.eval(out, hands);
    f.term(out, GIRTerm::Return(None));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 0, "{:#?}", stats);
    assert_eq!(loops(body).len(), 1, "the loop stands: {:#?}", body.blocks);
}

// The same two rewrites, from source, over what the lowering actually makes.
//
// A `for` in this language builds a `Range`, and a `Range` is "syntax for a
// type a library declares" -- so the fixture declares one, exactly as a suite
// would have to.
#[test]
fn a_counted_loop_written_as_source_comes_out_as_its_answer() {
    let (p, stats) = compiled(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn counted(): i32 {\n\
             var total: i32 = 0;\n\
             for i in 0..4 { total = total + i; }\n\
             total\n\
         }\n",
    );

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(loops(body).is_empty(), "the loop is written out: {:#?}", kinds(body));
    // 0 + 1 + 2 + 3, worked out here rather than four times at run time.
    assert_eq!(
        kinds(body),
        vec![SIRInstKind::Literal(TIRLit::Int(6))],
        "{:#?}",
        kinds(body)
    );
}

// And a loop whose turns are not counted, which is where the other rewrite is
// the one that has something to do: `a * b` is the same product every turn.
#[test]
fn a_product_that_does_not_vary_leaves_the_loop_it_was_written_in() {
    let (p, stats) = compiled(
        "fn work(a: i32, b: i32, n: i32): i32 {\n\
             var total: i32 = 0;\n\
             var i: i32 = 0;\n\
             while i < n { total = total + (a * b); i = i + 1; }\n\
             total\n\
         }\n",
    );

    assert_eq!(stats.unrolled, 0, "nothing says how many turns: {:#?}", stats);
    assert!(stats.hoisted > 0, "{:#?}", stats);
    let body = &p.bodies[0];
    assert_eq!(loops(body).len(), 1, "the loop is still a loop");
    assert!(
        !inside_a_loop(body, |k| matches!(k, SIRInstKind::Binary { op: TIRBinOp::Mul, .. })),
        "the product stands before it: {:#?}",
        kinds(body)
    );
    assert!(
        inside_a_loop(body, |k| matches!(k, SIRInstKind::Binary { op: TIRBinOp::Add, .. })),
        "and the sum that reads the turn before it does not"
    );
}

// A branch inside the loop, so each turn is three blocks and the copies carry
// a phi of their own. Nothing is asserted about what it comes to -- `compiled`
// holding every copy to `verify` is the test, and a rewrite that mixed up
// which turn a phi's edge came from is exactly what that catches.
#[test]
fn a_counted_loop_with_a_branch_in_it_is_written_out_soundly() {
    let (p, stats) = compiled(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn branchy(c: bool): i32 {\n\
             var total: i32 = 0;\n\
             for i in 0..3 {\n\
                 if c { total = total + i; } else { total = total + 1; }\n\
             }\n\
             total\n\
         }\n",
    );

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(loops(body).is_empty(), "{:#?}", body.blocks);
    // Three turns, each of which still has to ask `c`.
    assert_eq!(
        body.blocks
            .iter()
            .enumerate()
            .filter(|(at, b)| body.live()[*at] && matches!(b.term, SIRTerm::Branch { .. }))
            .count(),
        3,
        "{:#?}",
        body.blocks
    );
}

// A loop inside a loop, both counted. The inner one is written out first --
// `loops.rs` gives the tighter one first -- and then the outer one is written
// out with the copies of the inner already in it.
#[test]
fn a_counted_loop_inside_a_counted_loop_is_written_out_twice_over() {
    let (p, stats) = compiled(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn nested(): i32 {\n\
             var total: i32 = 0;\n\
             for i in 0..2 { for j in 0..3 { total = total + i * j; } }\n\
             total\n\
         }\n",
    );

    assert!(stats.unrolled >= 2, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(loops(body).is_empty(), "{:#?}", body.blocks);
    // i * j summed over both, which is 0 for the first turn of the outer loop
    // and 0 + 1 + 2 for the second.
    assert_eq!(kinds(body), vec![SIRInstKind::Literal(TIRLit::Int(3))], "{:#?}", kinds(body));
}

// A counted loop inside one that is not: the blocks being copied stand inside
// another loop, and the loop outside them has to be left holding the copies.
#[test]
fn a_counted_loop_inside_an_uncounted_one_leaves_the_uncounted_one_standing() {
    let (p, stats) = compiled(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn mixed(n: i32): i32 {\n\
             var total: i32 = 0;\n\
             var k: i32 = 0;\n\
             while k < n {\n\
                 for i in 0..2 { total = total + i; }\n\
                 k = k + 1;\n\
             }\n\
             total\n\
         }\n",
    );

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    let body = &p.bodies[0];
    assert_eq!(loops(body).len(), 1, "the one that is left is the one nothing counted");
    assert!(
        !inside_a_loop(body, |k| matches!(k, SIRInstKind::IterValid { .. })),
        "and no walk is left inside it: {:#?}",
        kinds(body)
    );
}
