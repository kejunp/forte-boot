// The whole pass over what the lowering actually makes, from source text.
//
// Everything else here builds its GIR by hand, which is what keeps each test
// about one rewrite. These do not: they run the whole compiler, so what the
// pass is held to is what the front of it really produces rather than what a
// fixture thought it would.

use super::*;

// A `for` goes through every rewrite here -- a loop is where a phi names
// itself, where a block has two ways in, and where a value is read above the
// instruction that makes it if a rewrite gets it wrong. Nothing is asserted
// about what it comes to; `worked` holding it to `verify` is the test.
#[test]
fn a_loop_survives_every_rewrite() {
    let (p, _) = worked(walking(true));
    let body = &p.bodies[0];
    assert!(
        count(body, |k| matches!(k, SIRInstKind::IterValid { .. })) > 0,
        "the loop is still a loop: {:#?}",
        kinds(body)
    );
}

// A call written out, the argument that came with it folded into the operator
// it reached, and a loop left standing beside both.
#[test]
fn a_program_written_as_source_comes_through_the_whole_pass() {
    let (p, stats) = compiled(
        "fn twice(n: i32): i32 { n * 2 }\n\
         fn counted(): i32 {\n\
             var a: i32 = twice(3) + 0;\n\
             var i: i32 = 0;\n\
             while i < 10 { a = a + i; i = i + 1; }\n\
             a\n\
         }\n",
    );

    assert_eq!(stats.inlined, 1, "{:#?}", stats);
    assert!(stats.folded > 0, "{:#?}", stats);
    // The one with a join in it: `twice` is a straight line, and the loop is
    // the only thing here that brings two paths together.
    let main = p
        .bodies
        .iter()
        .find(|body| !phis(body).is_empty())
        .expect("the body with the loop in it");
    assert_eq!(
        count(main, |k| matches!(k, SIRInstKind::Call { .. })),
        0,
        "nothing is called any more: {:#?}",
        kinds(main)
    );
    // `twice(3)` is 6 and `+ 0` is nothing, so what the loop starts from is a
    // literal and not a sum.
    assert_eq!(
        count(main, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(6)))),
        1,
        "{:#?}",
        kinds(main)
    );
    assert!(!phis(main).is_empty(), "the loop still joins two paths");
}

// And one that must not be written out, through the same pipeline: a fn that
// calls itself is the case where getting the cycle rule wrong does not fail a
// test, it fails to terminate.
#[test]
fn a_recursive_program_comes_through_it_too() {
    let (p, stats) = compiled(
        "fn down(n: i32): i32 { if n <= 0 { 0 } else { down(n - 1) } }\n\
         fn main(): null { var x: i32 = down(3); null }\n",
    );

    assert_eq!(stats.inlined, 0, "{:#?}", stats);
    let calls: usize = p.bodies.iter().map(|b| count(b, |k| matches!(k, SIRInstKind::Call { .. }))).sum();
    assert_eq!(calls, 2, "both calls stay");
}

// A struct built, handed to a fn, and read out of again on the other side --
// which is three separate rewrites meeting: the call written out, the field
// read out of the literal it was put in, and the sum of two literals. What is
// left of the body is the answer.
#[test]
fn a_struct_handed_to_a_call_comes_out_as_the_answer() {
    let (p, stats) = compiled(
        "struct Point { pub x: i32, pub y: i32 }\n\
         enum Shape { Dot, Line }\n\
         fn near(p: Point): i32 { p.x + p.y }\n\
         fn pick(s: Shape): i32 { match s { Shape::Dot => 1, Shape::Line => 2, } }\n\
         fn main(): i32 {\n\
             var p: Point = Point { x: 1, y: 2 };\n\
             var a: i32 = near(p);\n\
             var b: i32 = pick(Shape::Dot);\n\
             a + b * 1\n\
         }\n",
    );

    assert_eq!(stats.inlined, 2, "{:#?}", stats);
    // The bodies keep the order they were declared in, so `main` is the last.
    let main = p.bodies.last().expect("a body");
    assert_eq!(
        kinds(main),
        vec![SIRInstKind::Literal(TIRLit::Int(4))],
        "1 + 2, and 1 for the variant, and nothing else left: {:#?}",
        kinds(main)
    );

    // And the two bodies that were written out are still there to be called
    // from somewhere else. Nothing here decides that a declaration is unused.
    assert!(p.bodies.len() >= 3, "{:#?}", p.bodies.len());
}
