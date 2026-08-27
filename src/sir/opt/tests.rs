// What the pass takes out, and what it leaves standing.
//
// Every one of these goes through `fixture::worked`, which lowers, promotes,
// optimizes, and holds the result to the two rules in `verify.rs` after each
// of the three. So a test below that only looks at one instruction still says
// the rest of the body is well formed -- which matters more here than
// anywhere else in the SIR, because every rewrite in this pass is one that can
// break SSA quietly and leave the graph walking.
//
// The tests that assert something is *kept* are as much of the pass as the
// ones that assert something goes. An optimiser is only worth having if it is
// wrong about nothing, and the cases it must decline are where that is
// decided.

use crate::gir::gir_nodes::{GIRExprKind, GIRTerm};
use crate::sir::fixture::*;
use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRInline, TIRLit};

fn find(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> SIRInst {
    insts(body)
        .into_iter()
        .find(|(_, inst)| want(&inst.kind))
        .map(|(_, inst)| inst)
        .unwrap_or_else(|| panic!("nothing like that in {:#?}", kinds(body)))
}

// What the one call in the body was handed, which is how these tests ask "and
// what does this come to".
fn handed(body: &SIRBody) -> SIRValueId {
    let call = find(body, |k| matches!(k, SIRInstKind::Call { args, .. } if !args.is_empty()));
    let SIRInstKind::Call { args, .. } = call.kind else { unreachable!() };
    args[0]
}

fn literal(body: &SIRBody, value: SIRValueId) -> TIRLit {
    let found = insts(body).into_iter().find(|(_, inst)| inst.def == Some(value));
    match found.map(|(_, inst)| inst.kind) {
        Some(SIRInstKind::Literal(held)) => held,
        other => panic!("%{} is {:#?}, not a literal", value, other),
    }
}

fn blocks(body: &SIRBody) -> usize {
    body.live().iter().filter(|on| **on).count()
}

// ---- Folding ----------------------------------------------------------------

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

// ---- Branches and blocks ----------------------------------------------------

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

// ---- Two instructions, one value --------------------------------------------

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

// ---- What nothing reads -----------------------------------------------------

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

// ---- Writing a call out -----------------------------------------------------

// The body stands where the call did, the argument stands where the parameter
// did, and what that leaves is an operator over two literals -- which is the
// whole reason inlining is in the same pass as folding.
#[test]
fn a_call_to_a_declaration_is_written_out_where_it_was_called() {
    let mut f = Fixture::new();
    let n = f.param("n", f.int);
    let at = f.block();
    let (read, one) = (f.read(n), f.int(1));
    let sum = f.add(read, one);
    f.term(at, GIRTerm::Return(Some(sum)));
    let callee = f.body(at);
    let item = f.function("more", callee, TIRInline::Unwritten);

    let at = f.block();
    let two = f.int(2);
    let call = f.calling(item, vec![two]);
    let hands = f.hands(call);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    let caller = f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[caller];

    assert_eq!(stats.inlined, 1, "{:#?}", stats);
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Call { args, .. } if args.is_empty())),
        0,
        "nothing is called any more: {:#?}",
        kinds(body)
    );
    assert_eq!(literal(body, handed(body)), TIRLit::Int(3), "{:#?}", kinds(body));
}

// A fn that can reach itself is one there would be no end to writing out. The
// call stays, and so does the body it called.
#[test]
fn a_call_that_can_reach_itself_is_left_alone() {
    let mut f = Fixture::new();
    // The item is made first so that the body can name it: an id is settled by
    // the order things are pushed in, and this body is the first there is.
    let item = f.function("again", 0, TIRInline::Unwritten);
    let at = f.block();
    let call = f.calling(item, Vec::new());
    f.eval(at, call);
    f.term(at, GIRTerm::Return(None));
    let id = f.body(at);
    assert_eq!(id, 0);

    let (p, stats) = worked(f);
    let body = &p.bodies[0];

    assert_eq!(stats.inlined, 0, "{:#?}", stats);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Call { .. })), 1);
}

// And `@noinline` is the source having already decided, whatever this pass
// would have made of the size.
#[test]
fn a_declaration_written_noinline_is_not_written_out() {
    let mut f = Fixture::new();
    let at = f.block();
    let one = f.int(1);
    f.term(at, GIRTerm::Return(Some(one)));
    let callee = f.body(at);
    let item = f.function("kept", callee, TIRInline::Never);

    let at = f.block();
    let call = f.calling(item, Vec::new());
    let hands = f.hands(call);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    let caller = f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[caller];

    assert_eq!(stats.inlined, 0, "{:#?}", stats);
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Call { args, .. } if args.is_empty())),
        1,
        "{:#?}",
        kinds(body)
    );
}

// Two ways back, so what the call made cannot be either of them and is the phi
// the continuation begins with. `fixture::worked` is what checks that the phi
// has one edge per way in; this checks there is one at all.
#[test]
fn a_callee_with_two_returns_leaves_a_phi_where_the_call_was() {
    let mut f = Fixture::new();
    let a = f.param("a", f.bool);
    let (at, then, els) = (f.block(), f.block(), f.block());
    let cond = f.read(a);
    f.term(at, GIRTerm::Branch { cond, then, els });
    let one = f.int(1);
    f.term(then, GIRTerm::Return(Some(one)));
    let two = f.int(2);
    f.term(els, GIRTerm::Return(Some(two)));
    let callee = f.body(at);
    let item = f.function("either", callee, TIRInline::Unwritten);

    let at = f.block();
    let yes = f.boolean(true);
    let call = f.calling(item, vec![yes]);
    let hands = f.hands(call);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    let caller = f.body(at);

    let (p, stats) = worked(f);
    let body = &p.bodies[caller];

    assert_eq!(stats.inlined, 1, "{:#?}", stats);
    // The argument was a literal, so the branch the callee began with folds
    // and only one of the two ways back is left standing.
    assert_eq!(literal(body, handed(body)), TIRLit::Int(1), "{:#?}", kinds(body));
}

// ---- The shapes the lowering makes ------------------------------------------

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

// ---- From source --------------------------------------------------------

// Everything above builds its GIR by hand, which is what keeps each test about
// one rewrite. This one does not: it runs the whole compiler, so that what the
// pass is held to is what the lowering actually makes rather than what a
// fixture thought it would.
//
// It is the only test here that would catch a rewrite that is sound on every
// shape a fixture writes and wrong on the shape a `while` lowers to.
fn compiled(source: &str) -> (SIRProgram, crate::sir::opt::Stats) {
    use crate::expand::Expander;
    use crate::gir;
    use crate::lex::lexer::Lexer;
    use crate::parse::parser::Parser;
    use crate::prep::preprocess;
    use crate::sema;
    use crate::sir::lower::Lowerer;
    use crate::sir::opt::optimize;
    use crate::sir::promote::promote;
    use crate::tir::lower::Lowerer as TIRLowerer;

    let prepped = preprocess(source);
    let mut p = Parser::new(Lexer::new(&prepped));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{:#?}", p.errors());
    let root = {
        let mut e = Expander::new(&mut p);
        let out = e.expand(&root);
        assert!(e.errors().is_empty(), "{:#?}", e.errors());
        out
    };
    let mut l = TIRLowerer::new(&p);
    l.lower(&root);
    assert!(l.errors().is_empty(), "{:#?}", l.errors());
    let tir = l.finish();
    let (ttir, errors) = sema::lower::Lowerer::new(&tir).lower(vec!["t".to_string()]);
    assert!(!errors.has_errors(), "{:#?}", errors);

    let mut lowerer = gir::lower::Lowerer::new(&ttir);
    lowerer.lower();
    let mut graph = lowerer.finish();
    let copies = sema::borrows::Copies::of(&ttir);
    let generics: Vec<Vec<crate::tir::ttir_nodes::TTIRGeneric>> = (0..graph.bodies.len())
        .map(|body| crate::generics_of(&ttir, body))
        .collect();
    gir::drops::Drops::new(&ttir, &copies).place(&mut graph, &generics);
    gir::opt::optimize(&mut graph);

    let mut lowerer = Lowerer::new(&ttir, &graph);
    lowerer.lower();
    let mut out = lowerer.finish();
    promote(&mut out);
    sound(&out);
    let stats = optimize(&mut out, &ttir);
    sound(&out);
    (out, stats)
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
