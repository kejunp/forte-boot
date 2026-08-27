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
use crate::tir::tir_nodes::{TIRAssignOp, TIRBinOp, TIRInline, TIRLit};
use crate::tir::ttir_nodes::Ty;

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
    compiled_at(source, crate::sir::opt::Level::Default)
}

fn compiled_at(
    source: &str,
    level: crate::sir::opt::Level,
) -> (SIRProgram, crate::sir::opt::Stats) {
    compiled_for(source, level, machine())
}

fn compiled_for(
    source: &str,
    level: crate::sir::opt::Level,
    target: crate::sir::target::Target,
) -> (SIRProgram, crate::sir::opt::Stats) {
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
    let stats = optimize(&mut out, &ttir, level, target);
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

// ---- Out of the loop --------------------------------------------------------

// Which loops the body still has, and which block each instruction stands in.
fn loops(body: &SIRBody) -> Vec<crate::sir::loops::Loop> {
    crate::sir::loops::Loop::all(body, &crate::sir::dom::Dominators::of(body))
}

fn inside_a_loop(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> bool {
    let held = loops(body);
    insts(body)
        .into_iter()
        .filter(|(_, inst)| want(&inst.kind))
        .any(|(at, _)| held.iter().any(|held| held.has(at)))
}

// Everything handed to a call, in the order the calls stand in.
fn all_handed(body: &SIRBody) -> Vec<SIRValueId> {
    insts(body)
        .into_iter()
        .filter_map(|(_, inst)| match inst.kind {
            SIRInstKind::Call { args, .. } if !args.is_empty() => Some(args[0]),
            _ => None,
        })
        .collect()
}

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

// ---- The loop written out ---------------------------------------------------

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

// ---- What a store put there -------------------------------------------------

// Written and then read back: the read is the value that was written, and the
// read itself goes.
//
// The address is handed away first, which is what keeps the name in the frame
// -- `sir::promote` would otherwise have taken it out and answered the read
// long before this pass saw it. Every one of these does that or something like
// it, because a name still reached by loads and stores is by definition one
// that pass gave up on.
#[test]
fn a_load_below_a_store_to_one_place_is_what_the_store_wrote() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let seven = f.int(7);
    f.set(at, x, seven);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    // The last of the calls, the first being the one the address went out in.
    let read = *all_handed(body).last().expect("something was handed something");
    assert_eq!(literal(body, read), TIRLit::Int(7), "{:#?}", kinds(body));
}

// A write to another name is a write somewhere else, so it does not stop it.
#[test]
fn a_write_to_another_name_does_not_stop_it() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let y = f.local("y", f.int);
    let at = f.block();
    for name in [x, y] {
        let read = f.read(name);
        let addr = f.addr_of(read);
        let hands = f.hands(addr);
        f.eval(at, hands);
    }
    let seven = f.int(7);
    f.set(at, x, seven);
    let eight = f.int(8);
    f.set(at, y, eight);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    let read = *all_handed(body).last().expect("something was handed something");
    assert_eq!(literal(body, read), TIRLit::Int(7), "{:#?}", kinds(body));
}

// And not across a call, where the name is one whose address went out: what
// the call does through it is not this pass's to guess.
#[test]
fn a_call_between_them_ends_what_is_known_of_a_name_that_got_out() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let seven = f.int(7);
    f.set(at, x, seven);
    let call = f.call();
    f.eval(at, call);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(stats.forwarded, 0, "{:#?}", stats);
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Load { .. })) > 0,
        "the read is still a read: {:#?}",
        kinds(body)
    );
}

// A name nothing let out is one the call cannot have reached, so what was
// written to it is still what is there afterwards. Here it is a field written
// to that keeps the name in the frame, and stepping into a name is not letting
// it out -- which is the whole of what `sir::alias` adds over `sir::promote`.
#[test]
fn a_call_leaves_alone_what_it_could_not_have_reached() {
    let mut f = Fixture::new();
    let xs = f.local("xs", f.int);
    let at = f.block();
    let ty = f.int;
    let base = f.read(xs);
    let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
    let one = f.int(1);
    f.store(at, field, TIRAssignOp::Set, one);
    let five = f.int(5);
    f.set(at, xs, five);
    let call = f.call();
    f.eval(at, call);
    let read = f.read(xs);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    assert_eq!(literal(body, handed(body)), TIRLit::Int(5), "{:#?}", kinds(body));
}

// The same rewrite from source, over the one shape the lowering leaves a load
// in: a name whose address was handed away, so `sir::promote` could not take
// it out of the frame.
//
// The call is `%noinline` because the alternative is the better answer -- with
// the body written out, nothing holds the address any more and the name comes
// out of the frame altogether, which is `promote` answering the question
// before this pass is asked it.
#[test]
fn a_name_whose_address_went_out_is_still_read_back_as_what_was_written() {
    let (p, stats) = compiled(
        "%noinline\n\
         fn sink(p: &i32): null { null }\n\
         fn kept(): i32 { var x: i32 = 0; sink(&x); x = 7; x }\n",
    );

    assert_eq!(stats.forwarded, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Load { .. })),
        0,
        "the read is the value the write wrote: {:#?}",
        kinds(body)
    );
    let handed = body
        .blocks
        .iter()
        .find_map(|block| match block.term {
            SIRTerm::Return(Some(value)) => Some(value),
            _ => None,
        })
        .expect("something is given back");
    assert_eq!(literal(body, handed), TIRLit::Int(7), "{:#?}", kinds(body));
    // And the store stays: the address went out, so something else may read
    // what is there.
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Store { .. })), 2, "{:#?}", kinds(body));
}

// ---- Stores nothing will read -----------------------------------------------

// Written twice with nothing between: the first write is one nobody could have
// seen the result of.
#[test]
fn a_store_written_over_before_anything_reads_it_goes() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let one = f.int(1);
    f.set(at, x, one);
    let two = f.int(2);
    f.set(at, x, two);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, _) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Store { .. })),
        1,
        "one write where there were two: {:#?}",
        kinds(body)
    );
}

// Unless something between may read it. A read of the name is the plain case;
// a call is the case that needs to know whether the name ever got out.
#[test]
fn a_read_between_them_keeps_the_first_write() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let one = f.int(1);
    f.set(at, x, one);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    let two = f.int(2);
    f.set(at, x, two);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, _) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "{:#?}",
        kinds(body)
    );
}

// A call between them reads it if it could have reached it, and not if it
// could not -- the same question, and the same answer, as everywhere else.
#[test]
fn a_call_between_them_keeps_the_first_write_only_if_it_could_read_it() {
    let build = |lets_out: bool| {
        let mut f = Fixture::new();
        let x = f.local("x", f.int);
        let at = f.block();
        if lets_out {
            let read = f.read(x);
            let addr = f.addr_of(read);
            let hands = f.hands(addr);
            f.eval(at, hands);
        } else {
            // Something else that keeps the name in the frame without letting
            // it out, so that there is still a store here to have an opinion
            // about.
            let ty = f.int;
            let base = f.read(x);
            let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
            let nine = f.int(9);
            f.store(at, field, TIRAssignOp::Set, nine);
        }
        let one = f.int(1);
        f.set(at, x, one);
        let call = f.call();
        f.eval(at, call);
        let two = f.int(2);
        f.set(at, x, two);
        f.term(at, GIRTerm::Return(None));
        f.body(at);
        worked(f).0
    };

    let open = build(true);
    assert_eq!(
        count(&open.bodies[0], |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "the call may read what was written: {:#?}",
        kinds(&open.bodies[0])
    );

    let shut = build(false);
    // The write to the field, and one of the two to the name.
    assert_eq!(
        count(&shut.bodies[0], |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "the call cannot have reached it: {:#?}",
        kinds(&shut.bodies[0])
    );
}

// ---- Several turns at once --------------------------------------------------

// The canonical shape, and the one the three rewrites before this one exist to
// leave behind: a counted loop written out as its turns, each turn reading two
// neighbouring elements and writing a third. Four adds become one.
const NEIGHBOURS: &str = "struct Range<T> { pub lo: T, pub hi: T }\n\
     fn add4(a: i32[4], b: i32[4]): i32[4] {\n\
         var c: i32[4] = [0, 0, 0, 0];\n\
         for i in 0..4 { c[i] = a[i] + b[i]; }\n\
         c\n\
     }\n";

fn wide(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> Vec<usize> {
    insts(body)
        .into_iter()
        .filter(|(_, inst)| want(&inst.kind))
        .filter_map(|(_, inst)| inst.def.map(|def| body.values[def].lanes))
        .collect()
}

#[test]
fn a_run_of_writes_to_neighbouring_places_becomes_one_write() {
    let (p, stats) = compiled_at(NEIGHBOURS, crate::sir::opt::Level::More);
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert_eq!(stats.widened, 1, "{:#?}", stats);

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::VecStore { .. })),
        1,
        "one write where there were four: {:#?}",
        kinds(body)
    );
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Lanes { lanes: 4, .. })),
        2,
        "and one read of each thing read: {:#?}",
        kinds(body)
    );
    // The add is one instruction over four of everything.
    assert_eq!(
        wide(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        vec![4],
        "{:#?}",
        kinds(body)
    );
    // And the elements are not read one at a time any more.
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Index { .. })), 0, "{:#?}", kinds(body));
}

// It stands at the top level alone: the width is a guess about a machine, and
// a guess is not something to make on a program's behalf unless it was asked
// for.
#[test]
fn nothing_is_widened_below_the_top_level() {
    for level in [
        crate::sir::opt::Level::Less,
        crate::sir::opt::Level::Default,
    ] {
        let (p, stats) = compiled_at(NEIGHBOURS, level);
        assert_eq!(stats.widened, 0, "at {:?}: {:#?}", level, stats);
        assert_eq!(
            count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })),
            0,
            "at {:?}",
            level
        );
    }
}

// And only where the writes can be brought together. A call standing between
// them is what decides it -- and whether it decides it turns entirely on
// whether the call could have reached what is being written, which is the
// question `sir::alias` answers and nothing before it could.
#[test]
fn a_call_between_the_writes_stops_it_only_if_it_could_have_reached_them() {
    let build = |lets_out: bool| {
        let source = format!(
            "struct Range<T> {{ pub lo: T, pub hi: T }}\n\
             %noinline\n\
             fn sink(p: &i32[4]): null {{ null }}\n\
             %noinline\n\
             fn touch(): null {{ null }}\n\
             fn go(a: i32[4]): i32[4] {{\n\
                 var c: i32[4] = [0, 0, 0, 0];\n\
                 {}\n\
                 for i in 0..4 {{ c[i] = a[i]; touch(); }}\n\
                 c\n\
             }}\n",
            if lets_out { "sink(&c);" } else { "" }
        );
        compiled_at(&source, crate::sir::opt::Level::More)
    };

    let (_, shut) = build(false);
    assert_eq!(
        shut.widened, 1,
        "nothing kept the address of `c`, so the calls cannot have written it: {:#?}",
        shut
    );

    let (_, open) = build(true);
    assert_eq!(
        open.widened, 0,
        "the address went out, so what the calls did with it is not known: {:#?}",
        open
    );
}

// One write is never a group, however wide the machine. Two is the floor, and
// it is the floor because one of something at a time is what the program
// already said.
#[test]
fn one_write_on_its_own_is_not_a_group() {
    let (p, stats) = compiled_at(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn one(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..1 { c[i] = a[i]; }\n\
             c\n\
         }\n",
        crate::sir::opt::Level::More,
    );

    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert_eq!(
        count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })),
        0,
        "{:#?}",
        kinds(&p.bodies[0])
    );
}

// And two of them are, on a machine that holds four: the register is a ceiling
// and not a quota.
#[test]
fn two_writes_are_a_group_on_a_machine_that_holds_four() {
    let (p, stats) = compiled_at(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn two(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..2 { c[i] = a[i]; }\n\
             c\n\
         }\n",
        crate::sir::opt::Level::More,
    );

    assert_eq!(stats.widened, 1, "{:#?}", stats);
    assert_eq!(written_wide(&p.bodies[0]), vec![2], "{:#?}", kinds(&p.bodies[0]));
}

// ---- What the machine can do ------------------------------------------------

// How wide the value a vector store writes is, which is the whole of what the
// target decides.
fn written_wide(body: &SIRBody) -> Vec<usize> {
    insts(body)
        .into_iter()
        .filter_map(|(_, inst)| match inst.kind {
            SIRInstKind::VecStore { value, .. } => Some(body.values[value].lanes),
            _ => None,
        })
        .collect()
}

const COPY64: &str = "struct Range<T> { pub lo: T, pub hi: T }\n\
     fn copy(a: i64[4]): i64[4] {\n\
         var c: i64[4] = [0, 0, 0, 0];\n\
         for i in 0..4 { c[i] = a[i]; }\n\
         c\n\
     }\n";

// How many go at once is the register over the thing, so the same source over
// the same type comes out in twos on one machine and fours on another.
#[test]
fn a_wider_machine_takes_more_at_a_time() {
    let (narrow, _) = compiled_for(COPY64, crate::sir::opt::Level::More, crate::sir::target::X86_64);
    assert_eq!(
        written_wide(&narrow.bodies[0]),
        vec![2, 2],
        "two eight-byte things in sixteen bytes, so the four are written twice: {:#?}",
        kinds(&narrow.bodies[0])
    );

    let (wide, _) =
        compiled_for(COPY64, crate::sir::opt::Level::More, crate::sir::target::X86_64_V3);
    assert_eq!(
        written_wide(&wide.bodies[0]),
        vec![4],
        "and four of them in thirty-two, so once: {:#?}",
        kinds(&wide.bodies[0])
    );
}

// A register filled halfway is still a register. Four of something on a
// machine that holds eight is written out as four rather than left alone.
#[test]
fn a_group_narrower_than_the_register_is_still_worth_making() {
    let (p, stats) =
        compiled_for(NEIGHBOURS, crate::sir::opt::Level::More, crate::sir::target::X86_64_V4);
    assert_eq!(stats.widened, 1, "{:#?}", stats);
    assert_eq!(
        written_wide(&p.bodies[0]),
        vec![4],
        "sixteen would fit and there are four: {:#?}",
        kinds(&p.bodies[0])
    );
}

// A machine with no vectors is a target like any other, and nothing is widened
// for it however hard the level says to try.
#[test]
fn a_machine_with_no_vectors_leaves_it_all_alone() {
    let (p, stats) =
        compiled_for(NEIGHBOURS, crate::sir::opt::Level::More, crate::sir::target::NONE);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert_eq!(count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })), 0);
    // And the rest of the level still happened.
    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
}

// What the machine has not got is not done to several at once, whatever the
// shape of the loop. An integer divide is the one everybody expects to be
// there: four of them line up as neatly as four adds, and there is no machine
// here that can do them together.
#[test]
fn what_the_machine_cannot_do_is_left_one_at_a_time() {
    let divided = |ty: &str, by: &str| {
        format!(
            "struct Range<T> {{ pub lo: T, pub hi: T }}\n\
             fn half(a: {0}[4]): {0}[4] {{\n\
                 var c: {0}[4] = [{1}, {1}, {1}, {1}];\n\
                 for i in 0..4 {{ c[i] = a[i] / {2}; }}\n\
                 c\n\
             }}\n",
            ty,
            if ty == "f32" { "0.0" } else { "0" },
            by
        )
    };

    let (_, whole) = compiled_at(&divided("i32", "2"), crate::sir::opt::Level::More);
    assert_eq!(whole.widened, 0, "there is no integer divide over a vector: {:#?}", whole);

    let (p, real) = compiled_at(&divided("f32", "2.0"), crate::sir::opt::Level::More);
    assert_eq!(real.widened, 1, "and there is a float one: {:#?}", real);
    assert_eq!(written_wide(&p.bodies[0]), vec![4]);
}

// ---- Whether it is worth it -------------------------------------------------

// Values that have to be fetched one at a time cost an insert each, which is
// most of what a group of them would have saved. The same loop with the values
// already lined up is worth making, and it is the only difference between the
// two.
#[test]
fn a_group_that_must_be_gathered_is_not_worth_making() {
    let gathered = "struct Range<T> { pub lo: T, pub hi: T }\n\
         %noinline\n\
         fn make(n: i32): i32 { n }\n\
         fn go(): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..4 { c[i] = make(i); }\n\
             c\n\
         }\n";
    let (_, stats) = compiled_at(gathered, crate::sir::opt::Level::More);
    assert_eq!(
        stats.widened, 0,
        "four inserts to save four stores is not a saving: {:#?}",
        stats
    );

    let lined_up = "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn go(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..4 { c[i] = a[i]; }\n\
             c\n\
         }\n";
    let (_, stats) = compiled_at(lined_up, crate::sir::opt::Level::More);
    assert_eq!(stats.widened, 1, "one read and one write is: {:#?}", stats);
}

// And a machine where an insert costs more is a machine where fewer groups are
// worth making, which is what a cost model is for.
#[test]
fn what_an_insert_costs_changes_what_is_worth_making() {
    // Two values that cannot be lined up, written to neighbouring places.
    let source = "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn go(a: i64[4], b: i64[4]): i64[4] {\n\
             var c: i64[4] = [0, 0, 0, 0];\n\
             c[0] = a[1];\n\
             c[1] = b[0];\n\
             c\n\
         }\n";
    let cheap = crate::sir::target::Target { insert: 1, ..crate::sir::target::X86_64 };
    let dear = crate::sir::target::Target { insert: 4, ..crate::sir::target::X86_64 };

    let (_, held) = compiled_for(source, crate::sir::opt::Level::More, dear);
    assert_eq!(held.widened, 0, "four an insert is more than the stores cost: {:#?}", held);

    // The same program, the same everything, and one number different.
    let (_, held) = compiled_for(source, crate::sir::opt::Level::More, cheap);
    assert!(held.widened <= 1, "{:#?}", held);
}

// ---- How hard to try --------------------------------------------------------

// A program with something for every kind of rewrite in it, run at each level,
// so that what each one turns on is written down as a test rather than as a
// comment.
const EVERYTHING: &str = "struct Range<T> { pub lo: T, pub hi: T }\n\
     fn twice(n: i32): i32 { n * 2 }\n\
     fn all(a: i32[4]): i32[4] {\n\
         var c: i32[4] = [0, 0, 0, 0];\n\
         var k: i32 = twice(3) + 0;\n\
         for i in 0..4 { c[i] = a[i] + k; }\n\
         c\n\
     }\n";

// Nothing at all, which is what `-O0` is for: what comes out is what the
// lowering and the promotion made of the source.
#[test]
fn the_bottom_level_changes_nothing() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::None);

    assert_eq!(stats, crate::sir::opt::Stats::default(), "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(!loops(body).is_empty(), "the loop is still a loop");
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Call { .. })) > 0,
        "and the call is still a call: {:#?}",
        kinds(body)
    );
}

// The first level takes things away and moves nothing.
#[test]
fn the_first_level_removes_and_does_not_move() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::Less);

    assert_eq!(stats.inlined, 0, "{:#?}", stats);
    assert_eq!(stats.unrolled, 0, "{:#?}", stats);
    assert_eq!(stats.hoisted, 0, "{:#?}", stats);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert!(stats.dead > 0 || stats.folded > 0 || stats.shared > 0, "{:#?}", stats);
    assert!(!loops(p.bodies.last().expect("a body")).is_empty(), "the loop stands");
}

// The second moves code as well, which is where a program may come out bigger
// than it went in.
#[test]
fn the_second_level_writes_calls_and_loops_out() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::Default);

    assert!(stats.inlined > 0, "{:#?}", stats);
    assert!(stats.unrolled > 0, "{:#?}", stats);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(loops(body).is_empty(), "the loop is written out: {:#?}", body.blocks);
    // `twice(3) + 0` is 6, worked out here and not there.
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(6)))) > 0,
        "{:#?}",
        kinds(body)
    );
}

// And the third widens what the second left in a straight line.
#[test]
fn the_third_level_runs_the_turns_together() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::More);

    assert!(stats.inlined > 0, "{:#?}", stats);
    assert!(stats.unrolled > 0, "{:#?}", stats);
    assert_eq!(stats.widened, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    // The literal that does not vary with the turn is in every lane of one
    // value rather than in four instructions.
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Pack(_))),
        1,
        "{:#?}",
        kinds(body)
    );
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::VecStore { .. })), 1);
}

// The levels are ordered, which is what lets a rewrite ask `>= Default`
// instead of naming every level it runs at.
#[test]
fn the_levels_are_ordered_and_numbered() {
    use crate::sir::opt::Level;
    assert!(Level::None < Level::Less);
    assert!(Level::Less < Level::Default);
    assert!(Level::Default < Level::More);
    assert_eq!(Level::of(0), Level::None);
    assert_eq!(Level::of(2), Level::Default);
    assert_eq!(Level::of(3), Level::More);
    // A number nobody wrote a level for is the most there is.
    assert_eq!(Level::of(9), Level::More);
    assert_eq!(Level::default(), Level::Default);
}
