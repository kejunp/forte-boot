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
//
// One file per rewrite below, named for the file it tests. What stays here is
// what more than one of them wants: how to read a body back, and how to run a
// source string through the whole compiler.

use crate::gir::gir_nodes::{GIRExprKind, GIRTerm};
use crate::sir::fixture::*;
use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRAssignOp, TIRBinOp, TIRInline, TIRLit};
use crate::tir::ttir_nodes::Ty;

mod fold;
mod graph;
mod hoist;
mod inline;
mod levels;
mod memory;
mod share;
mod unroll;
mod whole;
mod wide;

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
