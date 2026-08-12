// What the simplifier makes of a graph, and what it deliberately leaves alone.

use super::*;
use crate::cfg::fixture::Fixture;
use crate::cfg::lower::Lowerer;
use crate::cfg::source_map::{Reason, Rewrite};
use crate::tir::ttir_nodes::{TTIRExprKind, TTIRStmt};

// Lowers a fixture and simplifies what came out.
fn run(f: Fixture) -> (CFGProgram, CFGSourceMap, CFGBody) {
    let ttir = f.p;
    let mut l = Lowerer::new(&ttir);
    l.lower();
    let mut cfg = l.finish();
    let map = optimize(&mut cfg);
    let body = cfg.bodies[0].clone();
    (cfg, map, body)
}

fn branch_count(body: &CFGBody) -> usize {
    let live = live_blocks(body);
    body.blocks
        .iter()
        .enumerate()
        .filter(|(id, b)| live[*id] && matches!(b.term, CFGTerm::Branch { .. }))
        .count()
}

// Every value written into a slot, which is where a folded answer ends up.
fn set_values(cfg: &CFGProgram, body: &CFGBody) -> Vec<CFGExprKind> {
    let live = live_blocks(body);
    let mut out = Vec::new();
    for (id, block) in body.blocks.iter().enumerate() {
        if !live[id] {
            continue;
        }
        for s in &block.stmts {
            if let CFGStmtKind::Set { value, .. } = s.kind {
                out.push(cfg.exprs[value].kind.clone());
            }
        }
    }
    out
}

#[test]
fn arithmetic_over_literals_folds() {
    let mut f = Fixture::new();
    let (a, b) = (f.int(1), f.int(2));
    let sum = f.add(a, b);
    let block = f.block(Vec::new(), Some(sum));
    f.body(block);
    let (cfg, _, body) = run(f);

    assert!(
        set_values(&cfg, &body)
            .iter()
            .any(|k| matches!(k, CFGExprKind::Literal(TIRLit::Int(3)))),
        "{:#?}",
        set_values(&cfg, &body)
    );
}

// A condition that is already a literal has one edge and not two.
#[test]
fn a_branch_that_cannot_be_taken_becomes_a_goto() {
    let mut f = Fixture::new();
    let cond = f.boolean(true);
    let then = f.block(Vec::new(), None);
    let els = f.block(Vec::new(), None);
    let iff = f.if_(cond, then, Some(els));
    let block = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: iff }], None);
    f.body(block);
    let (_, map, body) = run(f);

    assert_eq!(branch_count(&body), 0, "the branch is settled");
    assert!(
        map.dropped().iter().any(|d| d.why == Reason::BranchNotTaken),
        "{:#?}",
        map.dropped()
    );
}

// `&&` is two branches by the time the simplifier sees it, so settling the
// first side settles the whole of it.
#[test]
fn a_settled_short_circuit_loses_both_its_branches() {
    let mut f = Fixture::new();
    let (l, r) = (f.boolean(false), f.boolean(true));
    let cond = f.and(l, r);
    let then = f.block(Vec::new(), None);
    let iff = f.if_(cond, then, None);
    let block = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: iff }], None);
    f.body(block);
    let (_, _, body) = run(f);
    assert_eq!(branch_count(&body), 0, "neither side is reached");
}

// What the entry cannot get to is not run, and says so.
#[test]
fn a_block_nothing_reaches_is_emptied() {
    let mut f = Fixture::new();
    let value = f.int(1);
    let ty = f.int;
    let ret = f.expr(TTIRExprKind::Return(Some(value)), ty);
    let after = f.call();
    let block = f.block(
        vec![
            TTIRStmt::Expr { is_unsafe: false, expr: ret },
            TTIRStmt::Expr { is_unsafe: false, expr: after },
        ],
        None,
    );
    f.body(block);
    let (_, map, body) = run(f);

    let live = live_blocks(&body);
    for (id, block) in body.blocks.iter().enumerate() {
        if !live[id] {
            assert!(block.stmts.is_empty(), "block {} still holds statements", id);
            assert_eq!(block.term, CFGTerm::Unreachable);
        }
    }
    assert!(
        map.dropped().iter().any(|d| d.why == Reason::AfterDiverging),
        "{:#?}",
        map.dropped()
    );
}

#[test]
fn a_fold_records_what_stood_there() {
    let mut f = Fixture::new();
    let (a, b) = (f.int(1), f.int(2));
    let sum = f.add(a, b);
    let block = f.block(Vec::new(), Some(sum));
    f.body(block);
    let (cfg, map, _) = run(f);

    let folded = cfg
        .exprs
        .iter()
        .position(|e| matches!(&e.kind, CFGExprKind::Literal(TIRLit::Int(3))))
        .expect("a folded 3");
    let origin = map.origin(folded).expect("an origin");
    assert_eq!(origin.why, Rewrite::Folded);
    assert_eq!(origin.was, "a binary operator");
}

// Running it twice changes nothing the first run did not already do.
#[test]
fn a_second_run_is_a_no_op() {
    let mut f = Fixture::new();
    let cond = f.boolean(true);
    let (x, y) = (f.int(1), f.int(2));
    let sum = f.add(x, y);
    let then = f.block(Vec::new(), Some(sum));
    let iff = f.if_(cond, then, None);
    let block = f.block(Vec::new(), Some(iff));
    f.body(block);

    let ttir = f.p;
    let mut l = Lowerer::new(&ttir);
    l.lower();
    let mut cfg = l.finish();
    optimize(&mut cfg);
    let before = cfg.clone();
    let again = optimize(&mut cfg);
    assert_eq!(again.rounds, 1, "a settled graph takes one round to say so");
    assert_eq!(again.rewrites(), 0, "a settled graph is rewritten no further");
    assert_eq!(cfg, before, "the second run moved something");
}
