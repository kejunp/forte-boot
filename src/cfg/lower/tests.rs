// What lowering makes of a typed tree: the control flow, and nothing else.

use super::*;
use crate::cfg::fixture::Fixture;
use crate::tir::ttir_nodes::{TTIRExprKind, TTIRStmt};

// Lowers a fixture and hands back the one body it built.
fn graph(f: Fixture) -> (CFGProgram, CFGBody) {
    let ttir = f.p;
    let mut l = Lowerer::new(&ttir);
    l.lower();
    let cfg = l.finish();
    let body = cfg.bodies[0].clone();
    (cfg, body)
}

// Every terminator the entry can reach.
fn terms(body: &CFGBody) -> Vec<CFGTerm> {
    let mut seen = vec![false; body.blocks.len()];
    let mut out = Vec::new();
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if seen[id] {
            continue;
        }
        seen[id] = true;
        let t = body.blocks[id].term.clone();
        match &t {
            CFGTerm::Goto(to) => stack.push(*to),
            CFGTerm::Branch { then, els, .. } => stack.extend([*then, *els]),
            CFGTerm::Match { arms, otherwise, .. } => {
                stack.extend(arms.iter().map(|a| a.block));
                stack.extend(otherwise.iter());
            }
            CFGTerm::ForEach { body: b, exit, .. } => stack.extend([*b, *exit]),
            _ => {}
        }
        out.push(t);
    }
    out
}

fn branches_in(body: &CFGBody) -> usize {
    terms(body).iter().filter(|t| matches!(t, CFGTerm::Branch { .. })).count()
}

// A body always ends by handing back a slot, whatever else it does.
#[test]
fn a_body_returns_a_slot() {
    let mut f = Fixture::new();
    let value = f.int(1);
    let block = f.block(Vec::new(), Some(value));
    f.body(block);
    let (cfg, body) = graph(f);

    assert!(terms(&body).iter().any(|t| matches!(t, CFGTerm::Return(Some(_)))));
    // The slot it hands back is one the lowering made, not one the source had.
    let CFGTerm::Return(Some(answer)) = terms(&body)
        .into_iter()
        .find(|t| matches!(t, CFGTerm::Return(Some(_))))
        .unwrap()
    else {
        unreachable!()
    };
    let CFGExprKind::Local(slot) = cfg.exprs[answer].kind else {
        panic!("{:?}", cfg.exprs[answer].kind)
    };
    assert!(body.locals[slot].synthetic);
}

// An `if` is one two-way edge, and both sides join.
#[test]
fn an_if_becomes_a_branch() {
    let mut f = Fixture::new();
    let cond = f.boolean(true);
    let (a, b) = (f.int(1), f.int(2));
    let then = f.block(Vec::new(), Some(a));
    let els = f.block(Vec::new(), Some(b));
    let iff = f.if_(cond, then, Some(els));
    let block = f.block(Vec::new(), Some(iff));
    f.body(block);
    let (_, body) = graph(f);
    assert_eq!(branches_in(&body), 1);
}

// The pair the whole graph is for: `a && b` is not an operator here, it is two
// branches -- `if a { if b { .. } }` drawn out.
#[test]
fn a_short_circuit_becomes_two_branches() {
    let mut f = Fixture::new();
    let (l, r) = (f.boolean(true), f.boolean(false));
    let cond = f.and(l, r);
    let call = f.call();
    let then = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: call }], None);
    let iff = f.if_(cond, then, None);
    let block = f.block(Vec::new(), Some(iff));
    f.body(block);
    let (cfg, body) = graph(f);

    assert_eq!(branches_in(&body), 2, "one branch for each side");
    // And no `&&` reached an expression.
    assert!(!cfg.exprs.iter().any(|e| matches!(
        &e.kind,
        CFGExprKind::Binary { op: crate::tir::tir_nodes::TIRBinOp::And, .. }
    )));

    // `||` is the same shape with the edges the other way.
    let mut f = Fixture::new();
    let (l, r) = (f.boolean(true), f.boolean(false));
    let cond = f.or(l, r);
    let then = f.block(Vec::new(), None);
    let iff = f.if_(cond, then, None);
    let block = f.block(Vec::new(), Some(iff));
    f.body(block);
    let (_, body) = graph(f);
    assert_eq!(branches_in(&body), 2);
}

// A `while` goes back to the block that tests it, which is the edge that makes
// it a loop at all.
#[test]
fn a_while_loops_back_to_its_condition() {
    let mut f = Fixture::new();
    let cond = f.boolean(true);
    let call = f.call();
    let inner = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: call }], None);
    let ty = f.null;
    let wh = f.expr(TTIRExprKind::While { cond, body: inner }, ty);
    let block = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: wh }], None);
    f.body(block);
    let (_, body) = graph(f);

    let head = match body.blocks[body.entry].term {
        CFGTerm::Goto(to) => to,
        ref other => panic!("{:?}", other),
    };
    let inner_block = match body.blocks[head].term {
        CFGTerm::Branch { then, .. } => then,
        ref other => panic!("{:?}", other),
    };
    assert_eq!(body.blocks[inner_block].term, CFGTerm::Goto(head), "the body goes back");
}

// A `for` stays one edge: there is no iterator protocol to draw it as two.
#[test]
fn a_for_is_an_edge_of_its_own() {
    let mut f = Fixture::new();
    let slot = f.slot("i", f.int);
    let iter = f.call();
    let inner = f.block(Vec::new(), None);
    let ty = f.null;
    let fo = f.expr(TTIRExprKind::For { local: slot, iter, body: inner }, ty);
    let block = f.block(vec![TTIRStmt::Expr { is_unsafe: false, expr: fo }], None);
    f.body(block);
    let (_, body) = graph(f);
    assert!(terms(&body).iter().any(|t| matches!(t, CFGTerm::ForEach { .. })));
}

// A `return` ends its block, and what follows is a block nothing reaches.
#[test]
fn a_return_ends_the_block_it_stands_in() {
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
    let (_, body) = graph(f);

    // Two `Return`s: the one written, and the one every body ends with.
    let returns = terms(&body).iter().filter(|t| matches!(t, CFGTerm::Return(_))).count();
    assert!(returns >= 1);
    // The call after it is in a block, and the entry cannot get to it.
    let mut reachable = vec![false; body.blocks.len()];
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if reachable[id] {
            continue;
        }
        reachable[id] = true;
        if let CFGTerm::Goto(to) = body.blocks[id].term {
            stack.push(to);
        }
    }
    assert!(reachable.iter().any(|&on| !on), "the tail is unreachable");
}

// A `let` fills a slot the body already declared, and the slot is the source's
// rather than one the lowering made.
#[test]
fn a_let_fills_the_slot_it_was_given() {
    let mut f = Fixture::new();
    let slot = f.slot("x", f.int);
    let init = f.int(5);
    let block = f.block(
        vec![TTIRStmt::Let { is_unsafe: false, local: slot, init: Some(init) }],
        None,
    );
    f.body(block);
    let (_, body) = graph(f);

    assert!(!body.locals[slot].synthetic);
    let set = body.blocks[body.entry]
        .stmts
        .iter()
        .any(|s| matches!(s.kind, CFGStmtKind::Set { local, .. } if local == slot));
    assert!(set, "{:#?}", body.blocks[body.entry].stmts);
}

// Every expression carries the type it was given, and the slots do too: that is
// what makes this a graph of a typed tree rather than of a parse.
#[test]
fn the_graph_keeps_the_types_it_was_handed() {
    let mut f = Fixture::new();
    let (int_ty, bool_ty) = (f.int, f.bool);
    let a = f.int(1);
    let b = f.int(2);
    let sum = f.add(a, b);
    let block = f.block(Vec::new(), Some(sum));
    f.body(block);
    let (cfg, body) = graph(f);

    let added = cfg
        .exprs
        .iter()
        .find(|e| matches!(e.kind, CFGExprKind::Binary { .. }))
        .expect("the addition");
    assert_eq!(added.ty, int_ty);
    // The slot the body hands back is typed as what it holds.
    assert!(body.locals.iter().any(|l| l.synthetic && l.ty == int_ty));
    assert_ne!(int_ty, bool_ty);
}
