// Where a release goes, and which ones run.

use super::*;
use crate::gir::fixture::Fixture;
use crate::gir::lower::Lowerer;
use crate::tir::ttir_nodes::{TTIRExprKind, TTIRStmt};

// A fixture through both passes, and the body they made of it.
fn placed(f: Fixture) -> GIRBody {
    let ttir = f.p;
    let mut l = Lowerer::new(&ttir);
    l.lower();
    let mut gir = l.finish();
    let copies = Copies::of(&ttir);
    let generics: Vec<Vec<TTIRGeneric>> = vec![Vec::new(); gir.bodies.len()];
    Drops::new(&ttir, &copies).place(&mut gir, &generics);
    gir.bodies[0].clone()
}

// Every release the body holds, in the order the blocks were built -- which is
// the order they were written.
fn releases(body: &GIRBody) -> Vec<GIRLocalId> {
    body.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s.kind {
            GIRStmtKind::Drop { local } => Some(local),
            _ => None,
        })
        .collect()
}

// The releases the entry can get to. What stands in a block nothing reaches is
// not a release that runs, and is `opt`'s to take away rather than this pass's.
fn reached(body: &GIRBody) -> Vec<GIRLocalId> {
    let mut seen = vec![false; body.blocks.len()];
    let mut out = Vec::new();
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if seen[id] {
            continue;
        }
        seen[id] = true;
        out.extend(body.blocks[id].stmts.iter().filter_map(|s| match s.kind {
            GIRStmtKind::Drop { local } => Some(local),
            _ => None,
        }));
        match &body.blocks[id].term {
            GIRTerm::Goto(to) => stack.push(*to),
            GIRTerm::Branch { then, els, .. } => stack.extend([*then, *els]),
            GIRTerm::Match { arms, otherwise, .. } => {
                stack.extend(arms.iter().map(|a| a.block));
                stack.extend(otherwise.iter());
            }
            GIRTerm::ForEach { body: b, exit, .. } => stack.extend([*b, *exit]),
            _ => {}
        }
    }
    out
}

// Every branch the body ends a block on, which is how a flag shows.
fn branches(body: &GIRBody) -> usize {
    body.blocks.iter().filter(|b| matches!(b.term, GIRTerm::Branch { .. })).count()
}

// "a local at the end of its block" -- and only a local whose type has
// something to release.
#[test]
fn a_local_is_released_at_the_end_of_its_block() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let held = f.slot("held", buf);
    let plain = f.slot("plain", f.int);
    let one = f.call();
    let two = f.int(1);
    let stmts = vec![f.let_(held, Some(one)), f.let_(plain, Some(two))];
    let block = f.block(stmts, None);
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    assert_eq!(releases(&body), vec![held]);
}

// "locals in the reverse of it, which is the order that lets a later one still
// refer to an earlier one".
#[test]
fn locals_are_released_in_the_reverse_of_the_order_they_were_bound() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let first = f.slot("first", buf);
    let second = f.slot("second", buf);
    let one = f.call();
    let two = f.call();
    let stmts = vec![f.let_(first, Some(one)), f.let_(second, Some(two))];
    let block = f.block(stmts, None);
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    assert_eq!(releases(&body), vec![second, first]);
}

// "nothing at all where the value was moved away first".
#[test]
fn a_local_that_was_moved_away_is_not_released() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let held = f.slot("held", buf);
    let init = f.call();
    let read = f.local(held);
    let away = f.hands(read);
    let stmts = vec![f.let_(held, Some(init)), f.eval(away)];
    let block = f.block(stmts, None);
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    assert!(releases(&body).is_empty(), "{:?}", releases(&body));
}

// Moved on one path and not the other is neither "release it" nor "leave it",
// and there is no third answer at compile time -- so the program carries one: a
// flag beside the slot, and the release behind a branch on it.
#[test]
fn a_local_moved_on_one_path_is_released_behind_a_flag() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let held = f.slot("held", buf);
    let init = f.call();
    let read = f.local(held);
    let away = f.hands(read);
    let then = f.block(vec![f.eval(away)], None);
    let cond = f.boolean(true);
    let branch = f.if_(cond, then, None);
    let stmts = vec![f.let_(held, Some(init)), f.eval(branch)];
    let block = f.block(stmts, None);
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    // One release, and one branch more than the `if` itself put there.
    assert_eq!(releases(&body), vec![held]);
    assert_eq!(branches(&body), 2);
    // A flag of its own, which is a `bool` nobody wrote.
    assert!(
        body.locals.iter().any(|l| l.synthetic
            && matches!(&l.name, TIRBinding::Name(name) if name.ends_with("$held"))),
        "{:?}",
        body.locals
    );
}

// A slot nothing filled holds nothing, so there is nothing to release: a `let`
// with no initialiser is the shape that says so.
#[test]
fn a_slot_nothing_filled_is_not_released() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let held = f.slot("held", buf);
    let block = f.block(vec![f.let_(held, None)], None);
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    assert!(releases(&body).is_empty(), "{:?}", releases(&body));
}

// A parameter was filled by the caller before the entry block was reached, so
// it is released like anything else the body owns.
#[test]
fn a_parameter_is_released_like_any_other_slot() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let p = f.slot("p", buf);
    let block = f.block(Vec::new(), None);
    let body = f.body(block);
    f.owns(body, vec![p]);

    let body = placed(f);
    assert_eq!(body.params, vec![p]);
    assert_eq!(releases(&body), vec![p]);
}

// And a parameter handed on is a parameter moved away, so it is not released
// twice.
#[test]
fn a_parameter_handed_on_is_not_released() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let p = f.slot("p", buf);
    let read = f.local(p);
    let away = f.hands(read);
    let block = f.block(vec![f.eval(away)], None);
    let body = f.body(block);
    f.owns(body, vec![p]);

    let body = placed(f);
    assert!(releases(&body).is_empty(), "{:?}", releases(&body));
}

// And a slot the `return` hands on is one moved away, for the same reason a
// parameter handed on is: the value goes in a slot before the scope is left,
// so the move stands ahead of where the release was placed and the release is
// what this pass takes away.
#[test]
fn a_slot_the_return_hands_on_is_not_released() {
    let mut f = Fixture::new();
    let buf = f.dropper("Buf");
    let held = f.slot("held", buf);
    let made = f.call();
    let read = f.local(held);
    let away = f.hands(read);
    let ty = f.null;
    let ret = f.expr(TTIRExprKind::Return(Some(away)), ty);
    let block = f.block(
        vec![f.let_(held, Some(made)), TTIRStmt::Expr { is_unsafe: false, expr: ret }],
        None,
    );
    let body = f.body(block);
    f.owns(body, Vec::new());

    let body = placed(f);
    assert!(reached(&body).is_empty(), "{:?}", reached(&body));
}
