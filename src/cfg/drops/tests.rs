// Where a release goes, and which ones run.

use super::*;
use crate::cfg::fixture::Fixture;
use crate::cfg::lower::Lowerer;

// A fixture through both passes, and the body they made of it.
fn placed(f: Fixture) -> CFGBody {
    let ttir = f.p;
    let mut l = Lowerer::new(&ttir);
    l.lower();
    let mut cfg = l.finish();
    let copies = Copies::of(&ttir);
    let generics: Vec<Vec<TTIRGeneric>> = vec![Vec::new(); cfg.bodies.len()];
    Drops::new(&ttir, &copies).place(&mut cfg, &generics);
    cfg.bodies[0].clone()
}

// Every release the body holds, as `(local, guarded)`, in the order the blocks
// were built -- which is the order they were written.
fn releases(body: &CFGBody) -> Vec<(CFGLocalId, bool)> {
    body.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s.kind {
            CFGStmtKind::Drop { local, guarded } => Some((local, guarded)),
            _ => None,
        })
        .collect()
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
    assert_eq!(releases(&body), vec![(held, false)]);
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
    assert_eq!(releases(&body), vec![(second, false), (first, false)]);
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

// Moved on one path and not the other is neither, and what stands is a release
// with a flag beside it.
#[test]
fn a_local_moved_on_one_path_is_released_with_a_flag() {
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
    assert_eq!(releases(&body), vec![(held, true)]);
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
    assert_eq!(releases(&body), vec![(p, false)]);
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
