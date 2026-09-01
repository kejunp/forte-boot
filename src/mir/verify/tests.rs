// A body that is right, and then one broken in each of the ways that matter.
//
// The tests that assert a *correct* body passes are as much of this as the ones
// that assert a broken one is caught. A verifier that says everything is wrong
// is as useless as one that says nothing is, and it is the first kind that goes
// unnoticed -- nothing fails, and every test of every other pass starts
// reporting the same complaint.

use super::super::fixture::*;
use super::*;

// What a complaint has to mention to be worth printing.
fn says(wrong: &[String], about: &str) -> bool {
    wrong.iter().any(|said| said.contains(about))
}

// ---- The bodies that are right ---------------------------------------------

#[test]
fn a_straight_body_is_well_formed() {
    let mut f = Fixture::new();
    let at = f.block();
    let (a, b) = (f.int(at, 1), f.int(at, 2));
    let sum = f.add(at, a, b);
    f.term(at, MIRTerm::Return(Some(sum)));
    let body = f.body(at);
    assert!(verify(&body).is_empty(), "{:#?}", verify(&body));
    assert!(verify_order(&body).is_empty(), "{:#?}", verify_order(&body));
}

#[test]
fn a_phi_naming_both_ways_in_is_well_formed() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (els, b)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let body = f.body(entry);
    assert!(verify(&body).is_empty(), "{:#?}", verify(&body));
}

// A parameter is made by the caller and by no instruction, which is the one
// register with no def site and has to be allowed for rather than tripped over.
#[test]
fn a_parameter_is_made_by_nothing_and_is_still_made() {
    let mut f = Fixture::new();
    let x = f.param();
    let at = f.block();
    let one = f.int(at, 1);
    let sum = f.add(at, x, one);
    f.term(at, MIRTerm::Return(Some(sum)));
    let body = f.body(at);
    assert!(verify(&body).is_empty(), "{:#?}", verify(&body));
}

// A block nothing reaches is still in the arena -- nothing here shrinks one --
// so whatever is written in it is not held to anything.
#[test]
fn a_block_nothing_reaches_is_not_complained_about() {
    let mut f = Fixture::new();
    let (at, orphan) = (f.block(), f.block());
    let one = f.int(at, 1);
    f.term(at, MIRTerm::Return(Some(one)));
    // Reads a register made nowhere, in a block nothing enters.
    let ghost = f.reg();
    f.effect(orphan, MIRInstKind::Store { to: ghost, value: ghost, bytes: 8 });
    f.term(orphan, MIRTerm::Unreachable);
    let body = f.body(at);
    assert!(verify(&body).is_empty(), "{:#?}", verify(&body));
}

// ---- Made once -------------------------------------------------------------

#[test]
fn a_register_made_twice_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    let twice = f.reg();
    f.making(at, twice, MIRInstKind::Const(MIRConst::Int(1)));
    f.making(at, twice, MIRInstKind::Const(MIRConst::Int(2)));
    f.term(at, MIRTerm::Return(Some(twice)));
    let body = f.body(at);
    assert!(says(&verify(&body), "made more than once"), "{:#?}", verify(&body));
}

// Two blocks writing one register is the same mistake spread out, and it is the
// one a rewrite makes: the thing that made it was copied and the register it
// makes was not renamed.
#[test]
fn a_register_made_in_two_blocks_is_caught() {
    let (mut f, [entry, then, els, join]) = diamond();
    let twice = f.reg();
    f.making(then, twice, MIRInstKind::Const(MIRConst::Int(1)));
    f.making(els, twice, MIRInstKind::Const(MIRConst::Int(2)));
    f.term(join, MIRTerm::Return(Some(twice)));
    let body = f.body(entry);
    assert!(says(&verify(&body), "made more than once"), "{:#?}", verify(&body));
}

#[test]
fn a_register_nothing_makes_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    let never = f.reg();
    let one = f.int(at, 1);
    let sum = f.add(at, one, never);
    f.term(at, MIRTerm::Return(Some(sum)));
    let body = f.body(at);
    assert!(says(&verify(&body), "which nothing makes"), "{:#?}", verify(&body));
}

// ---- Every name reaches something ------------------------------------------

#[test]
fn a_register_outside_the_arena_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    let one = f.int(at, 1);
    f.effect(at, MIRInstKind::Store { to: one, value: 99, bytes: 8 });
    f.term(at, MIRTerm::Return(None));
    let body = f.body(at);
    assert!(says(&verify(&body), "not in the arena"), "{:#?}", verify(&body));
}

#[test]
fn a_slot_outside_the_frame_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    f.push(at, MIRInstKind::Frame(7));
    f.term(at, MIRTerm::Return(None));
    let body = f.body(at);
    assert!(says(&verify(&body), "not in the frame"), "{:#?}", verify(&body));
}

#[test]
fn an_edge_to_a_block_that_is_not_there_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    f.term(at, MIRTerm::Goto(9));
    let body = f.body(at);
    assert!(says(&verify(&body), "not in the arena"), "{:#?}", verify(&body));
}

#[test]
fn an_entry_that_is_not_there_is_caught() {
    let f = Fixture::new();
    let body = f.body(3);
    assert!(says(&verify(&body), "the entry"), "{:#?}", verify(&body));
}

// ---- What a phi has to say -------------------------------------------------

#[test]
fn a_phi_missing_a_way_in_is_caught() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let _ = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let body = f.body(entry);
    assert!(says(&verify(&body), "the ways in are"), "{:#?}", verify(&body));
}

#[test]
fn a_phi_naming_a_block_that_does_not_reach_it_is_caught() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (entry, b)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let body = f.body(entry);
    assert!(says(&verify(&body), "the ways in are"), "{:#?}", verify(&body));
}

// A phi's operand arrives along the edge, so what has to stand before it is the
// predecessor -- not the block the phi is in. One made in a sibling of the
// predecessor never arrives at all, and that is what this catches.
#[test]
fn a_phi_reading_down_the_wrong_edge_is_caught() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    // `a` is made in `then` and named as what came along `els`.
    let joined = f.phi(join, vec![(then, b), (els, a)]);
    f.term(join, MIRTerm::Return(Some(joined)));
    let body = f.body(entry);
    assert!(says(&verify(&body), "does not reach it"), "{:#?}", verify(&body));
}

// ---- And a read only where what it reads has been made ---------------------

// The mistake every rewrite over a graph can make: a value made down one arm
// and read after the join, where the other arm never made it.
#[test]
fn a_read_of_something_made_down_one_arm_only_is_caught() {
    let (mut f, [entry, then, _els, join]) = diamond();
    let a = f.int(then, 1);
    f.term(join, MIRTerm::Return(Some(a)));
    let body = f.body(entry);
    assert!(says(&verify(&body), "does not reach it"), "{:#?}", verify(&body));
}

// Made before the branch, so both arms have it and so does everything after.
#[test]
fn a_read_of_something_made_before_the_branch_is_fine() {
    let (mut f, [entry, _then, _els, join]) = diamond();
    let a = f.int(entry, 1);
    f.term(join, MIRTerm::Return(Some(a)));
    let body = f.body(entry);
    assert!(verify(&body).is_empty(), "{:#?}", verify(&body));
}

// ---- Order within a block --------------------------------------------------

// Dominance says nothing about this: a block stands between itself and the
// entry, so a read above the thing that makes it is well formed by that rule
// and is still nonsense.
#[test]
fn a_read_above_the_instruction_that_makes_it_is_caught() {
    let mut f = Fixture::new();
    let at = f.block();
    let later = f.reg();
    let one = f.int(at, 1);
    let sum = f.add(at, one, later);
    f.making(at, later, MIRInstKind::Const(MIRConst::Int(2)));
    f.term(at, MIRTerm::Return(Some(sum)));
    let body = f.body(at);
    assert!(verify(&body).is_empty(), "dominance is happy: {:#?}", verify(&body));
    assert!(
        says(&verify_order(&body), "above the instruction"),
        "{:#?}",
        verify_order(&body)
    );
}

// A phi is read before the block begins, so everything in the block may read it
// however far up it stands.
#[test]
fn an_instruction_may_read_a_phi_of_its_own_block() {
    let (mut f, [entry, then, els, join]) = diamond();
    let a = f.int(then, 1);
    let b = f.int(els, 2);
    let joined = f.phi(join, vec![(then, a), (els, b)]);
    let doubled = f.add(join, joined, joined);
    f.term(join, MIRTerm::Return(Some(doubled)));
    let body = f.body(entry);
    assert!(verify_order(&body).is_empty(), "{:#?}", verify_order(&body));
}

// ---- What the fixture itself has to be -------------------------------------

// Everything else here leans on the fixture building something sound, so that
// a failure elsewhere is about the rule and not about the scaffolding.
#[test]
fn the_diamond_the_fixture_builds_is_sound() {
    let (f, [entry, ..]) = diamond();
    sound(&f.program(entry));
}
