// What comes out of the frame, what stays in it, and where the phis land.
//
// Each of these goes through `fixture::taken_out`, which runs the lowering and
// then this pass and holds the result to the two rules in `verify.rs`. A phi
// with a missing edge or an operand from the wrong side of a branch is caught
// there rather than by any assertion written below.

use crate::sir::fixture::*;
use crate::sir::sir_nodes::*;
use crate::gir::gir_nodes::GIRTerm;
use crate::tir::tir_nodes::TIRLit;

fn find(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> SIRInst {
    insts(body)
        .into_iter()
        .find(|(_, inst)| want(&inst.kind))
        .map(|(_, inst)| inst)
        .unwrap_or_else(|| panic!("nothing like that in {:#?}", kinds(body)))
}

// What the one call in the body was handed, which is how these tests ask "and
// what does the name hold here".
fn handed(body: &SIRBody) -> SIRValueId {
    let call = find(body, |k| matches!(k, SIRInstKind::Call { args, .. } if !args.is_empty()));
    let SIRInstKind::Call { args, .. } = call.kind else { unreachable!() };
    args[0]
}

// ---- The names that come out ------------------------------------------------

// Written once and read below it: the read is the value the write made, and
// there is nothing left in memory at all.
#[test]
fn a_write_and_a_read_in_one_block_need_no_memory() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, x, one);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert!(body.slots.is_empty(), "{:#?}", body.slots);
    assert!(phis(body).is_empty(), "one path in wants no phi: {:#?}", phis(body));
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Load { .. })), 0);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Store { .. })), 0);

    let lit = find(body, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(1))));
    assert_eq!(handed(body), lit.def.unwrap(), "the read is the literal itself");
}

// Written on both sides of a branch, so the read below has two answers and a
// phi is what says which.
#[test]
fn a_name_written_on_both_sides_of_a_branch_gets_a_phi() {
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

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert!(body.slots.is_empty(), "{:#?}", body.slots);
    let held = phis(body);
    assert_eq!(held.len(), 1, "one name crossing one join: {:#?}", held);
    let (_, phi) = &held[0];
    assert_eq!(phi.edges.len(), 2, "one entry per way in: {:#?}", phi);
    assert_eq!(handed(body), phi.def, "and the read is the phi");

    // The two sides are the two literals, and not the one twice.
    let mut came: Vec<SIRValueId> = phi.edges.iter().map(|(_, v)| *v).collect();
    came.sort();
    came.dedup();
    assert_eq!(came.len(), 2, "{:#?}", phi);
}

// Only where it is needed. A name written above a branch and read below it
// crosses the join with one answer, so nothing is placed.
#[test]
fn a_name_with_one_answer_crosses_a_join_without_a_phi() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let (at, then, els, join) = (f.block(), f.block(), f.block(), f.block());
    let one = f.int(1);
    f.set(at, x, one);
    let cond = f.boolean(true);
    f.term(at, GIRTerm::Branch { cond, then, els });
    f.term(then, GIRTerm::Goto(join));
    f.term(els, GIRTerm::Goto(join));
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(join, hands);
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert!(phis(body).is_empty(), "nothing changed it: {:#?}", phis(body));
    let lit = find(body, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(1))));
    assert_eq!(handed(body), lit.def.unwrap());
}

// A loop's cursor is written before the loop and again on every turn, so the
// test at the head reads two answers -- which is the phi a back edge makes.
#[test]
fn a_loop_head_gets_a_phi_for_what_the_turn_changed() {
    let p = taken_out(walking(false));
    let body = &p.bodies[0];

    let step = find(body, |k| matches!(k, SIRInstKind::IterStep { .. }));
    let SIRInstKind::IterStep { at, .. } = step.kind else { unreachable!() };

    let held = phis(body);
    let cursor = held
        .iter()
        .find(|(_, phi)| phi.def == at)
        .unwrap_or_else(|| panic!("the cursor is not a phi: {:#?}", held));
    assert_eq!(cursor.1.edges.len(), 2, "the way in and the turn: {:#?}", cursor.1);

    // One of them is where it started and the other is the step itself, which
    // is what makes the loop go round rather than stand still.
    let came: Vec<SIRValueId> = cursor.1.edges.iter().map(|(_, v)| *v).collect();
    assert!(came.contains(&step.def.unwrap()), "the turn hands back the step: {:#?}", came);
    let start = find(body, |k| matches!(k, SIRInstKind::IterStart));
    assert!(came.contains(&start.def.unwrap()), "and the way in, where it began");
}

// A parameter is a value already; reading the name is reading what the caller
// handed over, with nothing in between.
#[test]
fn a_read_of_a_parameter_is_the_value_the_caller_handed_over() {
    let mut f = Fixture::new();
    let n = f.param("n", f.int);
    let at = f.block();
    let read = f.read(n);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert!(body.slots.is_empty(), "{:#?}", body.slots);
    assert_eq!(handed(body), body.params[0]);
}

// ---- The names that stay in --------------------------------------------------

// An address that goes anywhere but a load or a store is an address something
// else may write through, so the name stays where it can be written through.
#[test]
fn a_name_whose_address_was_taken_stays_in_the_frame() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, x, one);
    let place = f.read(x);
    let taken = f.addr_of(place);
    let hands = f.hands(taken);
    f.eval(at, hands);
    let read = f.read(x);
    let again = f.hands(read);
    f.eval(at, again);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert_eq!(body.slots.len(), 1, "the name is still somewhere: {:#?}", body.slots);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Store { .. })), 1);
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Load { .. })),
        1,
        "and reading it is still going and looking: {:#?}",
        kinds(body)
    );
}

// One name out and one name in, in the one body: the rule is per slot and not
// per body.
#[test]
fn one_name_staying_in_does_not_keep_the_others() {
    let mut f = Fixture::new();
    let held = f.local("held", f.int);
    let free = f.local("free", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, held, one);
    let two = f.int(2);
    f.set(at, free, two);
    let place = f.read(held);
    let taken = f.addr_of(place);
    let hands = f.hands(taken);
    f.eval(at, hands);
    let read = f.read(free);
    let again = f.hands(read);
    f.eval(at, again);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert_eq!(body.slots.len(), 1, "{:#?}", body.slots);
    assert_eq!(body.slots[0].name, crate::tir::tir_nodes::TIRBinding::Name("held".to_string()));
}

// ---- Reading what was never written ------------------------------------------

// `let x: T;` and then a read of it. Nothing here refuses that -- `sema` is
// where it is refused -- and inventing a zero would be answering a question
// this pass was not asked.
#[test]
fn a_read_of_a_name_nothing_wrote_is_undef() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    let undef = find(body, |k| matches!(k, SIRInstKind::Undef));
    assert_eq!(handed(body), undef.def.unwrap());
}

// And where every path wrote it first, no `Undef` is left standing: one would
// say there is a path that reads it unwritten, and there is not.
#[test]
fn a_name_always_written_first_leaves_no_undef_behind() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, x, one);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Undef)), 0, "{:#?}", kinds(body));
}

// ---- Releases ----------------------------------------------------------------

// A promoted name is released as the value it is. Loading it first would
// release a copy and leave the original.
#[test]
fn releasing_a_promoted_name_releases_the_value() {
    let mut f = Fixture::new();
    let x = f.dropping("x", f.null);
    let at = f.block();
    let made = f.call();
    f.set(at, x, made);
    f.release(at, x);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::DropSlot(_))), 0);
    let released = find(body, |k| matches!(k, SIRInstKind::Drop(_)));
    let SIRInstKind::Drop(value) = released.kind else { unreachable!() };
    let call = find(body, |k| matches!(k, SIRInstKind::Call { args, .. } if args.is_empty()));
    assert_eq!(value, call.def.unwrap(), "what the call made is what goes");
}

// A name that stayed in the frame is released where it stands.
#[test]
fn releasing_a_name_still_in_the_frame_releases_the_slot() {
    let mut f = Fixture::new();
    let x = f.dropping("x", f.null);
    let at = f.block();
    let made = f.call();
    f.set(at, x, made);
    let place = f.read(x);
    let taken = f.addr_of(place);
    let hands = f.hands(taken);
    f.eval(at, hands);
    f.release(at, x);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Drop(_))), 0);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::DropSlot(0))), 1, "{:#?}", kinds(body));
}

// ---- What is not reached ------------------------------------------------------

// A block nothing reaches is not a use. A release standing in one would name a
// slot that the renumbering has taken away, and an address escaping in one
// would keep a name in the frame that nothing reads.
#[test]
fn a_block_nothing_reaches_holds_nothing_this_pass_answers_for() {
    let mut f = Fixture::new();
    let x = f.dropping("x", f.null);
    let (at, gone) = (f.block(), f.block());
    let made = f.call();
    f.set(at, x, made);
    f.release(at, x);
    f.term(at, GIRTerm::Return(None));

    // Nothing goes to `gone`, and it takes the address of `x` and releases it.
    let place = f.read(x);
    let taken = f.addr_of(place);
    let hands = f.hands(taken);
    f.eval(gone, hands);
    f.release(gone, x);
    f.term(gone, GIRTerm::Return(None));
    f.body(at);

    let p = taken_out(f);
    let body = &p.bodies[0];

    assert!(body.slots.is_empty(), "the address never escapes: {:#?}", body.slots);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Drop(_))), 1);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::DropSlot(_))), 0);
}
