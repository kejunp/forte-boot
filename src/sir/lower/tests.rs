// What the GIR becomes: the trees flattened, the two whole terminators written
// out, and every name in a slot for `sir::promote` to take back out.
//
// Every one of these goes through `fixture::built`, which holds what came out
// to the two rules in `verify.rs`. So a test that asserts one thing about one
// instruction is also asserting that the body around it is in SSA form.

use crate::sir::fixture::*;
use crate::sir::sir_nodes::*;
use crate::gir::gir_nodes::{GIRArm, GIRTerm};
use crate::tir::tir_nodes::{TIRAssignOp, TIRBinOp, TIRLit};
use crate::tir::ttir_nodes::TTIRPatKind;

// Which block an instruction answering `want` stands in, and what it is.
fn find(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> (SIRBlockId, SIRInst) {
    insts(body)
        .into_iter()
        .find(|(_, inst)| want(&inst.kind))
        .unwrap_or_else(|| panic!("nothing like that in {:#?}", kinds(body)))
}

fn is_eq(kind: &SIRInstKind) -> bool {
    matches!(kind, SIRInstKind::Binary { op: TIRBinOp::Eq, .. })
}

// ---- Flattening -------------------------------------------------------------

// `a + b` is the two reads and then the operator, in that order, and the
// operator reads what the two of them made.
#[test]
fn an_expression_tree_becomes_the_line_that_built_it() {
    let mut f = Fixture::new();
    let (int, a, b) = (f.int, f.local("a", f.int), f.local("b", f.int));
    let c = f.local("c", int);
    let at = f.block();
    let (ra, rb) = (f.read(a), f.read(b));
    let sum = f.add(ra, rb);
    f.set(at, c, sum);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let held = kinds(body);
    let (_, add) = find(body, |k| matches!(k, SIRInstKind::Binary { op: TIRBinOp::Add, .. }));
    let SIRInstKind::Binary { lhs, rhs, .. } = add.kind else { unreachable!() };

    // Both operands are loads, and both loads stand above the operator.
    let loads: Vec<SIRValueId> = insts(body)
        .iter()
        .filter(|(_, i)| matches!(i.kind, SIRInstKind::Load { .. }))
        .filter_map(|(_, i)| i.def)
        .collect();
    assert!(loads.contains(&lhs) && loads.contains(&rhs), "{:#?}", held);
    assert_ne!(lhs, rhs, "two names are two values");
}

// Reading a name is reading its slot, and there is a slot for every one.
#[test]
fn every_name_starts_in_the_frame() {
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

    let p = built(f);
    let body = &p.bodies[0];
    assert_eq!(body.slots.len(), 1, "{:#?}", body.slots);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Store { .. })), 1);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Load { .. })), 1);
}

// A parameter is made by nobody and put where the body reads names from.
#[test]
fn a_parameter_is_stored_into_its_slot_before_anything_runs() {
    let mut f = Fixture::new();
    let n = f.param("n", f.int);
    let at = f.block();
    let read = f.read(n);
    f.term(at, GIRTerm::Return(Some(read)));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    assert_eq!(body.params.len(), 1);
    let param = body.params[0];
    let entry = &body.blocks[body.entry];
    assert!(
        entry.insts.iter().any(|i| matches!(i.kind, SIRInstKind::Store { value, .. }
                                            if value == param)),
        "{:#?}",
        entry.insts
    );
}

// `x += 1` reads the place, adds, and writes it back -- and reads the place
// rather than a copy taken from somewhere else.
#[test]
fn a_compound_assignment_reads_before_it_writes() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let place = f.read(x);
    let one = f.int(1);
    f.store(at, place, TIRAssignOp::Add, one);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let (_, add) = find(body, |k| matches!(k, SIRInstKind::Binary { op: TIRBinOp::Add, .. }));
    let SIRInstKind::Binary { lhs, .. } = add.kind else { unreachable!() };
    let (_, load) = find(body, |k| matches!(k, SIRInstKind::Load { .. }));
    assert_eq!(Some(lhs), load.def, "the left side is what was read out");

    let (_, store) = find(body, |k| matches!(k, SIRInstKind::Store { .. }));
    let (SIRInstKind::Store { to, value }, SIRInstKind::Load { from }) =
        (&store.kind, &load.kind)
    else {
        unreachable!()
    };
    assert_eq!(to, from, "read and written through the one address");
    assert_eq!(Some(*value), add.def, "and what is written is the sum");
}

// `&x` and the address of `x` are the same instruction; the type is all that
// differs, and the source gave that.
#[test]
fn taking_a_reference_is_taking_the_address() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let place = f.read(x);
    let taken = f.addr_of(place);
    let hands = f.hands(taken);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let (_, addr) = find(body, |k| matches!(k, SIRInstKind::Addr(0)));
    let (_, call) = find(body, |k| matches!(k, SIRInstKind::Call { .. }));
    let SIRInstKind::Call { args, .. } = call.kind else { unreachable!() };
    assert_eq!(args, vec![addr.def.unwrap()], "the address is what was handed over");
}

// ---- What a match becomes ---------------------------------------------------

#[test]
fn a_match_becomes_tests_and_branches() {
    let mut f = Fixture::new();
    let s = f.local("s", f.int);
    let (at, one, two, join) = (f.block(), f.block(), f.block(), f.block());
    let read = f.read(s);
    let (p1, p2) = (f.lit_pat(1), f.lit_pat(2));
    f.term(at, GIRTerm::Match {
        scrutinee: read,
        arms:      vec![GIRArm { pats: vec![p1], block: one },
                        GIRArm { pats: vec![p2], block: two }],
        otherwise: Some(join),
    });
    f.term(one, GIRTerm::Goto(join));
    f.term(two, GIRTerm::Goto(join));
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    assert_eq!(count(body, is_eq), 2, "one test per arm: {:#?}", kinds(body));
    let branches = body
        .blocks
        .iter()
        .filter(|b| matches!(b.term, SIRTerm::Branch { .. }))
        .count();
    assert_eq!(branches, 2, "and one branch per test");
}

// The first arm written is the first arm tried, because the first arm that
// takes it is the one that runs.
#[test]
fn the_arms_are_tried_in_the_order_they_were_written() {
    let mut f = Fixture::new();
    let s = f.local("s", f.int);
    let (at, one, two, join) = (f.block(), f.block(), f.block(), f.block());
    let read = f.read(s);
    let (p7, p3) = (f.lit_pat(7), f.lit_pat(3));
    f.term(at, GIRTerm::Match {
        scrutinee: read,
        arms:      vec![GIRArm { pats: vec![p7], block: one },
                        GIRArm { pats: vec![p3], block: two }],
        otherwise: Some(join),
    });
    f.term(one, GIRTerm::Goto(join));
    f.term(two, GIRTerm::Goto(join));
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let order: Vec<i64> = kinds(body)
        .iter()
        .filter_map(|k| match k {
            SIRInstKind::Literal(TIRLit::Int(n)) => Some(*n),
            _ => None,
        })
        .collect();
    assert_eq!(order, vec![7, 3], "7 was written first and is tested first");
}

// A variant is told by its discriminant, and the number compared against is
// the one the checker gave the variant -- not where it stands in the list.
#[test]
fn a_variant_is_told_by_the_number_the_checker_gave_it() {
    let mut f = Fixture::new();
    let held = f.enumeration(&[5, 9]);
    let s = f.local("s", f.int);
    let (at, arm, join) = (f.block(), f.block(), f.block());
    let read = f.read(s);
    let ty = f.int;
    let pat = f.pat(TTIRPatKind::Variant { item: held, variant: 1, elems: Vec::new() }, ty);
    f.term(at, GIRTerm::Match {
        scrutinee: read,
        arms:      vec![GIRArm { pats: vec![pat], block: arm }],
        otherwise: Some(join),
    });
    f.term(arm, GIRTerm::Goto(join));
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    find(body, |k| matches!(k, SIRInstKind::Discriminant(_)));
    assert!(
        kinds(body).iter().any(|k| matches!(k, SIRInstKind::Literal(TIRLit::Int(9)))),
        "the second variant is 9 and not 1: {:#?}",
        kinds(body)
    );
}

// Half a pattern may match and the whole of it still fail, so nothing is
// bound where the testing is done -- only past it.
#[test]
fn a_name_is_bound_only_where_the_whole_pattern_took() {
    let mut f = Fixture::new();
    let s = f.local("s", f.int);
    let x = f.local("x", f.int);
    let (at, arm, join) = (f.block(), f.block(), f.block());
    let read = f.read(s);
    let (lit, bind) = (f.lit_pat(1), f.bind_pat(x));
    let ty = f.int;
    let pat = f.pat(TTIRPatKind::Tuple(vec![lit, bind]), ty);
    f.term(at, GIRTerm::Match {
        scrutinee: read,
        arms:      vec![GIRArm { pats: vec![pat], block: arm }],
        otherwise: Some(join),
    });
    f.term(arm, GIRTerm::Goto(join));
    f.term(join, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let (tested, _) = find(body, is_eq);
    // The slot `x` went in is the second, locals being made in order.
    let addrs: Vec<SIRValueId> = insts(body)
        .iter()
        .filter(|(_, i)| matches!(i.kind, SIRInstKind::Addr(1)))
        .filter_map(|(_, i)| i.def)
        .collect();
    let (bound, _) = find(body, |k| match k {
        SIRInstKind::Store { to, .. } => addrs.contains(to),
        _ => false,
    });
    assert_ne!(bound, tested, "the binding does not stand in the block that tested");
}

// ---- What a for becomes -----------------------------------------------------

// A loop over a cursor, and one of each question the walk asks.
#[test]
fn a_for_becomes_a_cursor_and_a_loop() {
    let p = built(walking(false));
    let body = &p.bodies[0];

    assert_eq!(count(body, |k| matches!(k, SIRInstKind::IterStart)), 1);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::IterStep { .. })), 1);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::IterValid { .. })), 1);
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::IterElem { .. })), 1);
}

// The cursor is put back before the first only on the way in. If a turn of the
// loop reached the pre-header the cursor would be reset every time and the
// loop would never end.
#[test]
fn the_cursor_is_put_back_only_on_the_way_in() {
    let p = built(walking(false));
    let body = &p.bodies[0];

    let (before, _) = find(body, |k| matches!(k, SIRInstKind::IterStart));
    let (head, _) = find(body, |k| matches!(k, SIRInstKind::IterStep { .. }));
    assert_eq!(
        body.blocks[before].term,
        SIRTerm::Goto(head),
        "the pre-header does nothing but lead into the test"
    );

    let preds = body.preds();
    assert_eq!(preds[before].len(), 1, "and is reached only from outside");
    assert_eq!(preds[head].len(), 2, "while the test is reached by both");
}

// A `continue` is a turn of the loop and goes where a turn goes.
#[test]
fn a_continue_goes_to_the_test_and_not_to_the_way_in() {
    let p = built(walking(true));
    let body = &p.bodies[0];

    let (before, _) = find(body, |k| matches!(k, SIRInstKind::IterStart));
    let (head, _) = find(body, |k| matches!(k, SIRInstKind::IterStep { .. }));
    let preds = body.preds();

    assert_eq!(preds[before].len(), 1, "still only the one way in");
    assert_eq!(preds[head].len(), 3, "the way in, the bottom, and the continue");
}

// ---- Releases ---------------------------------------------------------------

// Where the GIR put them, still. Which releases run was settled on the graph,
// and this pass does not ask it again.
#[test]
fn a_release_is_carried_through_where_it_stood() {
    let mut f = Fixture::new();
    let x = f.dropping("x", f.null);
    let at = f.block();
    let call = f.call();
    f.set(at, x, call);
    f.release(at, x);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::DropSlot(_))), 1, "{:#?}", kinds(body));
}

// A closure keeps the number its body had, so that following one still lands
// on the graph it always landed on.
#[test]
fn a_closure_still_points_at_the_body_it_pointed_at() {
    let mut f = Fixture::new();
    let inner = f.block();
    f.term(inner, GIRTerm::Return(None));
    let held = f.body(inner);

    let outer = f.block();
    let ty = f.null;
    let made = f.expr(
        crate::gir::gir_nodes::GIRExprKind::Closure { captures: Vec::new(), body: held },
        ty,
    );
    f.eval(outer, made);
    f.term(outer, GIRTerm::Return(None));
    f.body(outer);

    let p = built(f);
    assert_eq!(p.bodies.len(), 2);
    let (_, closure) = find(&p.bodies[1], |k| matches!(k, SIRInstKind::Closure { .. }));
    let SIRInstKind::Closure { body, .. } = closure.kind else { unreachable!() };
    assert_eq!(body, held, "the same number the GIR gave it");
}
