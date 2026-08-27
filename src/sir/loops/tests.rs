// What is found in a graph that has a loop in it, and what is not found in one
// that has not.
//
// Every fixture here goes through `fixture::built`, so the body these are
// asked about is one the lowering actually makes and one `verify` has already
// agreed is in SSA form.

use crate::gir::gir_nodes::GIRTerm;
use crate::sir::dom::Dominators;
use crate::sir::fixture::*;
use crate::sir::loops::*;
use crate::sir::sir_nodes::*;

fn found(body: &SIRBody) -> Vec<Loop> {
    Loop::all(body, &Dominators::of(body))
}

// `while c { }`: one way in, one way round, one way out.
#[test]
fn a_loop_is_its_head_and_what_goes_back_to_it() {
    let mut f = Fixture::new();
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let cond = f.read(c);
    f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let p = built(f);
    let body = &p.bodies[0];
    let held = found(body);

    assert_eq!(held.len(), 1, "{:#?}", held.iter().map(|l| l.head).collect::<Vec<_>>());
    assert_eq!(held[0].blocks.len(), 2, "the head and the body: {:?}", held[0].blocks);
    assert_eq!(held[0].blocks[0], held[0].head, "the head is named first");
    assert_eq!(held[0].back.len(), 1);
    assert_eq!(held[0].entries.len(), 1);
    assert!(held[0].has(held[0].head));
}

// Two ways round is still one loop. A `continue` closes a second back edge
// into the same head, and a pass that took that for two loops would lift the
// same instruction out of it twice.
#[test]
fn two_ways_round_one_head_are_one_loop() {
    let p = built(walking(true));
    let body = &p.bodies[0];
    let held = found(body);

    assert_eq!(held.len(), 1, "{:#?}", held.iter().map(|l| l.head).collect::<Vec<_>>());
    assert_eq!(held[0].back.len(), 2, "{:?}", held[0].back);
}

// A loop inside a loop is two, and the tighter of them is given first.
#[test]
fn a_loop_inside_a_loop_is_two_of_them_innermost_first() {
    let mut f = Fixture::new();
    let c = f.param("c", f.bool);
    let (before, outer, inner, deep, after, exit) =
        (f.block(), f.block(), f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(outer));
    let cond = f.read(c);
    f.term(outer, GIRTerm::Branch { cond, then: inner, els: exit });
    let cond = f.read(c);
    f.term(inner, GIRTerm::Branch { cond, then: deep, els: after });
    f.term(deep, GIRTerm::Goto(inner));
    f.term(after, GIRTerm::Goto(outer));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let p = built(f);
    let body = &p.bodies[0];
    let held = found(body);

    assert_eq!(held.len(), 2, "{:#?}", held.iter().map(|l| l.head).collect::<Vec<_>>());
    assert!(held[0].blocks.len() < held[1].blocks.len(), "the tighter one first");
    // And the one outside holds everything the one inside does.
    for &at in &held[0].blocks {
        assert!(held[1].has(at), "b{} is in the inner loop and not the outer", at);
    }
}

// A graph with no edge going back to anywhere has nothing here to find.
#[test]
fn a_straight_line_holds_no_loops() {
    let mut f = Fixture::new();
    let (at, next) = (f.block(), f.block());
    f.term(at, GIRTerm::Goto(next));
    f.term(next, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    assert!(found(&p.bodies[0]).is_empty());
}

// ---- The block above the head -----------------------------------------------

// A block that goes to the head and nowhere else is already one, and is handed
// back rather than a second being put in front of it.
#[test]
fn a_block_that_only_goes_to_the_head_is_the_preheader() {
    let mut f = Fixture::new();
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let cond = f.read(c);
    f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let mut p = built(f);
    let body = &mut p.bodies[0];
    let held = found(body);
    let was = body.blocks.len();

    let pre = preheader(body, &held[0]).expect("one way in");
    assert_eq!(body.blocks.len(), was, "nothing was made");
    assert_eq!(pre, held[0].entries[0]);
    sound(&p);
}

// And a block that goes two ways is not one, so a block that goes one way is
// put between it and the head.
#[test]
fn a_branch_into_a_loop_gets_a_preheader_made_for_it() {
    let mut f = Fixture::new();
    let c = f.param("c", f.bool);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    let cond = f.read(c);
    // One arm of the branch is the loop and the other is not, so the block
    // above the head ends in two edges and cannot hold anything of the loop's.
    f.term(before, GIRTerm::Branch { cond, then: head, els: exit });
    let cond = f.read(c);
    f.term(head, GIRTerm::Branch { cond, then: inner, els: exit });
    f.term(inner, GIRTerm::Goto(head));
    f.term(exit, GIRTerm::Return(None));
    f.body(before);

    let mut p = built(f);
    let body = &mut p.bodies[0];
    let held = found(body);
    let was = body.blocks.len();

    let pre = preheader(body, &held[0]).expect("one way in");
    assert_eq!(body.blocks.len(), was + 1, "a block was made");
    assert_eq!(body.blocks[pre].term, SIRTerm::Goto(held[0].head));
    assert_eq!(
        body.preds()[held[0].head].iter().filter(|&&at| at != pre).count(),
        held[0].back.len(),
        "everything but the ways round comes through it now"
    );
    sound(&p);
}
