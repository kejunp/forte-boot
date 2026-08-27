// Calls written out where they were called, and the ones that are not:
// a fn that can reach itself, and one the source marked `%noinline`.

use super::*;

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
