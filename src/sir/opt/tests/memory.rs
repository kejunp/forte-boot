// Loads answered by the store above them, and stores nothing will ever read.

use super::*;

// Written and then read back: the read is the value that was written, and the
// read itself goes.
//
// The address is handed away first, which is what keeps the name in the frame
// -- `sir::promote` would otherwise have taken it out and answered the read
// long before this pass saw it. Every one of these does that or something like
// it, because a name still reached by loads and stores is by definition one
// that pass gave up on.
#[test]
fn a_load_below_a_store_to_one_place_is_what_the_store_wrote() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let seven = f.int(7);
    f.set(at, x, seven);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    // The last of the calls, the first being the one the address went out in.
    let read = *all_handed(body).last().expect("something was handed something");
    assert_eq!(literal(body, read), TIRLit::Int(7), "{:#?}", kinds(body));
}

// A write to another name is a write somewhere else, so it does not stop it.
#[test]
fn a_write_to_another_name_does_not_stop_it() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let y = f.local("y", f.int);
    let at = f.block();
    for name in [x, y] {
        let read = f.read(name);
        let addr = f.addr_of(read);
        let hands = f.hands(addr);
        f.eval(at, hands);
    }
    let seven = f.int(7);
    f.set(at, x, seven);
    let eight = f.int(8);
    f.set(at, y, eight);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    let read = *all_handed(body).last().expect("something was handed something");
    assert_eq!(literal(body, read), TIRLit::Int(7), "{:#?}", kinds(body));
}

// And not across a call, where the name is one whose address went out: what
// the call does through it is not this pass's to guess.
#[test]
fn a_call_between_them_ends_what_is_known_of_a_name_that_got_out() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let seven = f.int(7);
    f.set(at, x, seven);
    let call = f.call();
    f.eval(at, call);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(stats.forwarded, 0, "{:#?}", stats);
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Load { .. })) > 0,
        "the read is still a read: {:#?}",
        kinds(body)
    );
}

// A name nothing let out is one the call cannot have reached, so what was
// written to it is still what is there afterwards. Here it is a field written
// to that keeps the name in the frame, and stepping into a name is not letting
// it out -- which is the whole of what `sir::alias` adds over `sir::promote`.
#[test]
fn a_call_leaves_alone_what_it_could_not_have_reached() {
    let mut f = Fixture::new();
    let xs = f.local("xs", f.int);
    let at = f.block();
    let ty = f.int;
    let base = f.read(xs);
    let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
    let one = f.int(1);
    f.store(at, field, TIRAssignOp::Set, one);
    let five = f.int(5);
    f.set(at, xs, five);
    let call = f.call();
    f.eval(at, call);
    let read = f.read(xs);
    let hands = f.hands(read);
    f.eval(at, hands);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, stats) = worked(f);
    let body = &out.bodies[0];

    assert!(stats.forwarded > 0, "{:#?}", stats);
    assert_eq!(literal(body, handed(body)), TIRLit::Int(5), "{:#?}", kinds(body));
}

// The same rewrite from source, over the one shape the lowering leaves a load
// in: a name whose address was handed away, so `sir::promote` could not take
// it out of the frame.
//
// The call is `%noinline` because the alternative is the better answer -- with
// the body written out, nothing holds the address any more and the name comes
// out of the frame altogether, which is `promote` answering the question
// before this pass is asked it.
#[test]
fn a_name_whose_address_went_out_is_still_read_back_as_what_was_written() {
    let (p, stats) = compiled(
        "%noinline\n\
         fn sink(p: &i32): null { null }\n\
         fn kept(): i32 { var x: i32 = 0; sink(&x); x = 7; x }\n",
    );

    assert_eq!(stats.forwarded, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Load { .. })),
        0,
        "the read is the value the write wrote: {:#?}",
        kinds(body)
    );
    let handed = body
        .blocks
        .iter()
        .find_map(|block| match block.term {
            SIRTerm::Return(Some(value)) => Some(value),
            _ => None,
        })
        .expect("something is given back");
    assert_eq!(literal(body, handed), TIRLit::Int(7), "{:#?}", kinds(body));
    // And the store stays: the address went out, so something else may read
    // what is there.
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Store { .. })), 2, "{:#?}", kinds(body));
}

// ---- Stores nothing will read -----------------------------------------------

// Written twice with nothing between: the first write is one nobody could have
// seen the result of.
#[test]
fn a_store_written_over_before_anything_reads_it_goes() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let one = f.int(1);
    f.set(at, x, one);
    let two = f.int(2);
    f.set(at, x, two);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, _) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Store { .. })),
        1,
        "one write where there were two: {:#?}",
        kinds(body)
    );
}

// Unless something between may read it. A read of the name is the plain case;
// a call is the case that needs to know whether the name ever got out.
#[test]
fn a_read_between_them_keeps_the_first_write() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let at = f.block();
    let read = f.read(x);
    let addr = f.addr_of(read);
    let hands = f.hands(addr);
    f.eval(at, hands);
    let one = f.int(1);
    f.set(at, x, one);
    let read = f.read(x);
    let hands = f.hands(read);
    f.eval(at, hands);
    let two = f.int(2);
    f.set(at, x, two);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let (out, _) = worked(f);
    let body = &out.bodies[0];

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "{:#?}",
        kinds(body)
    );
}

// A call between them reads it if it could have reached it, and not if it
// could not -- the same question, and the same answer, as everywhere else.
#[test]
fn a_call_between_them_keeps_the_first_write_only_if_it_could_read_it() {
    let build = |lets_out: bool| {
        let mut f = Fixture::new();
        let x = f.local("x", f.int);
        let at = f.block();
        if lets_out {
            let read = f.read(x);
            let addr = f.addr_of(read);
            let hands = f.hands(addr);
            f.eval(at, hands);
        } else {
            // Something else that keeps the name in the frame without letting
            // it out, so that there is still a store here to have an opinion
            // about.
            let ty = f.int;
            let base = f.read(x);
            let field = f.expr(GIRExprKind::Field { base, index: 0 }, ty);
            let nine = f.int(9);
            f.store(at, field, TIRAssignOp::Set, nine);
        }
        let one = f.int(1);
        f.set(at, x, one);
        let call = f.call();
        f.eval(at, call);
        let two = f.int(2);
        f.set(at, x, two);
        f.term(at, GIRTerm::Return(None));
        f.body(at);
        worked(f).0
    };

    let open = build(true);
    assert_eq!(
        count(&open.bodies[0], |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "the call may read what was written: {:#?}",
        kinds(&open.bodies[0])
    );

    let shut = build(false);
    // The write to the field, and one of the two to the name.
    assert_eq!(
        count(&shut.bodies[0], |k| matches!(k, SIRInstKind::Store { .. })),
        2,
        "the call cannot have reached it: {:#?}",
        kinds(&shut.bodies[0])
    );
}
