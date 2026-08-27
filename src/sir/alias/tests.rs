// What can be told apart and what cannot.
//
// Each of these builds a body that writes to two places and then asks whether
// the two addresses those writes went to may be one address. Writing is how
// the addresses are got at: a store names one, and `stores` below hands back
// the ones a body holds in the order they were written.

use crate::gir::gir_nodes::{GIRExprKind, GIRTerm};
use crate::sir::alias::*;
use crate::sir::fixture::*;
use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::TIRAssignOp;

// Every address a store in the body writes to, in the order the stores stand
// -- barring the entry, which holds the stores that put the parameters in
// their slots and is nothing any of these tests is about.
fn stores(body: &SIRBody) -> Vec<SIRValueId> {
    insts(body)
        .into_iter()
        .filter(|(at, _)| *at != body.entry || body.blocks.len() == 1)
        .filter_map(|(_, inst)| match inst.kind {
            SIRInstKind::Store { to, .. } => Some(to),
            _ => None,
        })
        .collect()
}

// Two names are two places, whatever is written through them.
#[test]
fn two_slots_are_two_places() {
    let mut f = Fixture::new();
    let x = f.local("x", f.int);
    let y = f.local("y", f.int);
    let at = f.block();
    let one = f.int(1);
    f.set(at, x, one);
    let two = f.int(2);
    f.set(at, y, two);
    // Both addresses are handed away, so neither name is taken out of the
    // frame and both stores are still stores.
    for name in [x, y] {
        let read = f.read(name);
        let addr = f.addr_of(read);
        let hands = f.hands(addr);
        f.eval(at, hands);
    }
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);

    assert!(wrote.len() >= 2, "{:#?}", kinds(body));
    assert!(!held.may(wrote[0], wrote[1]), "two names, two places");
    assert!(held.may(wrote[0], wrote[0]), "and one name is itself");
    assert!(held.must(wrote[0], wrote[0]));
}

// Two fields of one name are two places as well: the path parts even though
// the root does not.
#[test]
fn two_fields_of_one_name_are_two_places() {
    let mut f = Fixture::new();
    let p = f.local("p", f.int);
    let at = f.block();
    for index in [0, 1] {
        let read = f.read(p);
        let ty = f.int;
        let field = f.expr(GIRExprKind::Field { base: read, index }, ty);
        let value = f.int(index as i64);
        f.store(at, field, TIRAssignOp::Set, value);
    }
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let built = built(f);
    let body = &built.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);

    assert_eq!(wrote.len(), 2, "{:#?}", kinds(body));
    assert!(!held.may(wrote[0], wrote[1]), "`p.x` and `p.y`");
}

// And the same field twice is the same place, which is the stronger answer
// and the one that lets a load read what a store put there.
#[test]
fn one_field_written_twice_is_one_place() {
    let mut f = Fixture::new();
    let p = f.local("p", f.int);
    let at = f.block();
    for value in [1, 2] {
        let read = f.read(p);
        let ty = f.int;
        let field = f.expr(GIRExprKind::Field { base: read, index: 0 }, ty);
        let value = f.int(value);
        f.store(at, field, TIRAssignOp::Set, value);
    }
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let built = built(f);
    let body = &built.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);

    assert!(held.may(wrote[0], wrote[1]));
    assert!(held.must(wrote[0], wrote[1]), "the same field of the same name");
}

// Elements are told apart by the number, where there is one.
#[test]
fn two_numbered_elements_are_two_places_and_two_unknown_ones_are_not() {
    let build = |numbered: bool| {
        let mut f = Fixture::new();
        let xs = f.local("xs", f.int);
        let i = f.param("i", f.int);
        let j = f.param("j", f.int);
        let at = f.block();
        for (turn, name) in [(0, i), (1, j)] {
            let base = f.read(xs);
            let index = if numbered { f.int(turn) } else { f.read(name) };
            let ty = f.int;
            let elem = f.expr(GIRExprKind::Index { base, index }, ty);
            let value = f.int(7);
            f.store(at, elem, TIRAssignOp::Set, value);
        }
        f.term(at, GIRTerm::Return(None));
        f.body(at);
        built(f)
    };

    let known = build(true);
    let body = &known.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);
    assert_eq!(wrote.len(), 2, "{:#?}", kinds(body));
    assert!(!held.may(wrote[0], wrote[1]), "`xs[0]` and `xs[1]`");

    let unknown = build(false);
    let body = &unknown.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);
    assert!(held.may(wrote[0], wrote[1]), "`xs[i]` and `xs[j]` may be one element");
    assert!(!held.must(wrote[0], wrote[1]), "and may not be");
}

// ---- What a name is reachable by --------------------------------------------

// A body written out by hand, because the shape this asks about is one the
// lowering does not build: an address that came from outside the frame. Every
// address the GIR spells is rooted at a name, and it takes a parameter that
// *is* an address -- what a reference looks like once `promote` has taken the
// name holding it out of the frame -- for `Base::Elsewhere` to arise at all.
fn from_elsewhere(lets_out: bool) -> SIRBody {
    let hold = |kind, def| SIRInst { def, kind, is_unsafe: false, line: 1, col: 1 };
    let value = SIRValue { ty: 0, of: None, line: 1, col: 1 };
    // %0 is the parameter, and the rest are made below.
    let values = vec![value; 8];
    let mut insts = vec![
        hold(SIRInstKind::Addr(0), Some(1)),
        hold(SIRInstKind::Literal(crate::tir::tir_nodes::TIRLit::Int(0)), Some(2)),
        // `x[0]`, off a name of this frame.
        hold(SIRInstKind::IndexAddr { base: 1, index: 2 }, Some(3)),
        hold(SIRInstKind::Store { to: 3, value: 2 }, None),
        // And `p[0]`, off the address handed in.
        hold(SIRInstKind::IndexAddr { base: 0, index: 2 }, Some(4)),
        hold(SIRInstKind::Store { to: 4, value: 2 }, None),
    ];
    if lets_out {
        // The address of the name handed to something, which is the one thing
        // that could have put it where `p` came from.
        insts.push(hold(SIRInstKind::Addr(0), Some(5)));
        insts.push(hold(SIRInstKind::Call { callee: 6, args: vec![5] }, Some(7)));
    }
    SIRBody {
        entry:  0,
        blocks: vec![SIRBlock {
            phis: Vec::new(),
            insts,
            term: SIRTerm::Return(None),
            line: 1,
            col: 1,
        }],
        values,
        slots:  vec![SIRSlot {
            name:      crate::tir::tir_nodes::TIRBinding::Name("x".to_string()),
            ty:        0,
            of:        None,
            drops:     false,
            synthetic: false,
        }],
        params: vec![0],
    }
}

// A name nothing kept the address of is a name no address from elsewhere can
// be -- and one whose address was handed away is.
#[test]
fn an_address_from_elsewhere_reaches_only_what_was_let_out() {
    let shut = from_elsewhere(false);
    let held = Alias::of(&shut);
    let wrote = stores(&shut);
    assert_eq!(wrote.len(), 2, "{:#?}", kinds(&shut));
    assert!(
        !held.may(wrote[0], wrote[1]),
        "nothing kept the address of `x`, so `p` is not it"
    );
    assert!(held.own(wrote[0]), "and it is a name nothing else can reach");
    assert!(!held.own(wrote[1]), "which the one from elsewhere is not");

    let open = from_elsewhere(true);
    let held = Alias::of(&open);
    let wrote = stores(&open);
    assert!(held.may(wrote[0], wrote[1]), "the address went out, so `p` may be it");
    assert!(!held.own(wrote[0]));
}

// Stepping into a name is not keeping it. This is the whole difference between
// what this asks and what `sir::promote` asks, and it is what leaves anything
// to say about an array that is only ever indexed.
#[test]
fn stepping_into_a_name_does_not_let_it_out() {
    let mut f = Fixture::new();
    let xs = f.local("xs", f.int);
    let i = f.param("i", f.int);
    let at = f.block();
    let base = f.read(xs);
    let index = f.read(i);
    let ty = f.int;
    let elem = f.expr(GIRExprKind::Index { base, index }, ty);
    let value = f.int(1);
    f.store(at, elem, TIRAssignOp::Set, value);
    f.term(at, GIRTerm::Return(None));
    f.body(at);

    let p = built(f);
    let body = &p.bodies[0];
    let held = Alias::of(body);
    let wrote = stores(body);

    assert!(held.own(wrote[0]), "indexing it is not keeping it: {:#?}", kinds(body));
    assert_eq!(
        held.place(wrote[0]).map(|p| p.path.len()),
        Some(1),
        "one step in: {:#?}",
        held.place(wrote[0])
    );
}
