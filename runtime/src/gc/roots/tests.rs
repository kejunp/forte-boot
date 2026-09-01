// That everything the program can still reach is found before marking starts.
//
// A root that is missed is an object freed underneath a live pointer, and it
// is the one bug in a collector that cannot be found by reading: the program
// carries on until it touches the freed thing, which may be a great deal
// later and somewhere else. So each kind of root gets a test of its own.

use super::super::super::shape::{Kind, Made};
use super::super::super::{alloc, Runtime};
use super::super::{cycle_from, mark};
use super::*;

fn pair() -> Made {
    Made::new(16, 8, Kind::Opaque).points_at(0)
}

fn marked(rt: &Runtime, at: usize) -> bool {
    match rt.heap.holding(at) {
        Some((id, index)) => rt.heap.span(id).marked(index),
        None => false,
    }
}

// ---- The stack -------------------------------------------------------------

#[test]
fn nothing_says_where_the_stack_is_until_something_says_so() {
    // Whatever an earlier test on this thread did, this is a fresh thread.
    let held = std::thread::spawn(|| base()).join().expect("a thread");
    assert_eq!(held, 0);
}

#[test]
fn noting_the_stack_records_something_above_where_we_are() {
    std::thread::spawn(|| {
        note();
        assert!(base() > here(), "the base is above the frames below it");
    })
    .join()
    .expect("a thread");
}

// The real thing: a pointer on the stack keeps its object, found by reading
// the words between here and the base.
#[test]
fn a_pointer_on_the_stack_is_found() {
    std::thread::spawn(|| {
        note();
        let mut rt = Runtime::new();
        let shape = pair();
        let held: [usize; 1] = [alloc::object(&mut rt, 16, Some(shape.shape()))];
        let at = held[0];
        super::super::start(&mut rt, here());
        assert!(marked(&rt, at), "a live local was not found");
        std::hint::black_box(&held);
        super::super::finish(&mut rt);
    })
    .join()
    .expect("a thread");
}

// ---- The registers ---------------------------------------------------------

// Read at all, and read as themselves. A list of six noughts would pass every
// test that only asked whether the call returned.
#[test]
fn the_callee_saved_registers_are_read() {
    let held = registers();
    assert!(!held.is_empty());
    // The frame pointer is one of them and is an address on this thread's
    // stack, so at least one of them is a plausible address rather than a
    // number nothing wrote.
    let near = here();
    assert!(
        held.iter().any(|one| one.abs_diff(near) < (1 << 20)),
        "none of {:x?} looks like this stack",
        held
    );
}

// ---- The runtime's own -----------------------------------------------------

#[test]
fn what_alloc_handed_out_is_a_root() {
    let mut rt = Runtime::new();
    let at = alloc::kept(&mut rt, 64);
    rt.heap.span_mut(rt.heap.holding(at).expect("a span").0).marks.none();
    owned(&mut rt);
    assert!(marked(&rt, at));
}

#[test]
fn what_is_pinned_is_reached_through_as_well() {
    let mut rt = Runtime::new();
    let shape = pair();
    let inner = alloc::object(&mut rt, 16, Some(shape.shape()));
    let outer = alloc::kept(&mut rt, 16);
    // `kept` says nothing about its contents, so nothing in it is followed --
    // which is the honest state of a closure environment nothing can read.
    unsafe { *(outer as *mut usize) = inner };
    cycle_from(&mut rt, &[]);
    assert!(rt.heap.holding(outer).is_some(), "it is not the collector's");
    assert!(rt.heap.holding(inner).is_none(), "and nothing said what is in it");
}

// A key in a map is reachable through the map however the map was reached,
// and the collector cannot see it any other way.
#[test]
fn what_is_in_a_map_is_a_root() {
    let mut rt = Runtime::new();
    let key = Made::new(24, 8, Kind::Opaque).indirect();
    let value = Made::new(8, 8, Kind::Signed);
    let table = super::super::super::map::Table::new(&mut rt, false, key.shape(), Some(value.shape()));
    rt.tables.push(table);

    let held: [u8; 24] = [7; 24];
    super::super::super::map::insert(&mut rt, 0, held.as_ptr() as usize, 5);
    let copied = rt.tables[0].get(held.as_ptr() as usize).map(|_| ());
    assert!(copied.is_some(), "the key went in");

    let roots = rt.tables[0].roots();
    assert!(!roots.is_empty(), "a copied key is somewhere only the map knows");
    cycle_from(&mut rt, &[]);
    for at in roots {
        assert!(rt.heap.holding(at).is_some(), "a map's own storage was collected");
    }
}

#[test]
fn what_is_in_a_set_is_a_root() {
    let mut rt = Runtime::new();
    let elem = Made::new(32, 8, Kind::Opaque).indirect();
    let held = super::super::super::set::Held::new(&mut rt, true, elem.shape());
    rt.sets.push(held);

    let one: [u8; 32] = [3; 32];
    super::super::super::set::Held::put(&mut rt, 0, one.as_ptr() as usize);
    let roots = rt.sets[0].roots();
    assert!(!roots.is_empty());
    cycle_from(&mut rt, &[]);
    for at in roots {
        assert!(rt.heap.holding(at).is_some(), "a set's own storage was collected");
    }
}

// ---- Together --------------------------------------------------------------

#[test]
fn shading_a_root_that_is_nothing_costs_nothing() {
    let mut rt = Runtime::new();
    mark::shade(&mut rt, 0);
    owned(&mut rt);
    assert!(rt.gc.work.is_empty());
}
