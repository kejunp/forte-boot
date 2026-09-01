// That the room really comes back, and that nothing comes back twice.
//
// The dangerous case is not the object that dies -- it is the span that
// empties. Its pages go back to the heap and become a span of some other
// class, and if anything still believed it held an object there, the two
// would be the same bytes. So the tests that matter here are about spans
// that empty and about the one span that must not be given back: the one the
// allocator is holding.

use super::super::super::shape::{Kind, Made};
use super::super::super::{alloc, Runtime};
use super::super::{cycle_from, finish, start_from, step, SLICE};
use super::*;

fn pair() -> Made {
    Made::new(16, 8, Kind::Opaque).points_at(0)
}

fn made(rt: &mut Runtime, shape: &Made) -> usize {
    alloc::object(rt, 16, Some(shape.shape()))
}

#[test]
fn nothing_is_freed_until_something_sweeps() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape);

    start_from(&mut rt, &[]);
    while step(&mut rt, SLICE) {}
    finish(&mut rt);
    assert!(rt.heap.holding(at).is_some(), "the marks are gone, the room is not");

    all(&mut rt);
    assert!(rt.heap.holding(at).is_none());
}

#[test]
fn what_a_sweep_freed_is_counted() {
    let mut rt = Runtime::new();
    let shape = pair();
    for _ in 0..10 {
        made(&mut rt, &shape);
    }
    start_from(&mut rt, &[]);
    finish(&mut rt);
    assert_eq!(all(&mut rt), 160, "ten objects of sixteen bytes");
}

#[test]
fn a_sweep_with_nothing_to_do_frees_nothing() {
    let mut rt = Runtime::new();
    cycle_from(&mut rt, &[]);
    assert_eq!(all(&mut rt), 0, "everything is already up to date");
}

// A large object is on no class list, so only its own list can find it.
#[test]
fn a_large_object_is_swept_too() {
    let mut rt = Runtime::new();
    let at = alloc::object(&mut rt, 100_000, None);
    assert_eq!(rt.large.all().len(), 1);
    cycle_from(&mut rt, &[]);
    assert!(rt.heap.holding(at).is_none());
    assert!(rt.large.all().is_empty());
}

#[test]
fn a_large_object_that_is_a_root_is_kept() {
    let mut rt = Runtime::new();
    let at = alloc::object(&mut rt, 100_000, None);
    cycle_from(&mut rt, &[at]);
    assert!(rt.heap.holding(at).is_some());
    assert_eq!(rt.large.all().len(), 1);
}

// ---- Spans that empty ------------------------------------------------------

// The span the cache is sitting on must not be given back, however empty it
// is: the allocator is about to take an object out of it, and the pages would
// belong to something else by then.
#[test]
fn the_span_the_allocator_is_holding_is_not_given_back() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape);
    let (id, _) = rt.heap.holding(at).expect("a span");
    assert!(rt.cache.all().contains(&id));

    cycle_from(&mut rt, &[]);
    assert!(rt.heap.span(id).pages > 0, "its pages were given away underneath");

    // And it still works.
    let again = made(&mut rt, &shape);
    assert_eq!(rt.heap.holding(again).map(|held| held.0), Some(id));
}

// ---- A slice at a time -----------------------------------------------------

// The background sweeper does a bounded amount, or lazy sweeping would mean a
// span nothing asks for again is never swept at all.
#[test]
fn a_slice_of_sweeping_does_a_bounded_number_of_spans() {
    let mut rt = Runtime::new();
    let shape = pair();
    for _ in 0..3000 {
        made(&mut rt, &shape);
    }
    start_from(&mut rt, &[]);
    finish(&mut rt);
    let spans = rt.heap.all().len();
    assert!(spans > 2, "this wants several spans");

    assert_eq!(some(&mut rt, 2), 2);
    let left = rt.heap.all().iter().filter(|id| rt.heap.span(**id).swept < rt.gc.cycle).count();
    assert_eq!(left, spans - 2, "only two were done");
}

#[test]
fn sweeping_a_slice_at_a_time_finishes_what_sweeping_all_would() {
    let mut rt = Runtime::new();
    let shape = pair();
    let mut held = Vec::new();
    for _ in 0..2000 {
        held.push(made(&mut rt, &shape));
    }
    start_from(&mut rt, &[]);
    finish(&mut rt);
    while some(&mut rt, 1) > 0 {}
    for at in &held {
        assert!(rt.heap.holding(*at).is_none(), "a slice-swept object survived");
    }
}
