// That a big object behaves like every other object, and that its pages come
// back when it dies.
//
// The second is the whole reason this file exists. A small span that empties
// goes on a list and is used again; a large one belongs to no list, so if
// nothing here kept them a program that allocated a hundred megabyte buffers
// in turn would hold all hundred at once.

use super::super::classes;
use super::*;

#[test]
fn what_fits_a_class_is_not_alone_and_what_does_not_is() {
    assert!(!alone(1));
    assert!(!alone(classes::MAX));
    assert!(alone(classes::MAX + 1));
    assert!(alone(1 << 20));
}

#[test]
fn a_large_object_is_the_only_thing_in_its_span() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 100_000, true, 1).expect("a span");
    assert_eq!(h.span(id).count, 1);
    assert!(h.span(id).taken(0), "it is handed out as it is made");
    assert!(h.span(id).full());
    assert!(h.span(id).size >= 100_000);
}

// The arithmetic that finds an object works unchanged, which is the reason a
// large object is a span of one rather than a thing of its own.
#[test]
fn an_address_anywhere_in_a_large_object_finds_it() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 50_000, true, 1).expect("a span");
    let at = h.span(id).at;
    assert_eq!(h.holding(at), Some((id, 0)));
    assert_eq!(h.holding(at + 40_000), Some((id, 0)));
    assert_eq!(h.holding(at + h.span(id).size - 1), Some((id, 0)));
}

#[test]
fn every_large_object_is_listed() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let a = l.make(&mut h, 40_000, false, 1).expect("a span");
    let b = l.make(&mut h, 90_000, false, 1).expect("another");
    assert_eq!(l.all(), &[a, b]);
}

// ---- Dying -----------------------------------------------------------------

#[test]
fn a_large_object_nothing_reached_gives_its_pages_back() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 40_000, false, 1).expect("a span");
    let at = h.span(id).at;
    let bytes = h.span(id).size;

    let gone = l.sweep(&mut h, 2);
    assert_eq!(gone, bytes);
    assert!(l.all().is_empty());
    assert_eq!(h.span_at(at), None, "nothing owns those pages now");
}

#[test]
fn a_large_object_that_was_reached_is_kept() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 40_000, true, 1).expect("a span");
    h.span_mut(id).mark(0);

    assert_eq!(l.sweep(&mut h, 2), 0);
    assert_eq!(l.all(), &[id]);
    assert!(h.span(id).taken(0), "it survived, so it is still allocated");
    assert!(!h.span(id).marked(0), "and the mark is cleared for the next cycle");
}

// A large object allocated during a cycle is already up to date, and sweeping
// it in the cycle it was born in would free something the program is holding.
#[test]
fn a_large_object_made_this_cycle_is_left_alone() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 40_000, false, 2).expect("a span");
    assert_eq!(l.sweep(&mut h, 2), 0);
    assert_eq!(l.all(), &[id]);
}

#[test]
fn the_pages_of_a_dead_large_object_are_used_again() {
    let mut h = Heap::new();
    let mut l = Large::new();
    let id = l.make(&mut h, 40_000, false, 1).expect("a span");
    let at = h.span(id).at;
    l.sweep(&mut h, 2);

    let again = l.make(&mut h, 40_000, false, 2).expect("a span");
    assert_eq!(h.span(again).at, at, "the same pages came back");
}
