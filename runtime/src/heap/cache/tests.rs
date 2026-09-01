// That a span with room in it is the one that comes back.
//
// The lists are bookkeeping, and bookkeeping fails quietly: a span put in the
// full list while it still has room is memory nothing will ever hand out
// again, and a span handed out while it is full is a caller looping forever
// looking for a free object in it. Neither shows up as a wrong answer.

use super::super::classes;
use super::*;

#[test]
fn a_class_with_nothing_in_it_gets_a_new_span() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let id = c.span(&mut h, 4, false, 1).expect("a span");
    assert_eq!(h.span(id).class, 4);
    assert!(!h.span(id).full());
}

#[test]
fn a_span_that_was_given_back_comes_back() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let first = c.span(&mut h, 4, false, 1).expect("a span");
    c.give(&h, first);
    let again = c.span(&mut h, 4, false, 1).expect("a span");
    assert_eq!(first, again, "there was one with room, so nothing new was made");
}

// A span holding pointers and one holding none are never the same span, which
// is what lets a whole span be skipped by the marker.
#[test]
fn a_scanned_class_and_an_unscanned_one_do_not_share_a_span() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let plain = c.span(&mut h, 4, false, 1).expect("a span");
    let held = c.span(&mut h, 4, true, 1).expect("another");
    assert_ne!(plain, held);
    assert!(!h.span(plain).scan);
    assert!(h.span(held).scan);
}

#[test]
fn a_full_span_is_not_handed_out_again() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let id = c.span(&mut h, 4, false, 1).expect("a span");
    while h.span_mut(id).take().is_some() {}
    c.give(&h, id);
    let again = c.span(&mut h, 4, false, 1).expect("a span");
    assert_ne!(id, again, "the full one would have nothing to give");
}

// ---- Sweeping when asked ---------------------------------------------------

// The whole of what "lazy" means. A span left over from the last cycle is full
// of things nothing reached, and nobody has looked yet -- so the caller that
// wants room is the one who looks.
#[test]
fn a_span_left_over_from_the_last_cycle_is_swept_when_something_wants_room() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let id = c.span(&mut h, 4, false, 1).expect("a span");
    while h.span_mut(id).take().is_some() {}
    c.give(&h, id);
    assert!(h.span(id).full());

    // A cycle passes and nothing in it was reached.
    let again = c.span(&mut h, 4, false, 2).expect("a span");
    assert_eq!(again, id, "the full one was swept and had room after all");
    assert_eq!(h.span(id).free(), h.span(id).count);
    assert_eq!(h.span(id).swept, 2);
}

#[test]
fn a_span_whose_objects_all_survived_is_still_full_after_a_sweep() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let id = c.span(&mut h, 4, false, 1).expect("a span");
    while let Some(at) = h.span_mut(id).take() {
        h.span_mut(id).mark(at);
    }
    c.give(&h, id);
    let again = c.span(&mut h, 4, false, 2).expect("a span");
    assert_ne!(again, id, "everything in it was reached, so it had no room");
    assert!(h.span(id).full());
}

// ---- What a sweep has to be able to find -----------------------------------

#[test]
fn every_span_the_lists_hold_is_listed() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let mut held = Vec::new();
    for class in [1usize, 4, 9] {
        let id = c.span(&mut h, class, false, 1).expect("a span");
        c.give(&h, id);
        held.push(id);
    }
    let all = c.all();
    for id in held {
        assert!(all.contains(&id), "span {} was not listed", id);
    }
}

// A span in the cache is in no central list, so a sweep that walked only the
// central lists would leave it holding garbage for ever.
#[test]
fn every_span_the_cache_is_sitting_on_is_listed() {
    let mut cache = Cache::new();
    cache.hold(4, false, Some(7));
    cache.hold(9, true, Some(11));
    let all = cache.all();
    assert!(all.contains(&7));
    assert!(all.contains(&11));
    assert_eq!(all.len(), 2);
}

#[test]
fn the_cache_holds_one_span_per_class_and_per_scannedness() {
    let mut cache = Cache::new();
    cache.hold(4, false, Some(1));
    cache.hold(4, true, Some(2));
    assert_eq!(cache.holding(4, false), Some(1));
    assert_eq!(cache.holding(4, true), Some(2));
    assert_eq!(cache.holding(5, false), None);
    cache.hold(4, false, None);
    assert_eq!(cache.holding(4, false), None);
}

// ---- Giving a span up altogether -------------------------------------------

// A span nothing is left in goes back to the heap so its pages can become a
// span of some other class. Without it a program that allocates a great many
// of one size and then a great many of another holds both for ever.
#[test]
fn an_empty_span_goes_back_to_the_heap() {
    let mut h = Heap::new();
    let mut c = Central::new();
    let id = c.span(&mut h, 4, false, 1).expect("a span");
    c.give(&h, id);
    let at = h.span(id).at;
    c.drop_empty(&mut h, id);
    assert_eq!(h.span_at(at), None);
    assert!(!c.all().contains(&id));
}

#[test]
fn there_is_a_list_for_every_class() {
    let mut h = Heap::new();
    let mut c = Central::new();
    for class in 1..=classes::COUNT {
        assert!(c.span(&mut h, class, false, 1).is_some(), "class {}", class);
    }
}
