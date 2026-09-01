// That an address can be turned back into the object it is inside.
//
// Everything the collector concludes is downstream of `holding`, and there are
// three ways for it to be wrong that no other test would notice: an address in
// a span nothing owns coming back as an object, an address in the tail waste
// coming back as the last object, and an address in a *freed* span coming back
// as whatever now occupies those pages. The last is the worst, because it is
// how a collector marks something that is not there.

use super::*;

#[test]
fn a_new_heap_holds_nothing_and_knows_nothing() {
    let h = Heap::new();
    assert_eq!(h.spans(), 0);
    assert_eq!(h.span_at(0x1000), None);
    assert_eq!(h.holding(0x1000), None);
}

// ---- Spans out of pages ----------------------------------------------------

#[test]
fn a_span_of_a_class_is_as_many_pages_as_the_class_says() {
    let mut h = Heap::new();
    for class in [1usize, 20, 44, classes::COUNT] {
        let id = h.span_of_class(class, false).expect("a span");
        assert_eq!(h.span(id).pages, classes::pages_of(class), "class {}", class);
        assert_eq!(h.span(id).class, class);
    }
}

#[test]
fn two_spans_do_not_share_a_page() {
    let mut h = Heap::new();
    let mut held: Vec<(usize, usize)> = Vec::new();
    for _ in 0..40 {
        let id = h.span_of_class(30, false).expect("a span");
        held.push((h.span(id).at, h.span(id).ends()));
    }
    for (i, a) in held.iter().enumerate() {
        for (j, b) in held.iter().enumerate() {
            if i != j {
                assert!(a.1 <= b.0 || b.1 <= a.0, "{:x?} and {:x?} overlap", a, b);
            }
        }
    }
}

// Every page of a span answers with that span, not just the first. A span of
// several pages whose later pages said nothing would lose every object past
// the first page's worth.
#[test]
fn every_page_of_a_span_names_it() {
    let mut h = Heap::new();
    let id = h.span_of_class(65, false).expect("a span");
    assert!(h.span(id).pages > 1, "this class wants several pages");
    for page in 0..h.span(id).pages {
        let at = h.span(id).at + page * PAGE;
        assert_eq!(h.span_at(at), Some(id), "page {}", page);
    }
}

// ---- Finding an object -----------------------------------------------------

#[test]
fn an_address_in_a_taken_object_finds_it() {
    let mut h = Heap::new();
    let id = h.span_of_class(6, true).expect("a span");
    let index = h.span_mut(id).take().expect("an object");
    let at = h.span(id).base_of(index);
    assert_eq!(h.holding(at), Some((id, index)));
    assert_eq!(h.holding(at + 1), Some((id, index)), "inside it, too");
    assert_eq!(h.holding(at + h.span(id).size - 1), Some((id, index)));
}

// An address into room nothing has been given is not an object. This is what
// keeps the marker from marking a bit for something the program has never
// seen -- which would be harmless until the sweep counted it as a survivor.
#[test]
fn an_address_in_a_free_object_finds_nothing() {
    let mut h = Heap::new();
    let id = h.span_of_class(6, true).expect("a span");
    let at = h.span(id).base_of(3);
    assert_eq!(h.holding(at), None);
}

#[test]
fn an_address_in_no_span_at_all_finds_nothing() {
    let mut h = Heap::new();
    let id = h.span_of_class(6, true).expect("a span");
    let past = h.span(id).at + ARENA;
    assert_eq!(h.holding(past), None);
    assert_eq!(h.holding(8), None);
    assert_eq!(h.holding(usize::MAX - 7), None);
}

// The one that would be a real bug: a span's pages given back and then handed
// to a span of some other class. An address that used to name an object must
// not name whatever is at those bytes now.
#[test]
fn an_address_in_a_released_span_finds_nothing() {
    let mut h = Heap::new();
    let id = h.span_of_class(6, true).expect("a span");
    let index = h.span_mut(id).take().expect("an object");
    let at = h.span(id).base_of(index);
    assert!(h.holding(at).is_some());

    h.release(id);
    assert_eq!(h.span_at(at), None, "nothing owns those pages now");
    assert_eq!(h.holding(at), None);
}

// ---- Pages back and forth --------------------------------------------------

#[test]
fn a_released_spans_pages_are_used_again() {
    let mut h = Heap::new();
    let first = h.span_of_class(20, false).expect("a span");
    let at = h.span(first).at;
    h.release(first);
    let second = h.span_of_class(20, false).expect("another");
    assert_eq!(h.span(second).at, at, "the same pages came back");
}

// The place in the list of spans is used again too, so that a program which
// allocates and frees for ever does not grow the list for ever.
#[test]
fn a_released_spans_place_is_used_again() {
    let mut h = Heap::new();
    let first = h.span_of_class(20, false).expect("a span");
    h.release(first);
    let second = h.span_of_class(20, false).expect("another");
    assert_eq!(first, second);
    assert_eq!(h.spans(), 1);
}

// Two neighbours given back become one run, or a heap that allocated many
// small spans and freed them could not then make one large one.
#[test]
fn neighbouring_free_runs_become_one() {
    let mut h = Heap::new();
    let mut held = Vec::new();
    for _ in 0..8 {
        held.push(h.span_of_class(1, false).expect("a span"));
    }
    for id in held {
        h.release(id);
    }
    let big = h.span_of_bytes(6 * PAGE, false).expect("a large span");
    assert!(h.span(big).pages >= 6);
}

#[test]
fn a_large_object_gets_a_span_the_size_it_asked_for() {
    let mut h = Heap::new();
    let id = h.span_of_bytes(100_000, true).expect("a span");
    assert!(h.span(id).bytes() >= 100_000);
    assert_eq!(h.span(id).class, 0);
    assert_eq!(h.span(id).count, 1);
}

// Bigger than a whole reservation, which is the case the page allocator would
// get wrong by giving out a run that stops at an arena boundary.
#[test]
fn an_object_bigger_than_an_arena_still_fits() {
    let mut h = Heap::new();
    let want = ARENA * 2 + PAGE;
    let id = h.span_of_bytes(want, false).expect("a span");
    assert!(h.span(id).bytes() >= want);
    // And every page of it answers, which is what says the run really is one
    // stretch and not two that happen to be adjacent.
    for page in 0..h.span(id).pages {
        assert_eq!(h.span_at(h.span(id).at + page * PAGE), Some(id), "page {}", page);
    }
}

// ---- Counting --------------------------------------------------------------

#[test]
fn what_has_been_reserved_is_counted() {
    let mut h = Heap::new();
    assert_eq!(h.reserved, 0);
    h.span_of_class(1, false);
    assert!(h.reserved >= ARENA);
}

#[test]
fn every_span_in_use_is_listed_and_a_released_one_is_not() {
    let mut h = Heap::new();
    let a = h.span_of_class(4, false).expect("a span");
    let b = h.span_of_class(5, false).expect("another");
    assert_eq!(h.all().len(), 2);
    h.release(a);
    assert_eq!(h.all(), vec![b]);
}
