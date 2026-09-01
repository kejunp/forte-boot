// That two objects are never the same object, and that what comes back is
// usable.
//
// An allocator has one thing it must never do and it is not a thing a type
// system can stop: hand the same bytes to two callers. So the tests here are
// mostly the same test at different sizes -- take a great many, write a
// distinct pattern into every one, then read them all back. Anything that
// overlapped shows up as a pattern that is not its own.
//
// The addresses are real, so these write to them. That is the point: a heap
// that returns plausible addresses backed by nothing would pass every test
// that only compared numbers.

use super::super::heap::classes;
use super::super::shape::{Kind, Made};
use super::*;

fn fresh() -> Runtime {
    Runtime::new()
}

// Writing the same byte through the whole object and reading it back is what
// says the room is really there and really that big.
fn fill(at: usize, bytes: usize, with: u8) {
    unsafe {
        std::ptr::write_bytes(at as *mut u8, with, bytes);
    }
}

fn holds(at: usize, bytes: usize, with: u8) -> bool {
    unsafe { (0..bytes).all(|i| *(at as *const u8).add(i) == with) }
}

// ---- One object ------------------------------------------------------------

#[test]
fn what_comes_back_can_be_written_to_all_the_way_through() {
    let mut rt = fresh();
    for bytes in [1usize, 8, 100, 5000, 40_000] {
        let at = object(&mut rt, bytes, None);
        assert_ne!(at, 0, "{} bytes", bytes);
        fill(at, bytes, 0xab);
        assert!(holds(at, bytes, 0xab), "{} bytes", bytes);
    }
}

// Reused room is not the last tenant's. The marker reads the words a shape
// called pointers, and a leftover word would be followed.
#[test]
fn what_comes_back_is_nought() {
    let mut rt = fresh();
    let made = Made::new(64, 8, Kind::Opaque);
    let first = object(&mut rt, 64, Some(made.shape()));
    fill(first, 64, 0xff);

    // Kill it, leaving the cache holding the span it came out of, so that the
    // next allocation of that class is the same room and the test is about
    // the same room.
    let (id, _) = rt.heap.holding(first).expect("a span");
    rt.heap.span_mut(id).sweep(2);
    let again = object(&mut rt, 64, Some(made.shape()));
    assert_eq!(again, first, "the same room, so the test is about the same room");
    assert!(holds(again, 64, 0), "it came back with the last tenant in it");
}

#[test]
fn nothing_at_all_still_gets_an_address_of_its_own() {
    let mut rt = fresh();
    let a = object(&mut rt, 0, None);
    let b = object(&mut rt, 0, None);
    assert_ne!(a, 0);
    assert_ne!(a, b, "two of nothing are still two things");
}

// ---- Many objects ----------------------------------------------------------

#[test]
fn no_two_objects_share_a_byte() {
    let mut rt = fresh();
    let sizes = [1usize, 3, 8, 17, 64, 200, 1000, 5000];
    let mut held = Vec::new();
    for round in 0..40u8 {
        for (which, &bytes) in sizes.iter().enumerate() {
            let at = object(&mut rt, bytes, None);
            let mark = round.wrapping_mul(11).wrapping_add(which as u8) | 1;
            fill(at, bytes, mark);
            held.push((at, bytes, mark));
        }
    }
    for (at, bytes, mark) in held {
        assert!(holds(at, bytes, mark), "{:x} was written over", at);
    }
}

// Enough of one class to fill several spans, which is the path where the cache
// gives a span up and takes another.
#[test]
fn filling_a_span_moves_on_to_the_next_one() {
    let mut rt = fresh();
    let mut held = Vec::new();
    for i in 0..2000u32 {
        let at = object(&mut rt, 48, None);
        unsafe { *(at as *mut u32) = i };
        held.push(at);
    }
    for (i, at) in held.iter().enumerate() {
        assert_eq!(unsafe { *(*at as *const u32) }, i as u32, "object {}", i);
    }
    assert!(rt.heap.spans() > 1, "two thousand of these do not fit one span");
}

// ---- Which path ------------------------------------------------------------

// A small pointer-free object shares a block with its neighbours, which is
// what makes a three-byte thing cost three bytes and not eight.
#[test]
fn small_things_with_no_pointers_share_a_block() {
    let mut rt = fresh();
    let a = object(&mut rt, 4, None);
    let b = object(&mut rt, 4, None);
    assert_eq!(b, a + 4, "the second went in beside the first");
    assert_eq!(rt.heap.holding(a), rt.heap.holding(b), "one object holds both");
}

// A small object that *does* hold a pointer must not, because the collector
// has to be able to say what is at each word of it and a shared block has
// several tenants' worth.
#[test]
fn a_small_thing_holding_a_pointer_gets_an_object_to_itself() {
    let mut rt = fresh();
    let held = Made::new(8, 8, Kind::Pointer).points_at(0);
    let a = object(&mut rt, 8, Some(held.shape()));
    let b = object(&mut rt, 8, Some(held.shape()));
    assert_ne!(rt.heap.holding(a), rt.heap.holding(b));
}

#[test]
fn a_block_that_is_full_is_left_and_another_begun() {
    let mut rt = fresh();
    let first = object(&mut rt, 12, None);
    let second = object(&mut rt, 12, None);
    assert_ne!(
        rt.heap.holding(first),
        rt.heap.holding(second),
        "twelve and twelve do not fit in sixteen"
    );
}

#[test]
fn something_too_big_for_a_class_gets_a_span_to_itself() {
    let mut rt = fresh();
    let at = object(&mut rt, classes::MAX + 1, None);
    let (id, index) = rt.heap.holding(at).expect("a span");
    assert_eq!(rt.heap.span(id).class, 0);
    assert_eq!(index, 0);
    assert_eq!(rt.large.all(), &[id]);
}

// ---- What the shape says ---------------------------------------------------

#[test]
fn a_type_with_pointers_goes_in_a_span_that_is_scanned() {
    let mut rt = fresh();
    let held = Made::new(32, 8, Kind::Opaque).points_at(8);
    let at = object(&mut rt, 32, Some(held.shape()));
    let (id, index) = rt.heap.holding(at).expect("a span");
    assert!(rt.heap.span(id).scan);
    assert!(!rt.heap.span(id).points(index, 0));
    assert!(rt.heap.span(id).points(index, 1), "the shape said word one");
    assert!(!rt.heap.span(id).points(index, 2));
}

#[test]
fn a_type_with_no_pointers_goes_in_a_span_that_is_never_scanned() {
    let mut rt = fresh();
    let held = Made::new(200, 8, Kind::Opaque);
    let at = object(&mut rt, 200, Some(held.shape()));
    let (id, _) = rt.heap.holding(at).expect("a span");
    assert!(!rt.heap.span(id).scan);
}

// Two types of the same size, one with a pointer and one without, share
// nothing -- which is what lets a whole span be skipped.
#[test]
fn two_types_of_one_size_are_described_apart() {
    let mut rt = fresh();
    let one = Made::new(32, 8, Kind::Opaque).points_at(0);
    let two = Made::new(32, 8, Kind::Opaque).points_at(24);
    let a = object(&mut rt, 32, Some(one.shape()));
    let b = object(&mut rt, 32, Some(two.shape()));
    let (ida, ia) = rt.heap.holding(a).expect("a span");
    let (idb, ib) = rt.heap.holding(b).expect("a span");
    assert_eq!(ida, idb, "the same class and both scanned");
    assert!(rt.heap.span(ida).points(ia, 0));
    assert!(!rt.heap.span(ida).points(ia, 3));
    assert!(!rt.heap.span(idb).points(ib, 0));
    assert!(rt.heap.span(idb).points(ib, 3));
}

// ---- Counting and colour ---------------------------------------------------

#[test]
fn what_has_been_handed_out_is_counted() {
    let mut rt = fresh();
    let before = rt.heap.live;
    object(&mut rt, 1000, None);
    assert!(rt.heap.live >= before + 1000);
}

// An object made while a cycle is running is marked as it is made, because the
// marker is working from a picture of the heap that could not have included
// it.
#[test]
fn an_object_made_during_a_cycle_is_marked_as_it_is_made() {
    let mut rt = fresh();
    rt.gc.black = true;
    let at = object(&mut rt, 100, None);
    let (id, index) = rt.heap.holding(at).expect("a span");
    assert!(rt.heap.span(id).marked(index));
}

#[test]
fn an_object_made_between_cycles_is_not_marked() {
    let mut rt = fresh();
    let at = object(&mut rt, 100, None);
    let (id, index) = rt.heap.holding(at).expect("a span");
    assert!(!rt.heap.span(id).marked(index));
}

// ---- Room nothing collects -------------------------------------------------

#[test]
fn what_is_kept_is_marked_and_remembered() {
    let mut rt = fresh();
    let at = kept(&mut rt, 64);
    let (id, index) = rt.heap.holding(at).expect("a span");
    assert!(rt.heap.span(id).marked(index));
    assert!(rt.pinned.contains(&(id, index)));
}
