// That shading follows what it should and stops where it should.
//
// The two halves are the whole of the marker's correctness. `scan` reads only
// the words a shape named, so an integer beside a pointer is never followed;
// `conservative` reads every word, so a stack can be scanned without knowing
// anything about it. Both end in `shade`, and `shade` is where a word that is
// not an address costs a failed lookup and nothing else.

use super::super::super::shape::{Kind, Made};
use super::super::super::{alloc, Runtime};
use super::*;

fn pair() -> Made {
    Made::new(16, 8, Kind::Opaque).points_at(0)
}

fn made(rt: &mut Runtime, shape: &Made, first: usize, second: usize) -> usize {
    let at = alloc::object(rt, 16, Some(shape.shape()));
    unsafe {
        *(at as *mut usize) = first;
        *((at + 8) as *mut usize) = second;
    }
    at
}

fn marked(rt: &Runtime, at: usize) -> bool {
    match rt.heap.holding(at) {
        Some((id, index)) => rt.heap.span(id).marked(index),
        None => false,
    }
}

// ---- Shading ---------------------------------------------------------------

#[test]
fn shading_an_address_marks_the_object_it_is_inside() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape, 0, 0);
    shade(&mut rt, at);
    assert!(marked(&rt, at));
}

#[test]
fn shading_a_word_that_is_not_an_address_does_nothing() {
    let mut rt = Runtime::new();
    for held in [0usize, 1, 0xdead_beef, usize::MAX] {
        shade(&mut rt, held);
    }
    assert!(rt.gc.work.is_empty());
}

// Twice is once. Without that a ring of objects would be an endless walk.
#[test]
fn shading_the_same_object_twice_puts_it_on_the_list_once() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape, 0, 0);
    shade(&mut rt, at);
    shade(&mut rt, at);
    assert_eq!(rt.gc.work.len(), 1);
}

// There is nothing inside it to reach, so putting it on the list would be
// putting it there to take it off again.
#[test]
fn an_object_with_nothing_in_it_is_marked_and_not_listed() {
    let mut rt = Runtime::new();
    let plain = Made::new(32, 8, Kind::Opaque);
    let at = alloc::object(&mut rt, 32, Some(plain.shape()));
    shade(&mut rt, at);
    assert!(marked(&rt, at));
    assert!(rt.gc.work.is_empty());
}

// ---- Draining --------------------------------------------------------------

#[test]
fn draining_follows_the_words_a_shape_called_pointers() {
    let mut rt = Runtime::new();
    let shape = pair();
    let inner = made(&mut rt, &shape, 0, 0);
    let outer = made(&mut rt, &shape, inner, 0);
    shade(&mut rt, outer);
    drain(&mut rt, usize::MAX);
    assert!(marked(&rt, inner));
}

#[test]
fn draining_does_not_follow_the_words_it_did_not() {
    let mut rt = Runtime::new();
    let shape = pair();
    let hidden = made(&mut rt, &shape, 0, 0);
    let outer = made(&mut rt, &shape, 0, hidden);
    shade(&mut rt, outer);
    drain(&mut rt, usize::MAX);
    assert!(!marked(&rt, hidden), "word one is a number");
}

// The budget is what makes marking concurrent: the thread does this much and
// lets go of the lock.
#[test]
fn draining_stops_at_the_budget() {
    let mut rt = Runtime::new();
    let shape = pair();
    let mut last = 0;
    for _ in 0..20 {
        last = made(&mut rt, &shape, last, 0);
    }
    shade(&mut rt, last);
    assert_eq!(drain(&mut rt, 5), 5);
    assert!(!rt.gc.work.is_empty(), "there was more to do");
}

#[test]
fn draining_an_empty_list_does_nothing() {
    let mut rt = Runtime::new();
    assert_eq!(drain(&mut rt, 100), 0);
}

// ---- Conservatively --------------------------------------------------------

#[test]
fn every_word_of_a_range_is_treated_as_an_address() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape, 0, 0);
    let held: [usize; 4] = [7, at, 0, 0xffff_0000];
    let from = held.as_ptr() as usize;
    conservative(&mut rt, from, from + 32);
    assert!(marked(&rt, at), "the address in the middle was not found");
}

// The cost of the compromise, asserted rather than hoped for: a number that
// looks like an address keeps its object alive.
#[test]
fn a_number_that_looks_like_an_address_keeps_its_object() {
    let mut rt = Runtime::new();
    let shape = pair();
    let at = made(&mut rt, &shape, 0, 0);
    let held: [usize; 1] = [at + 4];
    let from = held.as_ptr() as usize;
    conservative(&mut rt, from, from + 8);
    assert!(marked(&rt, at), "this is what conservative means");
}

// ---- Counting --------------------------------------------------------------

#[test]
fn what_is_marked_is_counted_in_bytes() {
    let mut rt = Runtime::new();
    let shape = pair();
    let a = made(&mut rt, &shape, 0, 0);
    let b = made(&mut rt, &shape, 0, 0);
    assert_eq!(marked_bytes(&rt), 0);
    shade(&mut rt, a);
    shade(&mut rt, b);
    assert_eq!(marked_bytes(&rt), 32, "two objects of sixteen bytes");
}

#[test]
fn every_span_is_listed_once() {
    let mut rt = Runtime::new();
    for bytes in [8usize, 100, 1000, 40_000] {
        alloc::object(&mut rt, bytes, None);
    }
    let held = every(&rt);
    let mut once = held.clone();
    once.dedup();
    assert_eq!(held, once);
    assert!(held.len() >= 4);
}
