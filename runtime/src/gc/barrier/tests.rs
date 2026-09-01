// That a pointer moved while the marker is walking is not lost.
//
// This is the one test in the runtime that reproduces a race deliberately.
// The shape of it is always the same: mark part of the way, move the only
// pointer to something from a place the marker has not reached into a place
// it has already left, finish, and check that the something is still there.
// Without the barrier that object is freed while the program is holding it,
// and every one of these tests fails.
//
// The barrier itself is a free function on a global, so these use the global
// runtime rather than one of their own. That is the only place in the runtime
// where a test does, and it is because the fast path reads a global on
// purpose -- a barrier that had to be handed a runtime would be a barrier
// taking the lock to find out it had nothing to do.

use super::super::super::shape::{Kind, Made};
use super::super::super::{alloc, Runtime};
use super::super::{finish, mark, start_from, step, sweep, SLICE};
use super::*;

fn pair() -> Made {
    Made::new(16, 8, Kind::Opaque).points_at(0)
}

fn made(rt: &mut Runtime, shape: &Made, first: usize) -> usize {
    let at = alloc::object(rt, 16, Some(shape.shape()));
    unsafe { *(at as *mut usize) = first };
    at
}

fn alive(rt: &Runtime, at: usize) -> bool {
    rt.heap.holding(at).is_some()
}

// ---- Off -------------------------------------------------------------------

// Between cycles the barrier is a store and a branch, which it has to be:
// this is on the path of every pointer store in the program.
#[test]
fn between_cycles_the_barrier_is_a_store() {
    let mut held: usize = 7;
    write(&mut held as *mut usize, 11);
    assert_eq!(held, 11);
}

#[test]
fn a_bulk_copy_between_cycles_moves_the_bytes() {
    let shape = Made::new(24, 8, Kind::Opaque).points_at(8);
    let from: [u8; 24] = [9; 24];
    let mut to: [u8; 24] = [0; 24];
    copy(to.as_mut_ptr(), from.as_ptr(), shape.shape());
    assert_eq!(to, from);
}

// ---- Hiding a pointer ------------------------------------------------------

// The Dijkstra half. `victim` is reachable only from `black`, which the marker
// has already looked at, so nothing will look at it again -- unless the store
// itself shades what is being written.
#[test]
fn a_pointer_written_into_something_already_scanned_survives() {
    let mut rt = Runtime::new();
    let shape = pair();
    let black = made(&mut rt, &shape, 0);
    let victim = made(&mut rt, &shape, 0);

    start_from(&mut rt, &[black]);
    while step(&mut rt, SLICE) {}
    assert!(rt.gc.work.is_empty(), "the marker has finished walking");

    // The program stores, and the barrier is what makes it visible.
    mark::shade(&mut rt, victim);
    unsafe { *(black as *mut usize) = victim };

    finish(&mut rt);
    sweep::all(&mut rt);
    assert!(alive(&rt, victim), "the pointer was hidden in a black object");
}

// The Yuasa half, which is what lets a stack be scanned once. `victim` is
// reachable only from `grey`, which the marker has not reached; the program
// takes it out and puts it on its own stack, where nothing will look again.
// Shading what is being *overwritten* is what saves it.
#[test]
fn a_pointer_taken_out_of_something_not_yet_scanned_survives() {
    let mut rt = Runtime::new();
    let shape = pair();
    let victim = made(&mut rt, &shape, 0);
    let grey = made(&mut rt, &shape, victim);

    start_from(&mut rt, &[grey]);
    // Nothing has been drained, so `grey` is grey and `victim` is white.
    let old = unsafe { *(grey as *const usize) };
    mark::shade(&mut rt, old);
    unsafe { *(grey as *mut usize) = 0 };

    while step(&mut rt, SLICE) {}
    finish(&mut rt);
    sweep::all(&mut rt);
    assert!(alive(&rt, victim), "the pointer was deleted before it was seen");
}

// And what it costs: an object saved by the deletion half is retained for one
// cycle whether or not anything still wants it. That is what "a snapshot of
// the heap as it stood at the start" means, and it is why a cycle frees what
// died before it began rather than what has died by the time it ends.
#[test]
fn what_the_barrier_saved_is_collected_by_the_next_cycle() {
    let mut rt = Runtime::new();
    let shape = pair();
    let victim = made(&mut rt, &shape, 0);
    let grey = made(&mut rt, &shape, victim);

    start_from(&mut rt, &[grey]);
    mark::shade(&mut rt, unsafe { *(grey as *const usize) });
    unsafe { *(grey as *mut usize) = 0 };
    while step(&mut rt, SLICE) {}
    finish(&mut rt);
    sweep::all(&mut rt);
    assert!(alive(&rt, victim));

    super::super::cycle_from(&mut rt, &[grey]);
    assert!(!alive(&rt, victim), "nothing points at it any more");
}

// ---- Through the barrier itself --------------------------------------------

// The same two shades, made by the barrier rather than by the test. Over a
// runtime of its own, because what is being checked is the three lines of the
// barrier and not the flag and the lock in front of them.
#[test]
fn the_barrier_shades_both_ends_of_a_store() {
    let mut rt = Runtime::new();
    let shape = pair();
    let old = made(&mut rt, &shape, 0);
    let new = made(&mut rt, &shape, 0);
    let slot = alloc::kept(&mut rt, 8);
    unsafe { *(slot as *mut usize) = old };

    start_from(&mut rt, &[]);
    write_in(&mut rt, slot as *mut usize, new);

    assert_eq!(unsafe { *(slot as *const usize) }, new, "the store still happened");
    for at in [old, new] {
        let (id, index) = rt.heap.holding(at).expect("a span");
        assert!(rt.heap.span(id).marked(index), "{:x} was not shaded", at);
    }
    finish(&mut rt);
}

// A structure assignment is a great many pointer stores at once and every one
// of them needs the same two shades.
#[test]
fn a_bulk_copy_shades_every_pointer_word_it_moves() {
    let mut rt = Runtime::new();
    let node = pair();
    let shape = Made::new(16, 8, Kind::Opaque).points_at(0);
    let old = made(&mut rt, &node, 0);
    let new = made(&mut rt, &node, 0);
    let to = alloc::kept(&mut rt, 16);
    let from = alloc::kept(&mut rt, 16);
    unsafe {
        *(to as *mut usize) = old;
        *(from as *mut usize) = new;
    }

    start_from(&mut rt, &[]);
    copy_in(&mut rt, to as *mut u8, from as *const u8, shape.shape());

    assert_eq!(unsafe { *(to as *const usize) }, new, "the bytes moved");
    for at in [old, new] {
        let (id, index) = rt.heap.holding(at).expect("a span");
        assert!(rt.heap.span(id).marked(index), "{:x} was not shaded", at);
    }
    finish(&mut rt);
}

// A word the map did not name is moved and not shaded, which is the whole
// difference between a bulk barrier and shading everything that goes past.
#[test]
fn a_bulk_copy_does_not_shade_what_the_map_did_not_name() {
    let mut rt = Runtime::new();
    let node = pair();
    let shape = Made::new(16, 8, Kind::Opaque).points_at(0);
    let hidden = made(&mut rt, &node, 0);
    let to = alloc::kept(&mut rt, 16);
    let from = alloc::kept(&mut rt, 16);
    unsafe { *((from + 8) as *mut usize) = hidden };

    start_from(&mut rt, &[]);
    copy_in(&mut rt, to as *mut u8, from as *const u8, shape.shape());

    let (id, index) = rt.heap.holding(hidden).expect("a span");
    assert!(!rt.heap.span(id).marked(index), "word one is a number");
    finish(&mut rt);
}
