// The symbols as a compiled program would call them.
//
// Everything underneath is tested against a runtime of its own; these go
// through the real entry points and the real global, which is the only way to
// check the two things this file is actually responsible for: that a handle
// means what the next call thinks it means, and that a register that was never
// filled is caught rather than followed.
//
// They share one global runtime, so they are taken one at a time. That is not
// tidiness: one of them collects, and a collection scans the stack of the
// thread that asked for it and no other -- so an object another test was
// holding on its own stack would be freed underneath it. The runtime is
// written for one mutator and this is a test binary with a dozen, which is a
// thing the tests have to arrange around rather than a thing the runtime is
// wrong about.

use std::sync::{Mutex, MutexGuard, OnceLock};

use super::super::shape::{Kind, Made};
use super::*;

static ORDER: OnceLock<Mutex<()>> = OnceLock::new();

fn alone() -> MutexGuard<'static, ()> {
    match ORDER.get_or_init(|| Mutex::new(())).lock() {
        Ok(held) => held,
        Err(held) => held.into_inner(),
    }
}

fn number() -> Made {
    Made::new(8, 8, Kind::Signed)
}

fn text() -> Made {
    Made::new(16, 8, Kind::Str).indirect()
}

// ---- Room ------------------------------------------------------------------

#[test]
fn asking_for_room_gives_room_that_can_be_written_to() {
    let _alone = alone();
    let at = __rt_alloc(64);
    assert!(!at.is_null());
    unsafe {
        std::ptr::write_bytes(at, 0x5a, 64);
        assert_eq!(*at, 0x5a);
        assert_eq!(*at.add(63), 0x5a);
    }
}

#[test]
fn asking_for_collected_room_gives_room_the_collector_knows_about() {
    let _alone = alone();
    let shape = Made::new(32, 8, Kind::Opaque).points_at(8);
    let at = __rt_gc_alloc(32, shape.bytes().as_ptr());
    assert!(!at.is_null());
    let rt = runtime();
    let (id, index) = rt.heap.holding(at as usize).expect("a span");
    assert!(rt.heap.span(id).scan, "its shape said it holds a pointer");
    assert!(rt.heap.span(id).points(index, 1));
}

// A null shape says nothing about the contents, which is the same as saying
// there are no pointers in it.
#[test]
fn room_with_no_shape_is_room_nothing_scans() {
    let _alone = alone();
    let at = __rt_gc_alloc(48, std::ptr::null());
    let rt = runtime();
    let (id, _) = rt.heap.holding(at as usize).expect("a span");
    assert!(!rt.heap.span(id).scan);
}

#[test]
fn asking_for_a_negative_amount_of_room_is_asking_for_none() {
    let _alone = alone();
    let at = __rt_gc_alloc(-8, std::ptr::null());
    assert!(!at.is_null(), "one byte, rather than a crash");
}

// ---- The barrier -----------------------------------------------------------

#[test]
fn writing_through_the_barrier_writes() {
    let _alone = alone();
    let mut held: usize = 1;
    __rt_write(&mut held as *mut usize, 99);
    assert_eq!(held, 99);
}

#[test]
fn copying_through_the_barrier_copies() {
    let _alone = alone();
    let shape = Made::new(24, 8, Kind::Opaque).points_at(0);
    let from: [u8; 24] = [4; 24];
    let mut to: [u8; 24] = [0; 24];
    __rt_copy(to.as_mut_ptr(), from.as_ptr(), shape.bytes().as_ptr());
    assert_eq!(to, from);
}

// Nothing said how big it is, so there is nothing that can be moved -- and a
// null that was read as a size would be a copy of whatever the first eight
// bytes at address nought happened to be.
#[test]
fn copying_with_no_shape_moves_nothing() {
    let _alone = alone();
    let from: [u8; 8] = [7; 8];
    let mut to: [u8; 8] = [0; 8];
    __rt_copy(to.as_mut_ptr(), from.as_ptr(), std::ptr::null());
    assert_eq!(to, [0; 8]);
}

// ---- Handles ---------------------------------------------------------------

// Nought is not a handle, so a register that was never filled is caught here
// rather than followed into the list.
#[test]
fn nought_is_not_a_handle() {
    let _alone = alone();
    assert_eq!(which(0), None);
    __rt_map_insert(0, 1, 2);
    __rt_set_insert(0, 1);
    assert_eq!(__rt_iter_valid(0, 0), 0);
    assert_eq!(__rt_iter_elem(0, 0), 0);
}

// The low bit is what lets the three cursor routines, which the compiler emits
// for both, tell a map from a set.
#[test]
fn a_handle_says_whether_it_is_a_map_or_a_set() {
    let _alone = alone();
    assert_eq!(which(handle(3, false)), Some((3, false)));
    assert_eq!(which(handle(3, true)), Some((3, true)));
    assert_ne!(handle(3, false), handle(3, true));
    assert_ne!(handle(0, false), 0);
}

#[test]
fn a_map_handle_is_not_a_set_handle() {
    let _alone = alone();
    let shape = number();
    let map = __rt_map_new(shape.bytes().as_ptr(), shape.bytes().as_ptr());
    __rt_set_insert(map, 5);
    assert_eq!(__rt_iter_valid(map, 0), 0, "nothing went in through the wrong door");
}

// ---- A map from end to end -------------------------------------------------

#[test]
fn a_map_built_through_the_symbols_walks_back_out_in_order() {
    let _alone = alone();
    let shape = number();
    let held = __rt_map_new(shape.bytes().as_ptr(), shape.bytes().as_ptr());
    assert_ne!(held, 0);
    for key in [7usize, 2, 5] {
        __rt_map_insert(held, key, key * 10);
    }

    let mut out = Vec::new();
    let mut at = __rt_iter_step(held, -1);
    while __rt_iter_valid(held, at) != 0 {
        let pair = __rt_iter_elem(held, at);
        unsafe { out.push((*(pair as *const usize), *((pair + 8) as *const usize))) };
        at = __rt_iter_step(held, at);
    }
    assert_eq!(out, vec![(2, 20), (5, 50), (7, 70)]);
}

#[test]
fn a_hashed_map_built_through_the_symbols_holds_everything() {
    let _alone = alone();
    let shape = number();
    let held = __rt_hashmap_new(shape.bytes().as_ptr(), shape.bytes().as_ptr());
    for key in 0..200usize {
        __rt_hashmap_insert(held, key, key + 1);
    }
    let mut seen = 0;
    let mut at = __rt_iter_step(held, -1);
    while __rt_iter_valid(held, at) != 0 {
        let pair = __rt_iter_elem(held, at);
        unsafe {
            assert_eq!(*((pair + 8) as *const usize), *(pair as *const usize) + 1);
        }
        seen += 1;
        at = __rt_iter_step(held, at);
    }
    assert_eq!(seen, 200);
}

// ---- A set from end to end -------------------------------------------------

#[test]
fn a_set_built_through_the_symbols_walks_back_out() {
    let _alone = alone();
    let shape = number();
    let held = __rt_set_new(shape.bytes().as_ptr());
    for one in [4usize, 1, 4, 9] {
        __rt_set_insert(held, one);
    }
    let mut out = Vec::new();
    let mut at = __rt_iter_step(held, -1);
    while __rt_iter_valid(held, at) != 0 {
        out.push(__rt_iter_elem(held, at));
        at = __rt_iter_step(held, at);
    }
    assert_eq!(out, vec![1, 4, 9], "in order, and four only once");
}

#[test]
fn a_hashed_set_holds_each_thing_once() {
    let _alone = alone();
    let shape = number();
    let held = __rt_hashset_new(shape.bytes().as_ptr());
    for one in 0..100usize {
        __rt_hashset_insert(held, one % 40);
    }
    let mut seen = 0;
    let mut at = __rt_iter_step(held, -1);
    while __rt_iter_valid(held, at) != 0 {
        seen += 1;
        at = __rt_iter_step(held, at);
    }
    assert_eq!(seen, 40);
}

// A key that arrives as an address of a pair, which is what a `str` is.
#[test]
fn a_map_with_string_keys_finds_what_it_put_in() {
    let _alone = alone();
    let shape = text();
    let value = number();
    let held = __rt_map_new(shape.bytes().as_ptr(), value.bytes().as_ptr());
    let words: [&[u8]; 3] = [b"pear", b"apple", b"fig"];
    for (at, one) in words.iter().enumerate() {
        let pair: [usize; 2] = [one.as_ptr() as usize, one.len()];
        __rt_map_insert(held, pair.as_ptr() as usize, at);
    }

    let mut out = Vec::new();
    let mut at = __rt_iter_step(held, -1);
    while __rt_iter_valid(held, at) != 0 {
        let entry = __rt_iter_elem(held, at);
        unsafe {
            let key = *(entry as *const usize) as *const usize;
            let (text, len) = (*key, *key.add(1));
            out.push(
                String::from_utf8_lossy(std::slice::from_raw_parts(text as *const u8, len))
                    .to_string(),
            );
        }
        at = __rt_iter_step(held, at);
    }
    assert_eq!(out, vec!["apple", "fig", "pear"], "in order, as `Map` promises");
}

// ---- Nothing to walk -------------------------------------------------------

#[test]
fn walking_something_empty_stops_at_once() {
    let _alone = alone();
    let shape = number();
    let held = __rt_set_new(shape.bytes().as_ptr());
    let at = __rt_iter_step(held, -1);
    assert_eq!(__rt_iter_valid(held, at), 0);
}

// ---- Collecting ------------------------------------------------------------

// A cycle through the real entry point, on a thread that said where its stack
// is. What is asserted is that it ran and did not take what the caller is
// holding -- the collector's own tests are where the freeing is checked.
#[test]
fn a_collection_through_the_symbols_keeps_what_is_still_held() {
    let _alone = alone();
    std::thread::spawn(|| {
        __rt_init();
        let shape = Made::new(16, 8, Kind::Opaque).points_at(0);
        let at = __rt_gc_alloc(16, shape.bytes().as_ptr());
        assert!(!at.is_null());
        let before = runtime().gc.cycles;
        __rt_collect();
        assert!(runtime().gc.cycles > before, "no cycle ran");
        assert!(runtime().heap.holding(at as usize).is_some(), "it is on the stack");
        std::hint::black_box(at);
    })
    .join()
    .expect("a thread");
}

// ---- The thread ------------------------------------------------------------

// The one test that runs the collector the way a program would: a background
// thread marking while the mutator allocates, rather than three calls made one
// after another.
//
// What it can assert is deliberately weak, and that is the honest position. A
// concurrent collector has no state a test can name at a moment -- ask whether
// a cycle is running and the answer is already out of date. So what is checked
// is the two things that must be true afterwards whatever the interleaving
// was: cycles happened, and the list the mutator was holding all the way
// through is whole. A test that passed by luck would be one where no cycle ran
// at all, which the first assertion is there to rule out.
#[test]
fn the_collector_runs_beside_a_program_that_is_allocating() {
    let _alone = alone();
    std::thread::spawn(|| {
        __rt_init();
        let node = Made::new(16, 8, Kind::Opaque).points_at(0);

        // A list the mutator keeps a hold of throughout.
        let mut head = 0usize;
        for _ in 0..500 {
            let at = __rt_gc_alloc(16, node.bytes().as_ptr()) as usize;
            __rt_write(at as *mut usize, head);
            head = at;
        }

        // And a great deal of rubbish beside it, enough to pass the goal
        // several times over and so to start several cycles.
        let before = runtime().gc.cycles;
        for _ in 0..40_000 {
            __rt_gc_alloc(256, node.bytes().as_ptr());
        }
        // The thread does its marking between our allocations, so give it the
        // chance -- and finish anything still in flight ourselves, which is
        // what a program asking for a collection does.
        __rt_collect();
        let after = runtime().gc.cycles;
        assert!(after > before, "no cycle ran at all: {} to {}", before, after);

        // The list is whole, every one of the five hundred.
        let mut at = head;
        let mut seen = 0;
        while at != 0 {
            assert!(runtime().heap.holding(at).is_some(), "node {} was collected", seen);
            at = unsafe { *(at as *const usize) };
            seen += 1;
        }
        assert_eq!(seen, 500);
        std::hint::black_box(head);
    })
    .join()
    .expect("a thread");
}

// The heap does not grow without bound when everything dies. This is the
// property the whole runtime exists for, and it is the one that fails silently
// -- a collector that never freed anything would pass every other test here.
#[test]
fn a_program_that_throws_everything_away_does_not_grow_without_bound() {
    let _alone = alone();
    std::thread::spawn(|| {
        __rt_init();
        let node = Made::new(16, 8, Kind::Opaque).points_at(0);
        for _ in 0..20_000 {
            __rt_gc_alloc(512, node.bytes().as_ptr());
        }
        __rt_collect();
        let held = runtime().heap.live;
        assert!(
            held < 4 << 20,
            "ten megabytes of garbage left {} bytes live",
            held
        );
    })
    .join()
    .expect("a thread");
}

// ---- The flag the barrier reads ---------------------------------------------

// The phase again, outside the lock. It is one flag for the whole process, so
// this is the one place it can be asserted: these tests take each other in
// turn and nothing else here raises it.
#[test]
fn the_flag_the_barrier_reads_follows_the_cycle() {
    let _alone = alone();
    assert_eq!(super::super::gc::phase(), super::super::gc::Phase::Off);
    let stack = super::super::gc::roots::here();
    {
        let mut rt = runtime();
        super::super::gc::roots::note();
        super::super::gc::start(&mut rt, stack);
    }
    assert_eq!(
        super::super::gc::phase(),
        super::super::gc::Phase::Mark,
        "a cycle is running and the barrier does not know"
    );
    __rt_collect();
    assert_eq!(super::super::gc::phase(), super::super::gc::Phase::Off);
}
