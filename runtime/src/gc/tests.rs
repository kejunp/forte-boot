// That what is reachable survives and what is not does not.
//
// Every test here gives the roots rather than letting them be found. That is
// the only way to ask the question: a conservative scan of a running stack
// finds whatever the last few calls happened to leave on it, so a test that
// allocated something, dropped the variable and asked whether it was collected
// would be asking whether a dead slot had been written over yet. `cycle_from`
// makes the reachable set exactly what the test says it is, and everything
// after the roots are shaded is the same code the real path runs.
//
// The heaps are built as linked lists, because a list is the shape where being
// wrong is visible: a marker that stops one step early keeps the head and
// loses the tail, and there is no way for that to look like an accident.
//
// Nothing here asserts on `phase()`. That is the flag the write barrier reads
// outside the lock, and it is one flag for the whole process -- so a runtime
// built by one test raises and lowers the same flag another test is looking
// at. What a cycle is doing is `rt.gc.phase`, which belongs to the runtime it
// is about; the flag is checked in `abi`, where the tests take each other in
// turn.

use super::super::shape::{Kind, Made};
use super::super::{alloc, Runtime};
use super::*;

// A node: a pointer at word nought and a number at word one, so that every
// node has something the marker must follow and something it must not.
fn node_shape() -> Made {
    Made::new(16, 8, Kind::Opaque).points_at(0)
}

fn node(rt: &mut Runtime, shape: &Made, next: usize, held: usize) -> usize {
    let at = alloc::object(rt, 16, Some(shape.shape()));
    unsafe {
        *(at as *mut usize) = next;
        *((at + 8) as *mut usize) = held;
    }
    at
}

// A chain of `n` nodes, newest first, with the address of each.
fn chain(rt: &mut Runtime, shape: &Made, n: usize) -> Vec<usize> {
    let mut held = Vec::new();
    let mut last = 0;
    for i in 0..n {
        last = node(rt, shape, last, i);
        held.push(last);
    }
    held
}

fn alive(rt: &Runtime, at: usize) -> bool {
    rt.heap.holding(at).is_some()
}

// ---- What survives ---------------------------------------------------------

#[test]
fn a_list_reached_from_a_root_survives_all_the_way_down() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 200);
    let head = *held.last().expect("a head");

    cycle_from(&mut rt, &[head]);
    for (i, at) in held.iter().enumerate() {
        assert!(alive(&rt, *at), "node {} was collected", i);
    }
}

// The other half, and the one a collector that never freed anything would
// pass silently.
#[test]
fn a_list_nothing_points_at_is_collected_whole() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 200);

    cycle_from(&mut rt, &[]);
    for (i, at) in held.iter().enumerate() {
        assert!(!alive(&rt, *at), "node {} survived with nothing pointing at it", i);
    }
}

// Two lists, one held and one not. This is the test that catches a sweep that
// frees by span rather than by object.
#[test]
fn what_is_held_survives_beside_what_is_not() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let kept = chain(&mut rt, &shape, 50);
    let gone = chain(&mut rt, &shape, 50);
    let head = *kept.last().expect("a head");

    cycle_from(&mut rt, &[head]);
    for at in &kept {
        assert!(alive(&rt, *at), "a held node was collected");
    }
    for at in &gone {
        assert!(!alive(&rt, *at), "an unheld node survived");
    }
}

// A cycle in the graph must not be a loop in the marker. The mark bit is what
// stops it: an object already marked is not pushed a second time.
#[test]
fn a_ring_of_nodes_is_walked_once_and_survives() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 10);
    let (head, tail) = (*held.last().expect("a head"), held[0]);
    unsafe { *(tail as *mut usize) = head };

    cycle_from(&mut rt, &[head]);
    for at in &held {
        assert!(alive(&rt, *at));
    }
}

// A word inside an object rather than at its start. A pointer to a field is
// what a program mostly has, and it has to keep the whole object.
#[test]
fn a_root_pointing_into_the_middle_of_an_object_keeps_it() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 5);
    let head = *held.last().expect("a head");

    cycle_from(&mut rt, &[head + 8]);
    for at in &held {
        assert!(alive(&rt, *at), "reached through the second word of the head");
    }
}

// ---- What is not followed --------------------------------------------------

// The whole value of the shape. Word one of a node is a number, and a number
// that happens to be the address of a dead object must not keep it alive --
// which is exactly what the stack scan cannot promise and the heap scan can.
#[test]
fn a_number_in_an_object_is_not_followed() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let victim = node(&mut rt, &shape, 0, 0);
    let holder = node(&mut rt, &shape, 0, victim);

    cycle_from(&mut rt, &[holder]);
    assert!(alive(&rt, holder));
    assert!(!alive(&rt, victim), "word one is a number and was followed anyway");
}

#[test]
fn an_object_with_no_pointers_in_it_is_never_read() {
    let mut rt = Runtime::new();
    let plain = Made::new(64, 8, Kind::Opaque);
    let at = alloc::object(&mut rt, 64, Some(plain.shape()));
    let (id, _) = rt.heap.holding(at).expect("a span");
    assert!(!rt.heap.span(id).scan);

    cycle_from(&mut rt, &[at]);
    assert!(alive(&rt, at), "it was a root, so it survives");
    assert!(rt.gc.work.is_empty());
}

// ---- What is allocated while a cycle runs ----------------------------------

// It cannot be garbage: the marker is working from a picture of the heap that
// could not have included it. Sweeping it would free something the program is
// holding right now.
#[test]
fn something_made_during_a_cycle_survives_that_cycle() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    start_from(&mut rt, &[]);
    let at = node(&mut rt, &shape, 0, 0);
    while step(&mut rt, SLICE) {}
    finish(&mut rt);
    sweep::all(&mut rt);
    assert!(alive(&rt, at));
}

// And is collected by the next one, or "allocate black" would be "allocate
// immortal".
#[test]
fn something_made_during_a_cycle_is_collected_by_the_next() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    start_from(&mut rt, &[]);
    let at = node(&mut rt, &shape, 0, 0);
    while step(&mut rt, SLICE) {}
    finish(&mut rt);
    sweep::all(&mut rt);

    cycle_from(&mut rt, &[]);
    assert!(!alive(&rt, at));
}

// ---- The phases ------------------------------------------------------------

#[test]
fn a_cycle_leaves_the_barrier_off_and_the_number_moved_on() {
    let mut rt = Runtime::new();
    let before = rt.gc.cycle;
    cycle_from(&mut rt, &[]);
    assert_eq!(rt.gc.phase, Phase::Off);
    assert!(!rt.gc.black);
    assert_eq!(rt.gc.cycle, before + 1);
    assert_eq!(rt.gc.cycles, 1);
}

#[test]
fn the_barrier_is_on_for_as_long_as_the_marker_is_walking() {
    let mut rt = Runtime::new();
    start_from(&mut rt, &[]);
    assert_eq!(rt.gc.phase, Phase::Mark);
    assert!(rt.gc.black);
    finish(&mut rt);
    assert_eq!(rt.gc.phase, Phase::Off);
}

// Starting one while one is running does nothing, or the second would clear
// the work list the first was in the middle of.
#[test]
fn a_cycle_started_twice_is_one_cycle() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 20);
    let head = *held.last().expect("a head");

    start_from(&mut rt, &[head]);
    let waiting = rt.gc.work.len();
    start_from(&mut rt, &[]);
    assert_eq!(rt.gc.work.len(), waiting, "the second start emptied the list");
    finish(&mut rt);
    sweep::all(&mut rt);
    for at in &held {
        assert!(alive(&rt, *at));
    }
}

// A cycle with no stack base does not run at all, which is the safe half of
// not knowing where the roots are.
#[test]
fn nothing_collects_until_something_says_where_the_stack_is() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 5);
    // `start` and not `start_from`: the roots would have to be found.
    start(&mut rt, roots::here());
    assert_eq!(rt.gc.phase, Phase::Off, "it should not have begun");
    for at in &held {
        assert!(alive(&rt, *at));
    }
}

// ---- Room nothing collects -------------------------------------------------

#[test]
fn what_alloc_handed_out_survives_every_cycle() {
    let mut rt = Runtime::new();
    let at = alloc::kept(&mut rt, 100);
    for _ in 0..3 {
        cycle_from(&mut rt, &[]);
        assert!(alive(&rt, at), "it is not the collector's to take");
    }
}

// ---- Counting --------------------------------------------------------------

#[test]
fn what_survived_is_what_the_next_goal_is_set_against() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 100);
    let head = *held.last().expect("a head");

    cycle_from(&mut rt, &[head]);
    assert!(rt.gc.live >= 100 * 16, "a hundred nodes of sixteen bytes survived");
    assert_eq!(rt.gc.goal, pace::goal(rt.gc.live));
}

#[test]
fn a_cycle_that_freed_nothing_says_so() {
    let mut rt = Runtime::new();
    cycle_from(&mut rt, &[]);
    assert_eq!(rt.gc.freed, 0);

    let shape = node_shape();
    chain(&mut rt, &shape, 10);
    cycle_from(&mut rt, &[]);
    assert!(rt.gc.freed > 0, "ten nodes died and none were counted");
}

// ---- Assisting -------------------------------------------------------------

// A program that allocates during a cycle does marking work for it, which is
// what stops it outrunning the marker.
#[test]
fn allocating_during_a_cycle_does_some_of_the_marking() {
    let mut rt = Runtime::new();
    let shape = node_shape();
    let held = chain(&mut rt, &shape, 500);
    let head = *held.last().expect("a head");

    start_from(&mut rt, &[head]);
    let waiting = rt.gc.work.len();
    after(&mut rt, 4096, roots::here());
    assert!(rt.gc.work.len() < waiting + 1, "an assist did nothing at all");
    assert!(rt.gc.phase == Phase::Mark, "an assist is not a second cycle");
}

// And a heap that has grown past its goal starts one, which is the only thing
// that ever starts one without being asked.
#[test]
fn a_heap_past_its_goal_starts_a_cycle() {
    let mut rt = Runtime::new();
    roots::note();
    let shape = node_shape();
    node(&mut rt, &shape, 0, 0);
    rt.gc.goal = 1;
    after(&mut rt, 8, roots::here());
    assert_eq!(rt.gc.phase, Phase::Mark);
    finish(&mut rt);
}
