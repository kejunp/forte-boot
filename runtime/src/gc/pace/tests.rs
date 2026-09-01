// That the goal is proportional and the assist is bounded.
//
// Pacing is the part of a collector that is wrong slowly. A goal that is too
// low collects constantly and recovers little; one that is too high grows the
// heap without bound. Neither is a failure a test can catch by running a
// program, so what is checked here is the shape of the arithmetic.

use super::*;

#[test]
fn the_goal_grows_with_what_survived() {
    let small = goal(100 << 20);
    let large = goal(400 << 20);
    assert!(large > small, "a bigger live heap gets a bigger goal");
    assert!(small > 100 << 20, "and the goal is above the live size");
}

// A hundred per cent means "collect when the heap has doubled", which is what
// GOGC means and what this is a copy of.
#[test]
fn a_hundred_per_cent_is_a_doubling() {
    if percent() != PERCENT {
        return;
    }
    let live = 100usize << 20;
    assert_eq!(goal(live), live * 2);
}

// A program whose live heap is tiny would otherwise collect on every
// allocation, spending its time proving that nothing died.
#[test]
fn a_tiny_live_heap_still_gets_room_to_grow() {
    assert_eq!(goal(0), FIRST);
    assert_eq!(goal(8), FIRST);
    assert!(goal(FIRST) > FIRST);
}

#[test]
fn a_live_heap_too_big_to_double_does_not_wrap() {
    assert!(goal(usize::MAX) >= usize::MAX / 2);
    assert!(goal(usize::MAX - 1) > 0);
}

// ---- Assists ---------------------------------------------------------------

#[test]
fn a_bigger_allocation_does_more_marking() {
    assert!(assist(4096) > assist(64));
}

// Every allocation does at least something, or a program allocating in the
// smallest possible steps would assist nothing at all and outrun the marker
// exactly as if there were no assists.
#[test]
fn even_the_smallest_allocation_assists() {
    assert!(assist(0) >= 1);
    assert!(assist(1) >= 1);
}

// One allocation is not allowed to become a pause. The point is to keep the
// marker ahead, not to finish the cycle in one call.
#[test]
fn one_allocation_never_does_an_unbounded_amount() {
    assert_eq!(assist(usize::MAX), MOST);
    assert!(assist(1 << 30) <= MOST);
}

#[test]
fn the_percentage_is_a_number_or_the_default() {
    assert!(percent() > 0, "nought would be a collection per allocation");
}
