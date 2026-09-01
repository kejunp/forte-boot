// That the pages are really there, checked by writing to them.
//
// A reservation that came back with a plausible address and no memory behind
// it is the one failure here that nothing else would catch: every allocator
// above this would work perfectly and the program would die on the first
// store. So these write to both ends of what they were given and read it back,
// which is the only question this file is actually answering.

use super::*;

#[test]
fn a_page_can_be_written_at_both_ends() {
    let at = map(PAGE).expect("a page");
    unsafe {
        *at = 0x5a;
        *at.add(PAGE - 1) = 0xa5;
        assert_eq!(*at, 0x5a);
        assert_eq!(*at.add(PAGE - 1), 0xa5);
    }
    unmap(at, PAGE);
}

// Anonymous memory arrives as noughts, and the allocator above leans on it:
// an object that was never written reads as nought rather than as whatever the
// last program to hold that page left there.
#[test]
fn what_comes_back_is_already_nought() {
    let at = map(PAGE).expect("a page");
    unsafe {
        for i in 0..PAGE {
            assert_eq!(*at.add(i), 0, "byte {} was not nought", i);
        }
    }
    unmap(at, PAGE);
}

#[test]
fn nothing_is_asked_for_nothing() {
    assert!(map(0).is_none());
}

// ---- Alignment -------------------------------------------------------------

#[test]
fn an_aligned_reservation_starts_on_its_boundary() {
    let at = map_aligned(ARENA, ARENA).expect("an arena");
    assert_eq!(at as usize % ARENA, 0, "{:p} is not on an arena boundary", at);
    unmap(at, ARENA);
}

// The trimming at both ends is where this could go wrong quietly -- give back
// one page too many and the region has a hole in it that reads fine until
// something lands there.
#[test]
fn an_aligned_reservation_is_whole_after_its_ends_are_given_back() {
    let at = map_aligned(ARENA, ARENA).expect("an arena");
    unsafe {
        *at = 1;
        *at.add(ARENA / 2) = 2;
        *at.add(ARENA - 1) = 3;
        assert_eq!(*at, 1);
        assert_eq!(*at.add(ARENA / 2), 2);
        assert_eq!(*at.add(ARENA - 1), 3);
    }
    unmap(at, ARENA);
}

#[test]
fn two_arenas_do_not_overlap() {
    let a = map_aligned(ARENA, ARENA).expect("an arena");
    let b = map_aligned(ARENA, ARENA).expect("another");
    let (a, b) = (a as usize, b as usize);
    assert!(a + ARENA <= b || b + ARENA <= a, "{:x} and {:x} overlap", a, b);
    unmap(a as *mut u8, ARENA);
    unmap(b as *mut u8, ARENA);
}

// The shift is what turns an address into the arena holding it, so it has to
// be the arena's size and not merely near it.
#[test]
fn the_arena_shift_is_the_arena_size() {
    assert_eq!(1usize << ARENA_SHIFT, ARENA);
    assert!(two(ARENA));
    assert!(two(PAGE));
    assert_eq!(ARENA % PAGE, 0);
}

// ---- Rounding --------------------------------------------------------------

#[test]
fn rounding_up_leaves_what_is_already_round_alone() {
    assert_eq!(up(0, 8), 0);
    assert_eq!(up(8, 8), 8);
    assert_eq!(up(9, 8), 16);
    assert_eq!(up(15, 8), 16);
    assert_eq!(up(1, PAGE), PAGE);
    // Nothing to round to is nothing to do, rather than a division by nought.
    assert_eq!(up(7, 0), 7);
}

#[test]
fn a_power_of_two_is_one_bit() {
    for n in [1usize, 2, 4, 8, 4096, 8192] {
        assert!(two(n), "{} is a power of two", n);
    }
    for n in [0usize, 3, 6, 12, 8193] {
        assert!(!two(n), "{} is not a power of two", n);
    }
}
