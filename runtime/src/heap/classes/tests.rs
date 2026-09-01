// That the table is a table, and that the lookup agrees with it.
//
// The table itself is copied and cannot be checked against anything -- there
// is no derivation here to re-run. What can be checked is that it is
// internally consistent and that the two lookup arrays built from it give the
// same answers a search over it would: a class that holds less than it was
// asked for is a heap corruption waiting for the first object that uses its
// last byte, and it would show up nowhere near here.

use super::*;

// ---- The table -------------------------------------------------------------

#[test]
fn every_class_is_bigger_than_the_one_before_it() {
    for c in 2..=COUNT {
        assert!(
            size_of(c) > size_of(c - 1),
            "class {} is {} and class {} is {}",
            c,
            size_of(c),
            c - 1,
            size_of(c - 1)
        );
    }
}

// Everything the allocator hands out has to be usable for a pointer, and a
// pointer wants to be on a word. Every size being a multiple of eight is what
// makes that true without the allocator ever rounding again.
#[test]
fn every_size_is_a_whole_number_of_words() {
    for c in 1..=COUNT {
        assert_eq!(size_of(c) % 8, 0, "class {} is {} bytes", c, size_of(c));
    }
}

#[test]
fn a_span_holds_a_whole_number_of_objects_and_at_least_one() {
    for c in 1..=COUNT {
        assert!(count_of(c) >= 1, "class {} holds nothing", c);
        assert!(
            count_of(c) * size_of(c) <= bytes_of(c),
            "class {} overruns its span",
            c
        );
    }
}

// The pair of numbers in each row is chosen so the tail is small. Go's own
// bound is 12.5% of the span; the rows here keep well inside it, and a row
// that did not would be a row that was mistyped.
#[test]
fn the_tail_left_at_the_end_of_a_span_is_small() {
    for c in 1..=COUNT {
        let tail = bytes_of(c) - count_of(c) * size_of(c);
        assert!(
            tail * 8 <= bytes_of(c),
            "class {} wastes {} of {} bytes",
            c,
            tail,
            bytes_of(c)
        );
    }
}

// The other half of what the table trades against: the step up from one class
// to the next is what an object pays for not being exactly a class size. The
// first rows step by a fixed few bytes, because a quarter of sixteen is four
// and there is nothing between eight and sixteen worth having; past them the
// step becomes proportional.
#[test]
fn the_step_up_to_the_next_class_is_small() {
    for c in 2..=18 {
        let step = size_of(c) - size_of(c - 1);
        assert!(step <= 16, "class {} steps up by {}", c, step);
    }
    for c in 19..=COUNT {
        let step = size_of(c) - size_of(c - 1);
        assert!(
            step * 4 <= size_of(c),
            "class {} steps up by {} from {}",
            c,
            step,
            size_of(c - 1)
        );
    }
}

#[test]
fn the_last_class_is_the_biggest_thing_that_shares_a_span() {
    assert_eq!(size_of(COUNT), MAX);
}

// ---- The lookup ------------------------------------------------------------

// The one that matters. Every size from nothing to the largest gets a class
// that is at least as big as it asked for and no bigger than it had to be --
// which is the whole contract, checked over every size rather than a few.
#[test]
fn every_size_gets_the_smallest_class_that_holds_it() {
    for bytes in 1..=MAX {
        let c = class_of(bytes).expect("a class");
        assert!(
            size_of(c) >= bytes,
            "{} bytes went in class {}, which is {}",
            bytes,
            c,
            size_of(c)
        );
        assert!(
            c == 1 || size_of(c - 1) < bytes,
            "{} bytes went in class {} and would have fitted class {}",
            bytes,
            c,
            c - 1
        );
    }
}

#[test]
fn a_size_that_is_exactly_a_class_gets_that_class() {
    for c in 1..=COUNT {
        assert_eq!(class_of(size_of(c)), Some(c), "class {}", c);
    }
}

#[test]
fn anything_past_the_last_class_has_none() {
    assert_eq!(class_of(MAX + 1), None);
    assert_eq!(class_of(1 << 20), None);
    assert!(class_of(MAX).is_some());
}

// Nothing asks for nothing often, but a field-less struct is a real type and
// the allocator must not hand back an address two of them share by accident.
#[test]
fn nothing_still_gets_room() {
    assert_eq!(class_of(0), Some(1));
}

// ---- Tiny ------------------------------------------------------------------

#[test]
fn the_tiny_block_is_a_class_of_its_own() {
    assert_eq!(class_of(TINY), Some(2));
    assert_eq!(size_of(2), TINY);
}
