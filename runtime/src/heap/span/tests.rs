// The bits, and the arithmetic that turns an address into an index.
//
// Everything a collector concludes rests on these two. If `holding` is wrong
// by one object then a mark lands on the neighbour and the object that was
// really reached is freed underneath a live pointer -- and the program that
// crashes does so somewhere else entirely, on a read that was correct. So the
// interior cases are written out one address at a time rather than sampled.

use super::*;

fn span(class: usize) -> Span {
    Span::new(0x40000, classes::pages_of(class), class, true)
}

// ---- Bits ------------------------------------------------------------------

#[test]
fn a_bit_that_was_set_reads_as_set_and_its_neighbours_do_not() {
    let mut b = Bits::new(200);
    b.set(64);
    assert!(b.get(64));
    assert!(!b.get(63));
    assert!(!b.get(65));
    assert_eq!(b.count(), 1);
    b.unset(64);
    assert!(!b.get(64));
    assert_eq!(b.count(), 0);
}

// Nothing outside the length exists, and asking is not a panic -- an index
// that came from arithmetic on an address is exactly the thing that can be a
// little too large.
#[test]
fn a_bit_past_the_end_is_not_there_and_does_not_panic() {
    let mut b = Bits::new(10);
    assert!(!b.get(10));
    assert!(!b.get(1000));
    b.set(1000);
    assert_eq!(b.count(), 0);
    assert!(!b.raise(1000));
}

// What a marker asks: the answer is whether this is the first time, because
// the first time is when the object's own contents still have to be walked.
#[test]
fn raising_a_bit_says_whether_it_was_the_first_time() {
    let mut b = Bits::new(8);
    assert!(b.raise(3));
    assert!(!b.raise(3));
}

#[test]
fn the_next_nought_is_found_across_a_word_boundary() {
    let mut b = Bits::new(200);
    for at in 0..130 {
        b.set(at);
    }
    assert_eq!(b.empty_from(0), Some(130));
    assert_eq!(b.empty_from(130), Some(130));
    assert_eq!(b.empty_from(131), Some(131));
}

#[test]
fn a_full_bitmap_has_no_next_nought() {
    let mut b = Bits::new(70);
    for at in 0..70 {
        b.set(at);
    }
    assert_eq!(b.empty_from(0), None);
}

// The tail of the last word is nought and is not an object. A bitmap of
// seventy is two words, and bits seventy to a hundred and twenty-seven must
// not be handed out as free room.
#[test]
fn the_unused_tail_of_the_last_word_is_not_free_room() {
    let mut b = Bits::new(70);
    for at in 0..70 {
        b.set(at);
    }
    assert_eq!(b.empty_from(64), None, "bit 70 is not an object");
}

#[test]
fn what_is_set_here_and_not_there_is_counted() {
    let mut a = Bits::new(100);
    let mut b = Bits::new(100);
    for at in 0..50 {
        a.set(at);
    }
    for at in 40..60 {
        b.set(at);
    }
    assert_eq!(a.without(&b), 40, "nought to thirty-nine");
}

// ---- Where an object is ----------------------------------------------------

#[test]
fn an_address_at_the_start_of_an_object_finds_it() {
    let s = span(4);
    for i in 0..s.count {
        assert_eq!(s.holding(s.base_of(i)), Some(i), "object {}", i);
    }
}

// The case that matters. A pointer to a field is an address partway into an
// object, and it has to keep that object alive rather than nothing.
#[test]
fn an_address_in_the_middle_of_an_object_finds_the_same_object() {
    let s = span(6);
    for i in 0..s.count {
        for byte in 0..s.size {
            assert_eq!(
                s.holding(s.base_of(i) + byte),
                Some(i),
                "byte {} of object {}",
                byte,
                i
            );
        }
    }
}

#[test]
fn an_address_outside_the_span_finds_nothing() {
    let s = span(4);
    assert_eq!(s.holding(s.at - 1), None);
    assert_eq!(s.holding(s.at + s.count * s.size), None);
    assert_eq!(s.holding(0), None);
}

// The tail the size-class table leaves at the end of a span is not part of any
// object, and a word pointing into it points at nothing.
#[test]
fn an_address_in_the_tail_waste_finds_nothing() {
    let s = span(3);
    let last = s.at + s.count * s.size;
    if last < s.ends() {
        assert_eq!(s.holding(last), None, "the tail is not an object");
    }
}

// ---- Handing objects out ---------------------------------------------------

#[test]
fn a_span_hands_out_every_object_once_and_then_nothing() {
    let mut s = span(5);
    let mut held = Vec::new();
    while let Some(at) = s.take() {
        assert!(!held.contains(&at), "object {} was handed out twice", at);
        held.push(at);
    }
    assert_eq!(held.len(), s.count);
    assert!(s.full());
    assert_eq!(s.free(), 0);
}

#[test]
fn two_objects_of_a_span_do_not_overlap() {
    let s = span(9);
    for i in 1..s.count {
        assert_eq!(s.base_of(i) - s.base_of(i - 1), s.size);
    }
    assert!(s.base_of(s.count - 1) + s.size <= s.ends());
}

// ---- Sweeping --------------------------------------------------------------

#[test]
fn what_was_not_marked_is_freed_and_what_was_is_kept() {
    let mut s = span(4);
    for _ in 0..10 {
        s.take();
    }
    for at in [1usize, 3, 7] {
        s.mark(at);
    }
    let gone = s.sweep(1);
    assert_eq!(gone, 7, "ten were taken and three were reached");
    for at in 0..10 {
        assert_eq!(s.taken(at), [1, 3, 7].contains(&at), "object {}", at);
    }
    assert_eq!(s.swept, 1);
}

// A sweep puts the search back to the front, because the room it freed is
// behind wherever the last allocation had got to.
#[test]
fn a_sweep_makes_the_room_it_freed_findable_again() {
    let mut s = span(4);
    while s.take().is_some() {}
    assert!(s.full());
    s.mark(0);
    s.sweep(1);
    assert!(!s.full());
    assert_eq!(s.take(), Some(1), "nought survived, so one is the first free");
}

#[test]
fn nothing_marked_frees_the_whole_span() {
    let mut s = span(2);
    let mut taken = 0;
    while s.take().is_some() {
        taken += 1;
    }
    assert_eq!(s.sweep(1), taken);
    assert_eq!(s.free(), s.count);
}

// ---- Which words are pointers ----------------------------------------------

#[test]
fn the_words_a_shape_called_pointers_are_the_ones_read_back() {
    let mut s = span(4);
    // Four words, of which the second and the fourth hold pointers.
    s.describe(0, &[0b1010], 4);
    assert!(!s.points(0, 0));
    assert!(s.points(0, 1));
    assert!(!s.points(0, 2));
    assert!(s.points(0, 3));
}

// Each object has its own run of bits, so two objects of the same size and
// different types share a span without sharing a description.
#[test]
fn two_objects_in_one_span_are_described_separately() {
    let mut s = span(4);
    s.describe(0, &[0b0001], 4);
    s.describe(1, &[0b1000], 4);
    assert!(s.points(0, 0));
    assert!(!s.points(0, 3));
    assert!(!s.points(1, 0));
    assert!(s.points(1, 3));
}

// Describing an object again has to leave nothing of the last description
// behind -- the room is reused, and the type that reused it is the only one
// that should be believed.
#[test]
fn describing_an_object_again_forgets_what_it_said_before() {
    let mut s = span(4);
    s.describe(0, &[0b1111], 4);
    s.describe(0, &[0b0001], 4);
    assert!(s.points(0, 0));
    assert!(!s.points(0, 1));
    assert!(!s.points(0, 2));
    assert!(!s.points(0, 3));
}

// A span nothing scans holds no description at all, which is most of the point
// of having the split.
#[test]
fn a_span_that_is_never_scanned_keeps_no_description() {
    let mut s = Span::new(0x40000, 1, 4, false);
    assert_eq!(s.ptrs.len(), 0);
    s.describe(0, &[0b1111], 4);
    assert!(!s.points(0, 0), "nothing in here is a pointer by construction");
}

// ---- A large object --------------------------------------------------------

#[test]
fn an_object_with_a_span_to_itself_is_the_whole_span() {
    let s = Span::new(0x40000, 8, 0, true);
    assert_eq!(s.count, 1);
    assert_eq!(s.size, s.bytes());
    assert_eq!(s.holding(s.at), Some(0));
    assert_eq!(s.holding(s.ends() - 1), Some(0));
    assert_eq!(s.holding(s.ends()), None);
}
