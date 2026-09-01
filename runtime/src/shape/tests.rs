// That what one side wrote is what the other side reads.
//
// A descriptor is bytes at an address and nothing checks it. Every field is a
// fixed offset agreed between two programs that are compiled separately, so
// the failure mode is not an error -- it is a size read out of the alignment's
// place, an object allocated with the wrong number of bytes, and a heap that
// is wrong everywhere. These pin the offsets by building one and reading it
// back, which is the only check there can be until the compiler's own tests
// build the same bytes.

use super::*;

#[test]
fn what_was_written_at_each_offset_is_what_is_read_from_it() {
    let made = Made::new(24, 8, Kind::Opaque);
    let held = made.shape();
    assert_eq!(held.bytes(), 24);
    assert_eq!(held.align(), 8);
    assert_eq!(held.words(), 3);
    assert_eq!(held.kind(), Kind::Opaque);
    assert!(!held.indirect());
}

// The map begins on a word, which is what the six bytes of nothing after the
// two flags are for -- so a descriptor can be read as words wherever that is
// convenient without the map falling across a boundary.
#[test]
fn the_map_starts_on_a_word() {
    assert_eq!(HEADER % 8, 0);
    assert_eq!(HEADER, 32);
}

#[test]
fn every_kind_survives_being_written_and_read() {
    for kind in [
        Kind::Opaque,
        Kind::Signed,
        Kind::Unsigned,
        Kind::Float,
        Kind::Pointer,
        Kind::Str,
    ] {
        let made = Made::new(8, 8, kind);
        assert_eq!(made.shape().kind(), kind, "{:?}", kind);
    }
}

// Anything the two sides do not agree on has to read as the dullest answer
// rather than as a panic: a byte from an older compiler is a byte this does
// not know, and treating it as opaque is wrong in a way that still runs.
#[test]
fn a_kind_nothing_knows_is_opaque() {
    assert_eq!(Kind::of(200), Kind::Opaque);
    assert_eq!(Kind::of(6), Kind::Opaque);
}

// ---- The map ---------------------------------------------------------------

#[test]
fn the_words_called_pointers_are_the_ones_that_read_back_as_pointers() {
    // Four words, the second and the fourth holding pointers -- a struct of
    // an integer, a reference, an integer and a reference.
    let made = Made::new(32, 8, Kind::Opaque).points_at(8).points_at(24);
    let held = made.shape();
    assert!(!held.points(0));
    assert!(held.points(1));
    assert!(!held.points(2));
    assert!(held.points(3));
    assert!(held.scan());
}

#[test]
fn a_type_with_no_pointers_is_not_scanned() {
    let made = Made::new(64, 8, Kind::Opaque);
    assert!(!made.shape().scan());
    assert!(!made.shape().points(0));
}

// A map longer than one byte, which is where an off-by-one in the shift would
// show up: word eight is the low bit of byte one, not the top bit of byte
// nought.
#[test]
fn a_map_longer_than_a_byte_counts_from_the_low_bit_of_each() {
    let made = Made::new(128, 8, Kind::Opaque).points_at(0).points_at(64);
    let held = made.shape();
    assert_eq!(held.words(), 16);
    assert!(held.points(0));
    assert!(held.points(8), "word eight is the low bit of the second byte");
    for word in 1..16 {
        if word != 8 {
            assert!(!held.points(word), "word {}", word);
        }
    }
}

#[test]
fn a_word_past_the_end_is_not_a_pointer() {
    let made = Made::new(8, 8, Kind::Pointer).points_at(0);
    assert!(made.shape().points(0));
    assert!(!made.shape().points(1));
    assert!(!made.shape().points(1000));
}

// Saying a word past the end holds a pointer says nothing, rather than writing
// over whatever follows the descriptor.
#[test]
fn pointing_past_the_end_writes_nothing() {
    let made = Made::new(8, 8, Kind::Opaque).points_at(800);
    assert!(!made.shape().scan());
    assert_eq!(made.bytes().len(), HEADER + 1);
}

// ---- Indirect --------------------------------------------------------------

// Which says how a caller passed one: a struct arrives as an address and an
// integer arrives as itself, and the runtime reading the second as the first
// would dereference a number.
#[test]
fn indirect_says_how_the_caller_passed_it() {
    let held = Made::new(40, 8, Kind::Opaque).indirect();
    assert!(held.shape().indirect());
    let held = Made::new(4, 4, Kind::Signed);
    assert!(!held.shape().indirect());
}

// ---- Nothing ---------------------------------------------------------------

// A null descriptor is what an allocation with nothing to say passes, and it
// has to be a `None` rather than a read of address nought.
#[test]
fn nothing_is_not_a_shape() {
    assert!(Shape::at(std::ptr::null()).is_none());
    let made = Made::new(8, 8, Kind::Signed);
    assert!(Shape::at(made.bytes().as_ptr()).is_some());
}
