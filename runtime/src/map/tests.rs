// That the two kinds are two kinds, and that a key survives the call it
// arrived on.
//
// The store underneath each is tested in its own file. What is tested here is
// the part that is the same for both and is the part a compiled program
// actually exercises: the key arrives as one register, it may be the address
// of a slot in a frame that is about to go, and what walking one yields has to
// be something the program can read.

use super::super::shape::{Kind, Made};
use super::super::Runtime;
use super::*;

fn number() -> Made {
    Made::new(8, 8, Kind::Signed)
}

fn table(rt: &mut Runtime, hashed: bool, key: &Made, value: &Made) -> usize {
    let held = Table::new(rt, hashed, key.shape(), Some(value.shape()));
    rt.tables.push(held);
    rt.tables.len() - 1
}

// ---- Which kind ------------------------------------------------------------

// §8: "which one you named says how it behaves". The `#` is the whole of the
// difference at the source, and it reaches down to two structures rather than
// one with a flag.
#[test]
fn a_hashed_map_and_an_ordered_one_are_two_different_things() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let ordered = table(&mut rt, false, &k, &v);
    let hashed = table(&mut rt, true, &k, &v);
    assert!(!rt.tables[ordered].hashed());
    assert!(rt.tables[hashed].hashed());
}

// And what the difference is for: the unhashed one keeps its keys in order.
#[test]
fn an_ordered_map_yields_its_keys_in_order() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, false, &k, &v);
    for key in [9usize, 1, 5, 3] {
        insert(&mut rt, which, key, key * 2);
    }
    let held = &rt.tables[which];
    let mut out = Vec::new();
    let mut at = held.step(-1);
    while held.valid(at) {
        let pair = held.elem(at);
        out.push(unsafe { *(pair as *const usize) });
        at = held.step(at);
    }
    assert_eq!(out, vec![1, 3, 5, 9]);
}

// ---- What walking one yields -----------------------------------------------

// A `(K, V)` is a tuple, and a tuple is reached by its address like every
// other aggregate.
#[test]
fn walking_a_map_yields_the_address_of_a_key_and_a_value() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, false, &k, &v);
    insert(&mut rt, which, 4, 44);

    let held = &rt.tables[which];
    let at = held.step(-1);
    let pair = held.elem(at);
    assert_ne!(pair, 0);
    unsafe {
        assert_eq!(*(pair as *const usize), 4);
        assert_eq!(*((pair + 8) as *const usize), 44);
    }
}

// The pair is written over at each turn, which is why it is one allocation and
// not one per turn.
#[test]
fn the_pair_a_map_yields_is_the_same_room_each_turn() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, false, &k, &v);
    insert(&mut rt, which, 1, 10);
    insert(&mut rt, which, 2, 20);

    let held = &rt.tables[which];
    let first = held.elem(0);
    let second = held.elem(1);
    assert_eq!(first, second, "one pair, written over");
    unsafe {
        assert_eq!(*(second as *const usize), 2, "and it holds the second entry");
    }
}

#[test]
fn a_position_that_holds_nothing_yields_nothing() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, false, &k, &v);
    assert_eq!(rt.tables[which].elem(0), 0);
    assert!(!rt.tables[which].valid(0));
}

// ---- Keeping the key -------------------------------------------------------

// The word the caller passed for an indirect key is the address of a slot in
// its frame. Keeping it would be keeping a pointer into a frame that is gone.
#[test]
fn an_indirect_key_is_not_the_callers_after_the_call() {
    let mut rt = Runtime::new();
    let key = Made::new(24, 8, Kind::Opaque).indirect();
    let value = number();
    let which = table(&mut rt, false, &key, &value);

    let mut held: [u8; 24] = [3; 24];
    insert(&mut rt, which, held.as_ptr() as usize, 7);
    // The caller's room is reused, as a frame's is.
    held = [99; 24];
    std::hint::black_box(&held);

    let want: [u8; 24] = [3; 24];
    assert_eq!(rt.tables[which].get(want.as_ptr() as usize), Some(7), "the key was not copied");
}

#[test]
fn a_direct_key_is_kept_as_the_number_it_is() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, true, &k, &v);
    insert(&mut rt, which, 12345, 6);
    assert_eq!(rt.tables[which].get(12345), Some(6));
}

// ---- Counting --------------------------------------------------------------

#[test]
fn a_map_says_how_much_is_in_it() {
    let mut rt = Runtime::new();
    let (k, v) = (number(), number());
    let which = table(&mut rt, true, &k, &v);
    assert!(rt.tables[which].is_empty());
    for key in 0..30usize {
        insert(&mut rt, which, key, key);
    }
    assert_eq!(rt.tables[which].len(), 30);
    insert(&mut rt, which, 5, 99);
    assert_eq!(rt.tables[which].len(), 30, "a key put in twice is one key");
}

// Inserting into a handle nobody gave out does nothing, rather than reaching
// into whatever is at that index.
#[test]
fn a_handle_that_names_nothing_does_nothing() {
    let mut rt = Runtime::new();
    insert(&mut rt, 40, 1, 2);
    assert!(rt.tables.is_empty());
}
