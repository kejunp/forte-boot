// That a set holds each thing once and yields the thing rather than a pair.
//
// Almost everything about a set is the map underneath it and is tested there.
// What is here is the two things that are a set's own: putting the same
// element in twice leaves one, and walking one yields the element as the
// register held it rather than the address of a pair.

use super::super::shape::{Kind, Made};
use super::super::Runtime;
use super::*;

fn number() -> Made {
    Made::new(8, 8, Kind::Signed)
}

fn set(rt: &mut Runtime, hashed: bool, elem: &Made) -> usize {
    let held = Held::new(rt, hashed, elem.shape());
    rt.sets.push(held);
    rt.sets.len() - 1
}

fn walked(held: &Held) -> Vec<usize> {
    let mut out = Vec::new();
    let mut at = held.step(-1);
    while held.valid(at) {
        out.push(held.elem(at));
        at = held.step(at);
    }
    out
}

// ---- One of each -----------------------------------------------------------

#[test]
fn putting_the_same_element_in_twice_leaves_one() {
    let mut rt = Runtime::new();
    let shape = number();
    let which = set(&mut rt, false, &shape);
    for held in [3usize, 1, 3, 1, 3] {
        Held::put(&mut rt, which, held);
    }
    assert_eq!(rt.sets[which].len(), 2);
    assert_eq!(walked(&rt.sets[which]), vec![1, 3]);
}

#[test]
fn an_element_that_went_in_is_there() {
    let mut rt = Runtime::new();
    let shape = number();
    let which = set(&mut rt, true, &shape);
    for held in 0..40usize {
        Held::put(&mut rt, which, held * 3);
    }
    for held in 0..40usize {
        assert!(rt.sets[which].has(held * 3), "{}", held * 3);
    }
    assert!(!rt.sets[which].has(1));
}

// ---- What walking one yields -----------------------------------------------

// A set's turn is the element, not a pair. A direct element reaches the
// program as the value itself.
#[test]
fn walking_a_set_yields_the_element_itself() {
    let mut rt = Runtime::new();
    let shape = number();
    let which = set(&mut rt, false, &shape);
    Held::put(&mut rt, which, 42);
    assert_eq!(walked(&rt.sets[which]), vec![42]);
}

// And an indirect one reaches it as the address of the runtime's own copy,
// which is what the register would have held for any other aggregate.
#[test]
fn an_indirect_element_is_yielded_by_its_address() {
    let mut rt = Runtime::new();
    let shape = Made::new(16, 8, Kind::Opaque).indirect();
    let which = set(&mut rt, false, &shape);
    let held: [u8; 16] = [8; 16];
    Held::put(&mut rt, which, held.as_ptr() as usize);

    let out = walked(&rt.sets[which]);
    assert_eq!(out.len(), 1);
    assert_ne!(out[0], held.as_ptr() as usize, "it is the copy, not the caller's");
    assert_eq!(unsafe { *(out[0] as *const u8) }, 8);
}

#[test]
fn an_ordered_set_yields_its_elements_in_order() {
    let mut rt = Runtime::new();
    let shape = number();
    let which = set(&mut rt, false, &shape);
    for held in [9usize, 2, 7, 4] {
        Held::put(&mut rt, which, held);
    }
    assert_eq!(walked(&rt.sets[which]), vec![2, 4, 7, 9]);
}

#[test]
fn an_empty_set_yields_nothing() {
    let mut rt = Runtime::new();
    let shape = number();
    let which = set(&mut rt, true, &shape);
    assert!(rt.sets[which].is_empty());
    assert!(walked(&rt.sets[which]).is_empty());
}

#[test]
fn a_hashed_set_and_an_ordered_one_are_two_different_things() {
    let mut rt = Runtime::new();
    let shape = number();
    let ordered = set(&mut rt, false, &shape);
    let hashed = set(&mut rt, true, &shape);
    assert!(!rt.sets[ordered].hashed());
    assert!(rt.sets[hashed].hashed());
}

#[test]
fn a_handle_that_names_nothing_does_nothing() {
    let mut rt = Runtime::new();
    Held::put(&mut rt, 12, 1);
    assert!(rt.sets.is_empty());
}
