// That the keys come out in order and that a key put in twice is one key.
//
// The order is not a nicety here -- §8 makes it what tells `Map` from
// `HashMap`, so a `for` over one has to yield its keys in order and that is
// what most of these check. The rest are about the binary search, which is the
// one piece with an off-by-one in it.

use super::super::super::shape::{Kind, Made};
use super::*;

fn number() -> Made {
    Made::new(8, 8, Kind::Signed)
}

fn built(held: &[i64]) -> (Ordered, Made) {
    let shape = number();
    let mut out = Ordered::new();
    for (at, key) in held.iter().enumerate() {
        out.put(*key as usize, at, shape.shape());
    }
    (out, shape)
}

fn keys_of(held: &Ordered) -> Vec<i64> {
    let mut out = Vec::new();
    let mut at = held.step(-1);
    while held.valid(at) {
        out.push(held.key_at(at).expect("a key") as i64);
        at = held.step(at);
    }
    out
}

// ---- Order -----------------------------------------------------------------

#[test]
fn the_keys_come_out_lowest_first_whatever_order_they_went_in() {
    let (held, _) = built(&[5, 1, 9, 3, 7]);
    assert_eq!(keys_of(&held), vec![1, 3, 5, 7, 9]);
}

#[test]
fn negative_keys_are_in_order_too() {
    let (held, _) = built(&[3, -7, 0, -1, 12]);
    assert_eq!(keys_of(&held), vec![-7, -1, 0, 3, 12]);
}

#[test]
fn an_empty_map_yields_nothing() {
    let held = Ordered::new();
    assert!(held.is_empty());
    assert!(!held.valid(held.step(-1)));
    assert_eq!(keys_of(&held), Vec::<i64>::new());
}

// The contract the lowering fixed when it made `IterStart` a constant: the
// first thing every loop does is step from -1.
#[test]
fn stepping_from_minus_one_lands_on_the_first() {
    let (held, _) = built(&[4, 2]);
    assert_eq!(held.step(-1), 0);
    assert!(held.valid(0));
    assert_eq!(held.key_at(0), Some(2));
}

#[test]
fn stepping_past_the_last_is_not_valid() {
    let (held, _) = built(&[1, 2, 3]);
    let mut at = held.step(-1);
    for _ in 0..3 {
        at = held.step(at);
    }
    assert!(!held.valid(at));
    assert_eq!(held.at(at), None);
}

// ---- Finding ---------------------------------------------------------------

#[test]
fn every_key_that_went_in_can_be_found() {
    let some: Vec<i64> = (0..200).map(|n| (n * 37) % 211).collect();
    let (held, shape) = built(&some);
    for key in &some {
        assert!(held.has(*key as usize, shape.shape()), "key {}", key);
    }
}

#[test]
fn a_key_that_never_went_in_is_not_found() {
    let (held, shape) = built(&[1, 3, 5]);
    for key in [0i64, 2, 4, 6, -1, 1000] {
        assert!(!held.has(key as usize, shape.shape()), "key {}", key);
    }
}

#[test]
fn the_value_that_comes_back_is_the_one_that_went_in() {
    let shape = number();
    let mut held = Ordered::new();
    for n in 0..50usize {
        held.put(n, n * 3, shape.shape());
    }
    for n in 0..50usize {
        assert_eq!(held.get(n, shape.shape()), Some(n * 3));
    }
}

// ---- A key twice -----------------------------------------------------------

#[test]
fn putting_a_key_in_again_writes_over_its_value() {
    let shape = number();
    let mut held = Ordered::new();
    held.put(7, 1, shape.shape());
    held.put(7, 2, shape.shape());
    assert_eq!(held.len(), 1, "one key, not two");
    assert_eq!(held.get(7, shape.shape()), Some(2));
}

#[test]
fn a_map_built_from_a_literal_with_a_repeat_holds_the_last() {
    let shape = number();
    let mut held = Ordered::new();
    for (key, value) in [(1usize, 10usize), (2, 20), (1, 30)] {
        held.put(key, value, shape.shape());
    }
    assert_eq!(held.len(), 2);
    assert_eq!(held.get(1, shape.shape()), Some(30));
}

// ---- Bigger ----------------------------------------------------------------

#[test]
fn a_thousand_keys_are_still_in_order_and_all_there() {
    let some: Vec<i64> = (0..1000).map(|n: i64| (n * 7919) % 10007).collect();
    let (held, shape) = built(&some);
    let out = keys_of(&held);
    assert_eq!(out.len(), some.len(), "no key was lost or doubled");
    for pair in out.windows(2) {
        assert!(pair[0] < pair[1], "{} came before {}", pair[0], pair[1]);
    }
    for key in &some {
        assert!(held.has(*key as usize, shape.shape()));
    }
}
