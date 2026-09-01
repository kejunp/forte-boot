// That everything put in can be found again, across a growth.
//
// Growing is where a hash table loses things, and it loses them silently: a
// key that was rehashed into the wrong bucket is simply never found again, and
// the table is otherwise perfectly consistent. So the tests here put in enough
// to force several growths and then look for every one of them.

use super::super::super::shape::{Kind, Made};
use super::*;

fn number() -> Made {
    Made::new(8, 8, Kind::Unsigned)
}

fn built(n: usize) -> (Hashed, Made) {
    let shape = number();
    let mut out = Hashed::new();
    for key in 0..n {
        out.put(key * 31, key, shape.shape());
    }
    (out, shape)
}

fn walked(held: &Hashed) -> Vec<usize> {
    let mut out = Vec::new();
    let mut at = held.step(-1);
    while held.valid(at) {
        out.push(held.key_at(at).expect("a key"));
        at = held.step(at);
    }
    out
}

// ---- Finding ---------------------------------------------------------------

#[test]
fn what_went_in_comes_out() {
    let (held, shape) = built(100);
    for key in 0..100usize {
        assert_eq!(held.get(key * 31, shape.shape()), Some(key), "key {}", key * 31);
    }
}

#[test]
fn a_key_that_never_went_in_is_not_found() {
    let (held, shape) = built(50);
    assert!(!held.has(7, shape.shape()));
    assert!(!held.has(usize::MAX, shape.shape()));
}

// The one that catches a rehash that lost something.
#[test]
fn everything_survives_a_table_growing_many_times() {
    let (held, shape) = built(5000);
    assert_eq!(held.len(), 5000);
    for key in 0..5000usize {
        assert!(held.has(key * 31, shape.shape()), "key {} was lost", key * 31);
    }
}

#[test]
fn a_table_grows_rather_than_chaining_for_ever() {
    let (held, _) = built(5000);
    assert!(held.main > 1, "it never grew");
    assert!(held.buckets.len() < 5000, "it is chaining rather than growing");
}

#[test]
fn putting_a_key_in_again_writes_over_its_value() {
    let shape = number();
    let mut held = Hashed::new();
    held.put(7, 1, shape.shape());
    held.put(7, 2, shape.shape());
    assert_eq!(held.len(), 1);
    assert_eq!(held.get(7, shape.shape()), Some(2));
}

// ---- Walking ---------------------------------------------------------------

#[test]
fn walking_yields_every_key_exactly_once() {
    let (held, _) = built(500);
    let mut out = walked(&held);
    assert_eq!(out.len(), 500);
    out.sort_unstable();
    out.dedup();
    assert_eq!(out.len(), 500, "something came out twice");
}

#[test]
fn an_empty_table_yields_nothing() {
    let held = Hashed::new();
    assert!(held.is_empty());
    assert!(!held.valid(held.step(-1)));
    assert!(walked(&held).is_empty());
}

// The empty slots between entries are skipped by stepping rather than
// reported by `valid`, so a mostly empty table takes one turn per entry.
#[test]
fn stepping_lands_only_on_slots_that_hold_something() {
    let shape = number();
    let mut held = Hashed::new();
    held.put(5, 1, shape.shape());
    let first = held.step(-1);
    assert!(held.valid(first));
    assert_eq!(held.key_at(first), Some(5));
    assert!(!held.valid(held.step(first)));
}

#[test]
fn a_position_that_holds_nothing_yields_nothing() {
    let (held, _) = built(3);
    assert_eq!(held.at(-1), None);
    assert_eq!(held.at(1 << 30), None);
}

// ---- The byte beside each slot ---------------------------------------------

// Nought means empty, so a real hash whose top byte is nought is nudged off
// it -- otherwise a key would land in a slot that reads as free.
#[test]
fn a_hash_whose_top_byte_is_nought_is_nudged_off_it() {
    assert_ne!(top(0), EMPTY);
    assert_ne!(top(0x00ff_ffff_ffff_ffff), EMPTY);
    assert_eq!(top(0xab00_0000_0000_0000), 0xab);
}

// Keys that all collide still all fit, through the overflow chain.
#[test]
fn keys_that_all_land_in_one_bucket_all_fit() {
    let shape = number();
    let mut held = Hashed::new();
    // Twenty into a table of one bucket: sixteen more than a bucket holds.
    for key in 0..20usize {
        held.put(key, key, shape.shape());
    }
    assert_eq!(held.len(), 20);
    for key in 0..20usize {
        assert_eq!(held.get(key, shape.shape()), Some(key), "key {}", key);
    }
}

// ---- Other kinds of key ----------------------------------------------------

#[test]
fn a_string_key_finds_its_value() {
    let shape = Made::new(16, 8, Kind::Str).indirect();
    let mut held = Hashed::new();
    let words = [b"one".as_slice(), b"two".as_slice(), b"three".as_slice()];
    let pairs: Vec<[usize; 2]> =
        words.iter().map(|held| [held.as_ptr() as usize, held.len()]).collect();
    for (at, pair) in pairs.iter().enumerate() {
        held.put(pair.as_ptr() as usize, at, shape.shape());
    }
    for (at, pair) in pairs.iter().enumerate() {
        assert_eq!(held.get(pair.as_ptr() as usize, shape.shape()), Some(at));
    }
    // The same characters written somewhere else is the same key.
    let again = b"two".to_vec();
    let other: [usize; 2] = [again.as_ptr() as usize, 3];
    assert_eq!(held.get(other.as_ptr() as usize, shape.shape()), Some(1));
}
