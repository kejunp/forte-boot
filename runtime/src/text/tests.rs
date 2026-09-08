// Two strings compare by what they say.

use super::*;

fn pair(held: &str) -> [usize; 2] {
    [held.as_ptr() as usize, held.len()]
}

#[test]
fn two_strings_of_the_same_characters_are_equal() {
    // The second is built rather than written, so that the two are the same
    // characters in two places -- a pooled literal would compare equal by its
    // address and prove nothing.
    let held = String::from("hell") + "o";
    let (a, b) = (pair("hello"), pair(&held));
    assert_ne!(a[0], b[0], "two places, or this proves nothing");
    assert_eq!(__rt_str_cmp(a.as_ptr() as usize, b.as_ptr() as usize), 0);
}

#[test]
fn a_shorter_string_sorts_before_the_one_it_starts() {
    let (a, b) = (pair("hell"), pair("hello"));
    assert_eq!(__rt_str_cmp(a.as_ptr() as usize, b.as_ptr() as usize), -1);
    assert_eq!(__rt_str_cmp(b.as_ptr() as usize, a.as_ptr() as usize), 1);
}

#[test]
fn the_order_is_by_byte_and_not_by_length() {
    let (a, b) = (pair("b"), pair("aa"));
    assert_eq!(__rt_str_cmp(a.as_ptr() as usize, b.as_ptr() as usize), 1);
}

#[test]
fn an_empty_string_is_every_strings_prefix() {
    let (a, b) = (pair(""), pair("a"));
    assert_eq!(__rt_str_cmp(a.as_ptr() as usize, b.as_ptr() as usize), -1);
    assert_eq!(__rt_str_cmp(a.as_ptr() as usize, a.as_ptr() as usize), 0);
}

// A `str` that was never given anything, which is a word of nought where the
// pair should be. Nothing here reads through it.
#[test]
fn nothing_at_all_is_the_empty_string() {
    let a = pair("a");
    assert_eq!(__rt_str_cmp(0, 0), 0);
    assert_eq!(__rt_str_cmp(0, a.as_ptr() as usize), -1);
}
