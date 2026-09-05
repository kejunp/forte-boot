// That a failed assertion is counted and a passing one is not, which is the
// whole of what the runner reads.
//
// The count is one static for the process, so these take a lock rather than
// running beside one another: two tests each clearing it and reading it back
// would be two tests asserting about each other's assertions. The lock is this
// file's own -- nothing else touches the count -- and it is taken for the whole
// of each test rather than around each call.

use std::sync::{Mutex, MutexGuard};

use super::*;

static ALONE: Mutex<()> = Mutex::new(());

// The lock, and a count that has been cleared: every test here begins the way
// the runner begins one.
fn alone() -> MutexGuard<'static, ()> {
    // A test that failed while holding the lock poisons it, and what the next
    // test wants is the lock rather than the news.
    let held = ALONE.lock().unwrap_or_else(|held| held.into_inner());
    __rt_test_start();
    held
}

// A `str` the way a Forte caller hands one over.
fn text(s: &str) -> Str {
    Str { at: s.as_ptr(), len: s.len() as i64 }
}

fn empty() -> Str {
    Str { at: std::ptr::null(), len: 0 }
}

fn int(n: i64) -> Arg {
    Arg { tag: 1, word: n, real: 0.0, held: empty() }
}

fn word(s: &str) -> Arg {
    Arg { tag: 5, word: 0, real: 0.0, held: text(s) }
}

#[test]
fn a_test_that_asserts_nothing_has_failed_nothing() {
    let _held = alone();
    assert_eq!(__rt_test_failed(), 0);
}

#[test]
fn an_assertion_that_holds_is_not_counted() {
    let _held = alone();
    let why = text("this holds");
    __rt_assert(1, &why);
    __rt_assert(1, &why);
    assert_eq!(__rt_test_failed(), 0);
}

// Every one that fails is counted and not just the first. A test goes on after
// it has failed -- nothing in the language unwinds -- so the count is what says
// how much of what followed was running on values already known to be wrong.
#[test]
fn every_assertion_that_fails_is_counted() {
    let _held = alone();
    let why = text("this does not hold");
    __rt_assert(0, &why);
    assert_eq!(__rt_test_failed(), 1);
    __rt_assert(0, &why);
    __rt_assert(1, &why);
    assert_eq!(__rt_test_failed(), 2);
}

// The runner clears the count before each test, so what one test failed is not
// still failing for the next.
#[test]
fn starting_a_test_forgets_what_the_last_one_failed() {
    let _held = alone();
    let why = text("no");
    __rt_assert(0, &why);
    assert_eq!(__rt_test_failed(), 1);
    __rt_test_start();
    assert_eq!(__rt_test_failed(), 0);
}

// ---- The two-sided one -------------------------------------------------------

#[test]
fn two_equal_things_are_equal_and_two_others_are_not() {
    let _held = alone();
    let why = text("equal");
    let (one, also_one, two) = (int(1), int(1), int(2));

    __rt_assert_cmp(1, &one, &also_one, &why);
    assert_eq!(__rt_test_failed(), 0, "1 == 1 was meant to hold");

    __rt_assert_cmp(1, &one, &two, &why);
    assert_eq!(__rt_test_failed(), 1, "1 == 2 was meant to fail");
}

#[test]
fn the_question_asked_the_other_way_round_fails_the_other_way_round() {
    let _held = alone();
    let why = text("different");
    let (one, also_one, two) = (int(1), int(1), int(2));

    __rt_assert_cmp(0, &one, &two, &why);
    assert_eq!(__rt_test_failed(), 0, "1 != 2 was meant to hold");

    __rt_assert_cmp(0, &one, &also_one, &why);
    assert_eq!(__rt_test_failed(), 1, "1 != 1 was meant to fail");
}

// A string compares as a string and not as the two words that carry it: the
// same text at two addresses is the same value.
#[test]
fn two_strings_compare_by_what_they_say() {
    let _held = alone();
    let why = text("same words");
    // Two addresses and one text, so that what is compared is what they say.
    let held = String::from("hello");
    let (a, b) = (word("hello"), word(&held));
    __rt_assert_cmp(1, &a, &b, &why);
    assert_eq!(__rt_test_failed(), 0);

    let c = word("goodbye");
    __rt_assert_cmp(1, &a, &c, &why);
    assert_eq!(__rt_test_failed(), 1);
}

// Two arguments of different kinds are never equal, whatever bits they carry:
// `int(1)` and `truth(true)` were written by somebody who meant two things.
#[test]
fn two_kinds_of_thing_are_never_the_same_thing() {
    let _held = alone();
    let why = text("a number is not a bool");
    let truth = Arg { tag: 4, word: 1, real: 0.0, held: empty() };
    __rt_assert_cmp(1, &int(1), &truth, &why);
    assert_eq!(__rt_test_failed(), 1);
}

// A side that is not there is a caller disagreeing with this file about how
// many it has, and is a failure rather than a read through nothing.
#[test]
fn a_side_that_is_not_there_fails_rather_than_being_followed() {
    let _held = alone();
    let why = text("nowhere");
    __rt_assert_cmp(1, std::ptr::null(), &int(1), &why);
    assert_eq!(__rt_test_failed(), 1);
}
