// That the way out is reachable and says what it was given.
//
// The one thing this file cannot do is call it: `__rt_panic` ends the process,
// and a test that ended the process would take the other 274 with it. What is
// left to check is the part that has an answer -- the message it would print --
// and that the symbol is the shape a Forte declaration of it expects.

use super::*;

#[test]
fn the_symbol_takes_a_string_and_never_comes_back() {
    // A borrow, so the signature is checked without the call being made.
    let held: extern "C" fn(*const Str) -> ! = __rt_panic;
    let _ = held;
}

// The words it would write. Spelled here rather than asserted through the
// process, for the reason the header gives.
#[test]
fn a_message_that_is_not_there_still_reads_as_a_sentence() {
    let empty = Str { at: std::ptr::null(), len: 0 };
    assert_eq!(empty.read(), Some(""));
}

#[test]
fn a_message_reads_back_as_what_was_handed_over() {
    let held = "cannot go on";
    let one = Str { at: held.as_ptr(), len: held.len() as i64 };
    assert_eq!(one.read(), Some("cannot go on"));
}
