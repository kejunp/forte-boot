// What a `%test` fails by.
//
// `std/test.ft` is the Forte half of this and the runner in `src/link.rs` is
// the third piece: the runner clears the count before each test and reads it
// afterwards, and what sits between them is whatever the test asserted.
//
// **A failed assertion does not stop the test.** It records itself, says what
// went wrong, and returns, so the rest of the body runs. That is not the
// behaviour anybody wants and it is the only one available: stopping early
// means unwinding, and nothing in the language unwinds -- there is no panic,
// no exception and no early return the callee can force on its caller. The
// alternatives were both worse. Taking the process down on the first failed
// assertion would report one test and abandon every test after it, which is
// the one thing a runner exists to avoid; and `longjmp`ing back to the runner
// would be jumping out of Rust frames, over Forte frames whose drops are
// written and would not run.
//
// So a test goes on after it has already failed, and what follows a failed
// assertion is running on values the test has just said are wrong. A test that
// checks a length and then reads that many elements will fail the first
// assertion and then run off the end of something. That is worth knowing about
// and is why the count is a count rather than a flag: every assertion that
// failed is reported, and reading the first one is usually reading the cause of
// all of them.

use std::sync::atomic::{AtomicI64, Ordering};

use super::fmt::{shown, same, Arg, Str};

// How many assertions have failed in the test now running.
//
// One count for the process and not one per thread: the runner calls the tests
// one after another on the thread it started on, and a test that puts an
// assertion on a thread of its own is a test whose failure should be counted
// wherever it happened.
static FAILED: AtomicI64 = AtomicI64::new(0);

// ---- What the runner calls -------------------------------------------------

// `__rt_test_start()`: a new test is about to run, so nothing has failed yet.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_test_start() {
    FAILED.store(0, Ordering::SeqCst);
}

// `__rt_test_failed()`: how many assertions the test that just returned failed.
// Nought is a test that passed.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_test_failed() -> i64 {
    FAILED.load(Ordering::SeqCst)
}

// ---- What a test calls -----------------------------------------------------

// `__rt_assert(ok, why)`: the plain one, where the test worked the question out
// itself and all this has to carry is the answer.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_assert(ok: i64, why: *const Str) {
    if ok != 0 {
        return;
    }
    failed(why, &[]);
}

// `__rt_assert_cmp(same, a, b, why)`: the two-sided one, which is worth a
// symbol of its own because it can say what the two sides were. `assert(x == y)`
// can only ever report that they differed.
//
// `same` is which way round the question was asked: whether they are equal, or
// whether they are not.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_assert_cmp(
    want_same: i64,
    a: *const Arg,
    b: *const Arg,
    why: *const Str,
) {
    let (Some(a), Some(b)) = (unsafe { a.as_ref() }, unsafe { b.as_ref() }) else {
        failed(why, &["one side of the comparison is not there".to_string()]);
        return;
    };
    if same(a, b) == (want_same != 0) {
        return;
    }
    // Both sides where they were meant to differ and did not, since printing
    // one of two equal things twice tells the reader nothing.
    let said = match want_same != 0 {
        true => vec![format!(" left: {}", shown(a)), format!("right: {}", shown(b))],
        false => vec![format!(" both: {}", shown(a))],
    };
    failed(why, &said);
}

// One failure: counted, and said where the reader will see it.
//
// The error stream, which is where every other word this runtime says about a
// program goes -- and which is not buffered, so what it says lands between the
// name the runner flushed before the test and the verdict it prints after.
fn failed(why: *const Str, said: &[String]) {
    FAILED.fetch_add(1, Ordering::SeqCst);
    let why = (unsafe { why.as_ref() }).and_then(Str::read).unwrap_or("");
    match why.is_empty() {
        true => eprintln!("\n    assertion failed"),
        false => eprintln!("\n    assertion failed: {}", why),
    }
    for line in said {
        eprintln!("    {}", line);
    }
}

#[cfg(test)]
mod tests;
