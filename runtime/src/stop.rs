// The way out of the middle of a program.
//
// `docs/prose.txt` §8 names this as the gap and says why nothing else fills
// it: "a fn deep in a program that has found it cannot go on returns `never`
// and has nothing to call -- nothing, that is, but a `%symbol` declaration of
// somebody else's `exit`, which is the same answer the language gives for
// every other thing it has not got round to and is not an answer for this
// one." So it is here rather than borrowed, and it says something before it
// goes.
//
// **It ends the process rather than unwinding.** Nothing in Forte unwinds --
// there is no exception, no `catch`, and no way for a callee to return on its
// caller's behalf -- so the two honest ends are stopping the process and
// carrying on wrongly. A `never` that carried on would be a lie about the one
// thing the type says.
//
// The status is 101, which is Rust's for the same thing. Any number would do;
// what matters is that it is not nought, so that whatever ran the program
// finds out without reading the words, and that it is one number rather than
// whatever the last expression left in a register.

use std::io::Write as _;

use super::fmt::Str;

// `__rt_panic(msg)`: say why, and stop.
//
// Never comes back, and its Forte declaration says `never`, so the compiler
// already knows nothing after a call to it can run.
//
// The message goes to the error stream unbuffered and is flushed before the
// exit: a program stopping is exactly the case where a line still sitting in a
// buffer is a line nobody ever sees.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_panic(msg: *const Str) -> ! {
    let why = (unsafe { msg.as_ref() }).and_then(Str::read).unwrap_or("");
    let stderr = std::io::stderr();
    let mut held = stderr.lock();
    let _ = match why.is_empty() {
        true => writeln!(held, "fortec: the program stopped"),
        false => writeln!(held, "fortec: the program stopped: {}", why),
    };
    let _ = held.flush();
    std::process::exit(101)
}

#[cfg(test)]
mod tests;
