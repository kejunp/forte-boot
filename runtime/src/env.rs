// What the process was started with: its arguments, and its environment.
//
// §8: "There is no spelling for the arguments a process was started with and
// none for its environment, so the only program that can be written is one
// that computes what it was going to compute anyway." This is the way in, and
// `stop` is the way out.
//
// It is here and not in the language for the reason `fmt` and `mem` are here.
// A `main` that took its arguments would answer half of it -- an environment
// is a lookup and not a list -- and it would make `main` two functions where
// §1 says a program has one beginning, "taking nothing". So both halves are
// read the way everything else outside the language is read: a `%symbol` fn
// per question, and `std/env.ft` is the other half of this file.
//
// **Where the arguments come from.** Not from `std::env::args`, which is
// Rust's own copy and would answer for the Rust runtime rather than for the
// program: the shim `link.rs` writes takes them from the kernel and hands them
// over before anything else runs. That also makes them the bytes the process
// was actually started with, and not what Rust made of them -- an argument is
// bytes, and `str` in this language is bytes too.
//
// **Why they are held rather than copied.** `argv` is the kernel's and lives
// as long as the process, so a `str` naming a piece of it is good for as long
// as anything can ask. Nothing here allocates and nothing here is collected.

use std::sync::atomic::{AtomicI64, AtomicPtr, Ordering};

use super::fmt::Str;

// What the shim handed over. Two atomics rather than a lock: they are written
// once, before the program's first line, and only read afterwards.
static COUNT: AtomicI64 = AtomicI64::new(0);
static ARGV: AtomicPtr<*const u8> = AtomicPtr::new(std::ptr::null_mut());

// `__rt_args(argc, argv)`: called once by the shim, before `__rt_init`.
//
// A program whose shim never calls it -- the test runner's does not -- reads
// no arguments rather than reading rubbish, which is what the nought above is
// for.
///
/// # Safety
/// `argv` is the kernel's array of `argc` NUL-terminated strings, and it must
/// live as long as the process does. That is what a C `main` is handed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_args(argc: i64, argv: *const *const u8) {
    COUNT.store(argc.max(0), Ordering::Relaxed);
    ARGV.store(argv as *mut *const u8, Ordering::Relaxed);
}

// `__rt_arg_count() -> i64`: how many there are, the program's own name among
// them, as a C `main` counts them.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_arg_count() -> i64 {
    COUNT.load(Ordering::Relaxed)
}

// `__rt_arg(out, i)`: the i'th of them, or nothing where there is no i'th.
//
// Written through `out` and not given back: a `str` is two words and this
// compiler hands every aggregate over as an address (`fmt::Str`), so what a
// Forte `fn arg(i: i64): str` calls is a routine taking the room first.
///
/// # Safety
/// `out` is room for one `Str`, which the caller made.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_arg(out: *mut Str, i: i64) {
    if out.is_null() {
        return;
    }
    let held = unsafe { held_at(i) };
    unsafe { out.write(held) };
}

// `__rt_var(out, name)`: what the environment holds under that name, or
// nothing where it holds none.
//
// The empty string for a name that is not there *and* for one set to nothing,
// which `has` below is what tells apart. Two questions and two routines: an
// `Option<str>` is a Forte enum and not a shape a `%symbol` fn can give back.
///
/// # Safety
/// `out` is room for one `Str` and `name` is one `Str`, both the caller's.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_var(out: *mut Str, name: *const Str) {
    if out.is_null() {
        return;
    }
    let held = unsafe { looked_up(name) };
    let held = match held {
        // The bytes the environment holds, which live as long as the process:
        // `std::env::var_os` copies, so what is kept is leaked on purpose --
        // once per name, and a name is asked for a bounded number of times.
        Some(text) => {
            let held: &'static [u8] = Box::leak(text.into_boxed_slice());
            Str { at: held.as_ptr(), len: held.len() as i64 }
        }
        None => Str { at: std::ptr::null(), len: 0 },
    };
    unsafe { out.write(held) };
}

// `__rt_has_var(name) -> bool`: whether the environment holds one at all,
// which is the question the empty string cannot answer.
///
/// # Safety
/// `name` is one `Str`, the caller's.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_has_var(name: *const Str) -> bool {
    unsafe { looked_up(name).is_some() }
}

// ---- Reading what was handed over ------------------------------------------

// The i'th argument as a `str`, measured where it stands. Nothing is copied:
// `argv` is the kernel's and outlives everything that could ask.
unsafe fn held_at(i: i64) -> Str {
    let none = Str { at: std::ptr::null(), len: 0 };
    if i < 0 || i >= COUNT.load(Ordering::Relaxed) {
        return none;
    }
    let argv = ARGV.load(Ordering::Relaxed) as *const *const u8;
    if argv.is_null() {
        return none;
    }
    let at = unsafe { *argv.offset(i as isize) };
    if at.is_null() {
        return none;
    }
    // To the NUL and not past it. A length and not a terminator is what a
    // `str` is here, so the one thing this has to do is count.
    let mut len = 0i64;
    while unsafe { *at.offset(len as isize) } != 0 {
        len += 1;
    }
    Str { at, len }
}

// The bytes the environment holds under that name. `None` where it holds
// none, which is not the same as holding nothing.
unsafe fn looked_up(name: *const Str) -> Option<Vec<u8>> {
    if name.is_null() {
        return None;
    }
    let held = unsafe { &*name };
    if held.at.is_null() || held.len < 0 {
        return None;
    }
    let bytes = unsafe { std::slice::from_raw_parts(held.at, held.len as usize) };
    // A name with a NUL or an `=` in it is one no environment can hold, and
    // `var_os` would answer `None` for it anyway -- said here so that it is
    // said rather than depended on.
    let text = std::str::from_utf8(bytes).ok()?;
    std::env::var_os(text).map(|held| held.into_encoded_bytes())
}

#[cfg(test)]
mod tests;
