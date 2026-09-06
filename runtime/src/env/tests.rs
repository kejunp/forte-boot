// What the process was started with, read back.

use super::*;

// Nothing handed over is no arguments, which is what the test runner's shim
// leaves behind -- and reading one of them has to answer emptily rather than
// walk a null.
#[test]
fn a_program_handed_nothing_reads_no_arguments() {
    unsafe { __rt_args(0, std::ptr::null()) };
    assert_eq!(__rt_arg_count(), 0);
    let mut held = Str { at: std::ptr::null(), len: 0 };
    unsafe { __rt_arg(&mut held, 0) };
    assert!(held.at.is_null());
    assert_eq!(held.len, 0);
}

// And what was handed over reads back as the bytes it was, measured to the NUL
// and not past it.
#[test]
fn an_argument_reads_back_as_what_the_kernel_held() {
    let one = b"fortec\0";
    let two = b"--emit\0";
    let argv: [*const u8; 2] = [one.as_ptr(), two.as_ptr()];
    unsafe { __rt_args(2, argv.as_ptr()) };
    assert_eq!(__rt_arg_count(), 2);

    let mut held = Str { at: std::ptr::null(), len: 0 };
    unsafe { __rt_arg(&mut held, 1) };
    assert_eq!(held.len, 6, "the NUL is not one of them");
    let bytes = unsafe { std::slice::from_raw_parts(held.at, held.len as usize) };
    assert_eq!(bytes, b"--emit");

    // One past the end is nothing, not the next thing in memory.
    unsafe { __rt_arg(&mut held, 2) };
    assert!(held.at.is_null());
    unsafe { __rt_arg(&mut held, -1) };
    assert!(held.at.is_null());
    unsafe { __rt_args(0, std::ptr::null()) };
}

// A name the environment holds, and one it does not. The two are told apart by
// `has` and not by the answer: a name set to nothing and a name that is not
// there both read as no bytes.
#[test]
fn the_environment_is_read_by_name() {
    unsafe { std::env::set_var("FORTEC_ENV_TEST", "held") };
    let name = b"FORTEC_ENV_TEST";
    let asked = Str { at: name.as_ptr(), len: name.len() as i64 };
    assert!(unsafe { __rt_has_var(&asked) });

    let mut held = Str { at: std::ptr::null(), len: 0 };
    unsafe { __rt_var(&mut held, &asked) };
    let bytes = unsafe { std::slice::from_raw_parts(held.at, held.len as usize) };
    assert_eq!(bytes, b"held");

    let missing = b"FORTEC_ENV_TEST_NOT_SET";
    let asked = Str { at: missing.as_ptr(), len: missing.len() as i64 };
    assert!(!unsafe { __rt_has_var(&asked) });
    unsafe { __rt_var(&mut held, &asked) };
    assert!(held.at.is_null());
    unsafe { std::env::remove_var("FORTEC_ENV_TEST") };
}
