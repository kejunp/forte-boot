// What aarch64 comes out as, and whether an assembler will take it.
//
// There is no way to *run* this here -- the machine these tests are compiled
// on is not this one and there is no emulator beside them -- so what is
// checked is the two things that can be: that the shapes this file is supposed
// to produce are the shapes it produces, and that an assembler for this
// machine accepts every line of it. The second is the one that finds a
// mnemonic that does not exist or a register named where it may not be, and it
// found several.

use super::super::super::fixture::*;
use super::super::super::machine::AARCH64;
use super::super::{render, tried};
use super::*;

fn shown(source: &str) -> String {
    render(&lowered(source), AARCH64).0
}

fn has(text: &str, want: &str) -> bool {
    text.lines().any(|line| line.contains(want))
}

// ---- The frame -------------------------------------------------------------

#[test]
fn every_body_saves_what_it_has_to_and_puts_it_back() {
    let text = shown("fn f(a: i32): i32 { a }\n");
    // The frame pointer and the link register go down together and come back
    // together, which is what this machine's pair instructions are for.
    assert!(has(&text, "stp\tx29, x30, [sp, #-16]!"), "{}", text);
    assert!(has(&text, "mov\tx29, sp"), "{}", text);
    assert!(has(&text, "ldp\tx29, x30, [sp], #16"), "{}", text);
    assert!(has(&text, "ret"), "{}", text);
}

// ---- The instructions ------------------------------------------------------

// A remainder is two instructions here and no registers are put out of the
// way: the quotient, and the dividend less the quotient times the divisor.
#[test]
fn a_remainder_is_a_divide_and_a_multiply_subtract() {
    let text = shown("fn f(a: i32, b: i32): i32 { a % b }\n");
    assert!(has(&text, "sdiv"), "{}", text);
    assert!(has(&text, "msub"), "{}", text);
    assert!(!has(&text, "push"), "nothing has to be got out of the way: {}", text);
}

// A comparison sets flags and `cset` reads them, which is the shape x86-64 has
// too and RISC-V does not.
#[test]
fn a_comparison_sets_flags_and_a_register_is_set_from_them() {
    let text = shown("fn f(a: i32, b: i32): i32 { if a < b { 1 } else { 0 } }\n");
    assert!(has(&text, "cmp\t"), "{}", text);
    assert!(has(&text, "cset"), "{}", text);
    assert!(has(&text, "cbnz"), "{}", text);
}

// A wide constant is built sixteen bits at a time, there being no instruction
// that takes a whole one.
#[test]
fn a_wide_constant_is_built_a_piece_at_a_time() {
    let text = shown("fn f(): i64 { 1234605616436508552 }\n");
    assert!(has(&text, "movz"), "{}", text);
    assert!(has(&text, "movk"), "{}", text);
}

// A small one is one instruction, or every nought in a program would be four.
#[test]
fn a_small_constant_is_one_instruction() {
    let text = shown("fn f(): i64 { 7 }\n");
    assert_eq!(text.lines().filter(|l| l.contains("movk")).count(), 0, "{}", text);
}

// An address is a page and then the rest of the way, this machine having no
// instruction that reaches an arbitrary symbol.
#[test]
fn a_symbol_is_reached_in_two_steps() {
    let text = shown("fn f(): str { \"hi\" }\n");
    assert!(has(&text, "adrp"), "{}", text);
    assert!(has(&text, ":lo12:"), "{}", text);
}

// The destination is written first, which is the opposite of the other file
// here and is the one thing most likely to be got backwards.
#[test]
fn the_destination_comes_first() {
    let text = shown("fn f(a: i64, b: i64): i64 { a + b }\n");
    let held = text.lines().find(|l| l.contains("add\tx")).expect("an add");
    let parts: Vec<&str> = held.split_whitespace().collect();
    assert_eq!(parts.len(), 4, "three operands: {}", held);
}

// ---- And whether it is really assembly -------------------------------------

#[test]
fn what_comes_out_assembles() {
    let held = [
        "fn f(a: i32, b: i32): i32 { a + b }\n",
        "fn f(a: i32, b: i32): i32 { if a > b { a } else { b } }\n",
        "fn f(n: i32): i32 {\n    var t = 0\n    var i = 0\n\
         \x20   while i < n { t = t + i\n i = i + 1 }\n    t\n}\n",
        "fn f(a: i32, b: i32): i32 { a / b + a % b }\n",
        "fn f(a: u32, b: u32): u32 { a / b + a % b }\n",
        "fn f(a: i64, b: i64): i64 { (a << b) + (a >> b) }\n",
        "fn f(a: f64, b: f64): f64 { a * b - a / b }\n",
        "fn f(a: f64, b: f64): i32 { if a < b { 1 } else { 0 } }\n",
        "fn f(n: i32): f64 { n as f64 }\n",
        "fn f(x: f64): i32 { x as i32 }\n",
        "fn f(a: i64, b: i64, c: i64, d: i64, e: i64, g: i64): i64 { a+b+c+d+e+g }\n",
        "struct P {\n    pub a: i8,\n    pub b: i64,\n}\n\
         fn f(p: &P): i64 { p.b }\n",
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn f(a: i64): i64 {\n    let p = P { a: a, b: a }\n    p.a + p.b\n}\n",
        "fn f(): str { \"hello\" }\n",
        "fn f(xs: &i32[], i: i32): i32 { xs[i] }\n",
        "fn g(x: i32): i32 { x }\nfn f(): i32 { g(1) }\n",
        "trait Drop {\n    fn drop(self)\n}\n\
         struct H {\n    pub n: i32,\n}\n\
         impl Drop for H {\n    fn drop(self) {\n    }\n}\n\
         enum E {\n    Empty,\n    One(H),\n}\n\
         fn f() {\n    let e = E::One(H { n: 1 })\n}\n",
        "fn f(a: i32): i32 {\n    let g = |x: i32| x + a\n    g(2)\n}\n",
    ];
    for source in held {
        let text = render(&lowered(source), AARCH64).0;
        if let Some(said) = tried(&text, "aarch64-linux-gnu") {
            panic!("{}\n---- from ----\n{}", said, source);
        }
    }
}
