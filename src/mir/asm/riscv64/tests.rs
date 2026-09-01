// What riscv64 comes out as, and whether an assembler will take it.
//
// There is no way to *run* this here -- the machine these tests are compiled
// on is not this one and there is no emulator beside them -- so what is
// checked is the two things that can be: that the shapes this file is supposed
// to produce are the shapes it produces, and that an assembler for this
// machine accepts every line of it. The second is the one that finds a
// mnemonic that does not exist or a register named where it may not be, and it
// found several.

use super::super::super::fixture::*;
use super::super::super::machine::RISCV64;
use super::super::{render, tried};
use super::*;

fn shown(source: &str) -> String {
    render(&lowered(source), RISCV64).0
}

fn has(text: &str, want: &str) -> bool {
    text.lines().any(|line| line.contains(want))
}

// ---- The frame -------------------------------------------------------------

#[test]
fn every_body_saves_what_it_has_to_and_puts_it_back() {
    let text = shown("fn f(a: i32): i32 { a }\n");
    assert!(has(&text, "sd\tra, 8(sp)"), "{}", text);
    assert!(has(&text, "sd\ts0, 0(sp)"), "{}", text);
    assert!(has(&text, "ld\ts0, 0(sp)"), "{}", text);
    assert!(has(&text, "ret"), "{}", text);
}

// ---- The instructions ------------------------------------------------------

// No flags at all: a comparison writes a one or a nought into a register,
// which is what the MIR's own comparison already means, and a branch is on
// that value. Of the three machines this is the one that matches.
#[test]
fn a_comparison_is_a_value_and_the_branch_is_on_it() {
    let text = shown("fn f(a: i32, b: i32): i32 { if a < b { 1 } else { 0 } }\n");
    assert!(has(&text, "slt"), "{}", text);
    assert!(has(&text, "bnez"), "{}", text);
    assert!(!has(&text, "cmp"), "there is nothing to compare against: {}", text);
}

// Equality has no instruction, so it is a difference and a test against
// nought.
#[test]
fn equality_is_a_difference_that_is_nought() {
    let text = shown("fn f(a: i64, b: i64): i32 { if a == b { 1 } else { 0 } }\n");
    assert!(has(&text, "xor"), "{}", text);
    assert!(has(&text, "seqz"), "{}", text);
}

// A remainder has an instruction of its own here, where aarch64 needs two.
#[test]
fn a_remainder_is_one_instruction() {
    let text = shown("fn f(a: i64, b: i64): i64 { a % b }\n");
    assert!(has(&text, "rem\t"), "{}", text);
}

// The `w` forms are the only narrow arithmetic there is, and they leave the
// answer sign-extended through the register.
#[test]
fn a_four_byte_operation_uses_the_narrow_form() {
    let text = shown("fn f(a: i32, b: i32): i32 { a + b }\n");
    assert!(has(&text, "addw"), "{}", text);
    let text = shown("fn f(a: i64, b: i64): i64 { a + b }\n");
    assert!(has(&text, "add\t"), "{}", text);
    assert!(!has(&text, "addw"), "{}", text);
}

// Bitwise operations have no narrow form and want none: every bit of the
// answer depends on the bit under it and nothing else.
#[test]
fn a_bitwise_operation_has_no_narrow_form() {
    let text = shown("fn f(a: i32, b: i32): i32 { a & b }\n");
    assert!(has(&text, "and\t"), "{}", text);
    assert!(!has(&text, "andw"), "{}", text);
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
        let text = render(&lowered(source), RISCV64).0;
        if let Some(said) = tried(&text, "riscv64-linux-gnu") {
            panic!("{}\n---- from ----\n{}", said, source);
        }
    }
}
