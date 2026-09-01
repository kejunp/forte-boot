// What x86-64 comes out as, and whether an assembler will take it.
//
// Two kinds of test, and the second is the one that matters. Asserting on the
// text is asserting that this file wrote what it meant to; handing the text to
// `clang` is asserting that what it meant to write is an instruction. Only the
// second catches a register named at the wrong width, an operand in the wrong
// order, or a mnemonic that does not exist -- and every one of those was found
// that way rather than by reading.
//
// The assembling tests skip themselves where there is no assembler. That is
// worse than failing and better than the alternative: a suite that cannot run
// on a machine without a cross toolchain is a suite nobody runs.

use super::super::super::fixture::*;
use super::super::super::machine::X86_64;
use super::super::{render, tried, Body};
use super::*;

fn shown(source: &str) -> String {
    render(&lowered(source), X86_64).0
}

fn has(text: &str, want: &str) -> bool {
    text.lines().any(|line| line.trim() == want || line.contains(want))
}

// ---- The frame -------------------------------------------------------------

#[test]
fn every_body_sets_up_a_frame_and_takes_it_down() {
    let text = shown("fn f(a: i32): i32 { a }\n");
    assert!(has(&text, "pushq\t%rbp"), "{}", text);
    assert!(has(&text, "movq\t%rsp, %rbp"), "{}", text);
    assert!(has(&text, "leave"), "{}", text);
    assert!(has(&text, "ret"), "{}", text);
}

// A body with nothing in its frame does not move the stack pointer, which is
// two instructions saved on the commonest shape there is.
#[test]
fn a_body_with_nothing_to_hold_does_not_move_the_stack() {
    let text = shown("fn f(a: i32, b: i32): i32 { a + b }\n");
    assert!(!has(&text, "subq\t$"), "{}", text);
}

// A body that really does want room -- `sir::promote` takes out every slot
// whose address goes nowhere, so a local holding a number is not one.
#[test]
fn a_body_that_wants_room_takes_it_in_one_go() {
    let text = shown(
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn f(a: i64): i64 {\n    let p = P { a: a, b: a }\n    p.a + p.b\n}\n",
    );
    assert_eq!(text.lines().filter(|l| l.contains("subq\t$")).count(), 1, "{}", text);
}

// ---- The calling convention ------------------------------------------------

#[test]
fn a_parameter_is_moved_out_of_the_register_it_arrived_in() {
    let text = shown("fn f(a: i64, b: i64): i64 { a - b }\n");
    assert!(has(&text, "%rdi"), "the first argument register is never read: {}", text);
    assert!(has(&text, "%rsi"), "{}", text);
}

#[test]
fn an_answer_goes_back_in_the_register_a_caller_reads() {
    let text = shown("fn f(a: i64): i64 { a }\n");
    let at = text.find("leave").expect("an epilogue");
    assert!(text[..at].contains("%rax"), "{}", text);
}

#[test]
fn a_call_names_the_symbol_it_calls() {
    let text = shown("fn g(x: i32): i32 { x }\nfn f(): i32 { g(1) }\n");
    assert!(has(&text, "call\t__F1t1g3i32"), "{}", text);
}

// ---- The instructions this machine has to work around ----------------------

// A division wants `rdx:rax` and writes both, and neither is a register the
// allocator knows to keep clear -- so what is in the way is pushed.
#[test]
fn a_division_puts_the_registers_it_insists_on_out_of_the_way() {
    let text = shown("fn f(a: i32, b: i32): i32 { a / b }\n");
    assert!(has(&text, "pushq\t%rax"), "{}", text);
    assert!(has(&text, "pushq\t%rdx"), "{}", text);
    assert!(has(&text, "cltd"), "{}", text);
    assert!(has(&text, "idivl"), "{}", text);
    assert!(has(&text, "popq\t%rdx"), "{}", text);
}

#[test]
fn an_unsigned_division_clears_the_top_half_rather_than_extending_it() {
    let text = shown("fn f(a: u32, b: u32): u32 { a / b }\n");
    assert!(has(&text, "xorl\t%edx, %edx"), "{}", text);
    assert!(has(&text, "divl"), "{}", text);
    assert!(!has(&text, "cltd"), "an unsigned dividend has no sign to extend: {}", text);
}

// A shift wants its count in `cl` and nowhere else.
#[test]
fn a_shift_puts_its_count_where_the_machine_insists() {
    let text = shown("fn f(a: i64, b: i64): i64 { a << b }\n");
    assert!(has(&text, "pushq\t%rcx"), "{}", text);
    assert!(has(&text, "%cl"), "{}", text);
    assert!(has(&text, "popq\t%rcx"), "{}", text);
}

// ---- Widths ----------------------------------------------------------------

// The suffix is the whole of what says how wide an instruction is here, and a
// four-byte add written as an eight-byte one is a wrong answer that assembles.
#[test]
fn the_width_of_a_value_is_the_width_of_its_instruction() {
    let text = shown("fn f(a: i32, b: i32): i32 { a + b }\n");
    assert!(has(&text, "addl"), "{}", text);
    assert!(!has(&text, "addq"), "{}", text);

    let text = shown("fn f(a: i64, b: i64): i64 { a + b }\n");
    assert!(has(&text, "addq"), "{}", text);
}

#[test]
fn a_narrow_load_says_how_narrow_it_is() {
    let text = shown(
        "struct P {\n    pub a: i8,\n    pub b: i64,\n}\nfn f(p: &P): i8 { p.a }\n",
    );
    assert!(has(&text, "movb") || has(&text, "movzb"), "{}", text);
}

// ---- The pool --------------------------------------------------------------

#[test]
fn a_string_goes_in_a_section_nothing_writes_to() {
    let text = shown("fn f(): str { \"hi\" }\n");
    assert!(has(&text, ".section\t.rodata"), "{}", text);
    assert!(has(&text, ".byte"), "{}", text);
}

#[test]
fn every_body_is_given_a_name_the_linker_can_see() {
    let text = shown("fn f(): i32 { 1 }\n");
    assert!(has(&text, ".globl\t__F1t1f"), "{}", text);
    assert!(has(&text, ".type\t__F1t1f, @function"), "{}", text);
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
        let text = render(&lowered(source), X86_64).0;
        if let Some(said) = tried(&text, "x86_64-linux-gnu") {
            panic!("{}\n---- from ----\n{}", said, source);
        }
    }
}
