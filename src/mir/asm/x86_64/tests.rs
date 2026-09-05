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
use super::super::super::linear::{Line, Linear};
use super::super::super::machine::X86_64;
use super::super::super::regalloc::{Allocation, Where};
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
        // More arguments than there are registers, in both files and in the
        // two shapes that overflow before they look as though they do: a
        // struct handed back takes a register for the room, and a method
        // takes one for the receiver.
        "fn f(a: i64, b: i64, c: i64, d: i64, e: i64, g: i64, h: i64, i: i64, j: i64): i64 {\n\
         \x20   a + b + c + d + e + g + h + i + j\n}\n",
        "fn f(a: f64, b: f64, c: f64, d: f64, e: f64, g: f64, h: f64, i: f64,\n\
         \x20    j: f64, k: f64): f64 {\n    a + b + c + d + e + g + h + i + j + k\n}\n",
        "fn f(a: i64, b: f64, c: i64, d: f64, e: i64, g: f64, h: i64, i: f64,\n\
         \x20    j: i64, k: f64, l: i64, m: f64): f64 {\n\
         \x20   (a + c + e + h + j + l) as f64 + b + d + g + i + k + m\n}\n",
        "struct P {\n    pub x: i64,\n    pub y: i64,\n}\n\
         fn mk(a: i64, b: i64, c: i64, d: i64, e: i64, g: i64): P {\n\
         \x20   P { x: a + b + c, y: d + e + g }\n}\n\
         fn f(a: i64): i64 {\n    let p = mk(a, a, a, a, a, a)\n    p.x + p.y\n}\n",
        "fn g(a: i64, b: i64, c: i64, d: i64, e: i64, h: i64, i: i64, j: i64): i64 {\n\
         \x20   a + b + c + d + e + h + i + j\n}\n\
         fn f(a: i64): i64 { g(a, a, a, a, a, a, a, a) }\n",
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

// ---- Widening ----------------------------------------------------------------

// A narrow unsigned value widened to eight bytes. `movzlq` is the one extension
// that was never written -- a four-byte write already zeroes the top half -- so
// widening from four is a plain `movl`. Widening from one or two is not: those
// have `movzbq` and `movzwq`, and the `movl` shortcut taken for them named a
// byte register and a four-byte one in the same instruction.
//
// `bool` is the value this happens to, being the one-byte unsigned type a
// program actually writes: `v as i64` of one assembled as `movl %al, %ecx`,
// which the assembler refuses and no test caught, there being none that widened
// anything narrower than four.
#[test]
fn a_byte_widened_to_eight_does_not_name_two_widths_in_one_move() {
    let text = shown("fn f(v: bool): i64 {\n    v as i64\n}\n");
    assert!(!has(&text, "movl\t%al,"), "{}", text);
    assert!(has(&text, "movzb"), "{}", text);
}

#[test]
fn every_width_widens_to_something_an_assembler_takes() {
    let held = [
        "fn f(v: bool): i64 {\n    v as i64\n}\n",
        "fn f(v: u8): i64 {\n    v as i64\n}\n",
        "fn f(v: u16): i64 {\n    v as i64\n}\n",
        "fn f(v: u32): i64 {\n    v as i64\n}\n",
        "fn f(v: u8): u64 {\n    v as u64\n}\n",
        "fn f(v: i8): i64 {\n    v as i64\n}\n",
        "fn f(v: i16): i64 {\n    v as i64\n}\n",
        "fn f(v: i32): i64 {\n    v as i64\n}\n",
        "fn f(v: u8): i32 {\n    v as i32\n}\n",
        "fn f(v: bool): i32 {\n    v as i32\n}\n",
    ];
    for source in held {
        let text = render(&lowered(source), X86_64).0;
        if let Some(said) = tried(&text, "x86_64-linux-gnu") {
            panic!("{}\n---- from ----\n{}", said, source);
        }
    }
}

// ---- The three registers a copy insists on -----------------------------------

// `rep movsb` wants its two addresses in `rdi` and `rsi` and its count in
// `rcx`, and all three are registers the allocator hands out -- so either
// address may already be sitting in one of them. Setting the destination first
// then loses the source when the source *was* the destination's register, and
// what comes out is a copy of the destination onto itself.
//
// It is asserted as a shape because it is a shape: both addresses are read
// into the scratch registers before any of the three is touched, and the two
// `movq`s that fill `rdi` and `rsi` read from nowhere else.
#[test]
fn a_copy_reads_both_addresses_before_it_writes_either() {
    let text = shown(
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n",
    );
    let held: Vec<&str> = text
        .lines()
        .map(|line| line.trim())
        .filter(|line| line.starts_with("movq") && (line.ends_with("%rdi") || line.ends_with("%rsi")))
        .collect();
    assert!(!held.is_empty(), "nothing sets up a copy: {}", text);
    for line in held {
        let from = line.split_whitespace().nth(1).unwrap_or("").trim_end_matches(',');
        assert!(
            from == "%r10" || from == "%r11",
            "a copy reads its address out of {}, which the allocator may have \
             given to something: {}",
            from,
            line
        );
    }
}

// And what comes out still assembles, which is the only reader that knows.
#[test]
fn a_body_that_answers_with_an_aggregate_assembles() {
    let held = [
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n",
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n\
         fn f(n: i64): i64 {\n    let p = mk(n)\n    p.a + p.b\n}\n",
    ];
    for source in held {
        let text = render(&lowered(source), X86_64).0;
        if let Some(said) = tried(&text, "x86_64-linux-gnu") {
            panic!("{}\n---- from ----\n{}", said, source);
        }
    }
}


// ---- The two registers the divide names for itself ---------------------------

// `cqto` fills `%rdx` and the dividend goes in `%rax`, so a divisor allocated
// to either is destroyed before `idiv` reads it. The allocator does not know
// that -- nothing tells it an instruction claims a register -- so `divide`
// moves the divisor out of the way itself.
//
// Asserted as an invariant over the whole page rather than on one line: which
// register a divisor lands in is the allocator's to choose, so a test that
// pinned it would be testing the allocation and not the hazard. What must hold
// is that no divide anywhere reads one of the two.
fn divisors(text: &str) -> Vec<String> {
    text.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("idiv") || line.starts_with("div"))
        .filter_map(|line| line.split_whitespace().nth(1).map(str::to_string))
        .collect()
}

// The hazard built rather than hoped for. Which register a divisor lands in is
// the allocator's to choose, and it does not choose `%rdx` for any source
// written here -- but it chose it for a real one, and only for one of the two
// phi orderings the compiler used to produce at random. So the allocation is
// made by hand: this is the one shape that has to be right, and waiting for
// the allocator to stumble into it again is not a test.
fn int(name: &'static str) -> Reg {
    Reg { name, class: Class::Int }
}

fn divided(lhs: Reg, rhs: Reg, op: MIRBinOp) -> String {
    let regs = vec![MIRReg::one(Class::Int, 8, 1, 1); 3];
    let held = Linear {
        symbol: "__F1t1f".to_string(),
        regs,
        frame: Vec::new(),
        params: vec![1, 2],
        lines: vec![Line::Inst(MIRInst {
            def:  Some(0),
            kind: MIRInstKind::Bin { op, lhs: 1, rhs: 2 },
            line: 1,
            col:  1,
        })],
    };
    let at = Allocation {
        at:     vec![Where::In(int("rcx")), Where::In(lhs), Where::In(rhs)],
        spills: 0,
        most:   3,
    };
    let b = Body::new(&held, &at, X86_64, 0);
    let mut out = String::new();
    divide(&mut out, &b, 0, op, 1, 2);
    out
}

// The divisor in each of the two registers the instruction writes for itself,
// and the dividend in the other, which is every way of colliding there is.
#[test]
fn a_divisor_in_a_register_the_divide_writes_is_moved_out_of_the_way() {
    for op in [MIRBinOp::SDiv, MIRBinOp::SRem, MIRBinOp::UDiv, MIRBinOp::URem] {
        for (lhs, rhs) in [
            (int("r8"), int("rdx")),
            (int("r8"), int("rax")),
            (int("rax"), int("rdx")),
            (int("rdx"), int("rax")),
        ] {
            let out = divided(lhs, rhs, op);
            for held in divisors(&out) {
                assert!(
                    !matches!(held.as_str(), "%rax" | "%eax" | "%rdx" | "%edx"),
                    "{:?} with the divisor in {} reads {}:\n{}",
                    op,
                    rhs.name,
                    held,
                    out
                );
            }
            if let Some(said) = tried(&format!("f:\n{}", out), "x86_64-linux-gnu") {
                panic!("{:?}: {}\n{}", op, said, out);
            }
        }
    }
}

#[test]
fn a_divide_never_reads_the_registers_it_writes_for_itself() {
    // Enough live values at once that the allocator has reason to reach for
    // `%rax` and `%rdx`: they are the first two it hands out.
    let sources = [
        "fn f(a: i64, b: i64): i64 { a / b }\n",
        "fn f(a: i64, b: i64): i64 { a % b }\n",
        "fn f(a: i64, b: i64, c: i64, d: i64): i64 { (a / b) + (c / d) }\n",
        "fn f(a: i64, b: i64, c: i64, d: i64): i64 { (a % b) * (c / d) + a }\n",
        "fn f(a: i32, b: i32): i32 { a / b }\n",
        "fn f(a: u64, b: u64): u64 { a / b }\n",
        "fn f(a: i64): i64 {\n    var t = 0\n    var i = 1\n    while i < 20 { t = t + (a / i); i = i + 1 }\n    t\n}\n",
    ];
    for source in sources {
        let text = shown(source);
        for held in divisors(&text) {
            assert!(
                !matches!(held.as_str(), "%rax" | "%eax" | "%rdx" | "%edx"),
                "a divide reads {}, which it writes for itself:\n{}",
                held,
                text
            );
        }
    }
}

// And the whole thing still assembles, which is what says the rescue move is
// an instruction and not merely a plausible line.
#[test]
fn a_rescued_divide_still_assembles() {
    let text = shown("fn f(a: i64, b: i64, c: i64, d: i64): i64 { (a / b) + (c % d) }\n");
    if let Some(said) = tried(&text, "x86_64-linux-gnu") {
        panic!("{}\n{}", said, text);
    }
}
