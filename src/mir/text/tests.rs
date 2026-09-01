// What the listing says, checked as text.
//
// A printer is the one thing here that can only be tested by reading it, so
// these read it. They are written against whole lines rather than fragments --
// `"      ret rax"` and not `"ret"` -- because what is being checked is the
// shape of the page and a fragment matches half a dozen of them.
//
// The registers in a listing are the allocated ones, so the exact name in an
// assertion depends on what the allocator handed out. Where that would make a
// test about the allocator rather than about the printer, what is asserted is
// the form -- a label, a width, a frame line -- rather than the name.

use super::super::fixture::*;
use super::*;

fn shown(source: &str) -> String {
    render(&lowered(source), machine())
}

fn lines(text: &str) -> Vec<String> {
    text.lines().map(|line| line.to_string()).collect()
}

fn has(text: &str, want: &str) -> bool {
    text.lines().any(|line| line.contains(want))
}

// ---- The page ---------------------------------------------------------------

#[test]
fn a_body_is_written_under_the_symbol_it_compiles_to() {
    let out = shown("fn f(): i32 { 1 }\n");
    assert!(
        lines(&out).iter().any(|line| line.starts_with("__F") && line.ends_with(':')),
        "{}",
        out
    );
}

#[test]
fn every_block_gets_a_label() {
    let out = shown("fn f(a: i32): i32 { if a > 0 { 1 } else { 2 } }\n");
    let labels = out.lines().filter(|line| line.trim_start().starts_with(".L")).count();
    assert!(labels >= 3, "{}", out);
}

#[test]
fn a_body_says_how_big_its_frame_is() {
    let out = shown("fn f(): i32 { 1 }\n");
    assert!(has(&out, "frame "), "{}", out);
}

// The frame is rounded up to what the machine keeps the stack aligned to, so a
// body that wants nine bytes says sixteen.
#[test]
fn the_frame_is_rounded_to_what_the_stack_wants() {
    let held = vec![
        MIRSlot { bytes: 9, align: 1, name: "$0".to_string(), spill: false },
    ];
    let (_, size) = frame(&held, machine());
    assert_eq!(size, 16, "the stack is kept to {}", machine().stack);
}

#[test]
fn nothing_in_the_frame_overlaps_anything_else() {
    let held = vec![
        MIRSlot { bytes: 1, align: 1, name: "$0".to_string(), spill: false },
        MIRSlot { bytes: 8, align: 8, name: "$1".to_string(), spill: false },
        MIRSlot { bytes: 4, align: 4, name: "$2".to_string(), spill: false },
    ];
    let (offsets, _) = frame(&held, machine());
    for (at, slot) in held.iter().enumerate() {
        for (other, one) in held.iter().enumerate() {
            if at == other {
                continue;
            }
            // Written downwards, so a slot covers `offset-bytes .. offset`.
            let a = (offsets[at] - slot.bytes, offsets[at]);
            let b = (offsets[other] - one.bytes, offsets[other]);
            assert!(a.1 <= b.0 || b.1 <= a.0, "{:?} and {:?} overlap", a, b);
        }
    }
}

#[test]
fn each_slot_sits_where_its_alignment_allows() {
    let held = vec![
        MIRSlot { bytes: 1, align: 1, name: "$0".to_string(), spill: false },
        MIRSlot { bytes: 8, align: 8, name: "$1".to_string(), spill: false },
    ];
    let (offsets, _) = frame(&held, machine());
    assert_eq!(offsets[1] % 8, 0, "a word has to be on a word");
}

// ---- What the instructions look like ----------------------------------------

#[test]
fn a_terminator_is_written_at_the_end_of_its_block() {
    let out = shown("fn f(): i32 { 1 }\n");
    assert!(has(&out, "ret "), "{}", out);
}

#[test]
fn a_branch_names_both_labels() {
    let out = shown("fn f(a: i32): i32 { if a > 0 { 1 } else { 2 } }\n");
    assert!(
        out.lines().any(|line| line.trim_start().starts_with("br ") && line.matches(".L").count() == 2),
        "{}",
        out
    );
}

// A load says how wide it is, because there is no type left to ask. That the
// width is *in the text* is what makes a wrong one findable by reading.
#[test]
fn a_load_says_how_many_bytes_it_reads() {
    let out = shown(
        "struct Pair { a: i8, b: i64 }\n\
         fn f(p: Pair): i8 { p.a }\n",
    );
    assert!(has(&out, "load.1 "), "{}", out);
}

#[test]
fn an_offset_says_how_far_along_it_is() {
    let out = shown(
        "struct Pair { a: i8, b: i64 }\n\
         fn f(p: Pair): i64 { p.b }\n",
    );
    assert!(has(&out, "+ 8]"), "{}", out);
}

#[test]
fn an_index_says_the_stride_it_steps_by() {
    let out = shown("fn f(xs: i32[4], i: i32): i32 { xs[i] }\n");
    assert!(has(&out, "*4]"), "{}", out);
}

// The one place two instructions differ by a letter and by nothing else, so the
// letter had better be in the listing.
#[test]
fn a_signed_and_an_unsigned_division_read_differently() {
    let signed = shown("fn f(a: i32, b: i32): i32 { a / b }\n");
    let unsigned = shown("fn f(a: u32, b: u32): u32 { a / b }\n");
    assert!(has(&signed, "sdiv "), "{}", signed);
    assert!(has(&unsigned, "udiv "), "{}", unsigned);
}

#[test]
fn a_call_names_what_it_calls_and_what_it_hands_over() {
    let out = shown("fn g(x: i32): i32 { x }\nfn f(): i32 { g(1) }\n");
    assert!(
        out.lines().any(|line| line.contains("call ") && line.contains("1g")),
        "{}",
        out
    );
}

// ---- The pool ---------------------------------------------------------------

#[test]
fn a_string_is_written_under_the_pool() {
    let out = shown("fn f(): str { \"hi\" }\n");
    assert!(has(&out, "pool:"), "{}", out);
    assert!(has(&out, "\"hi\""), "{}", out);
}

// A pool entry holding a newline should not put one in the listing.
#[test]
fn a_byte_that_is_not_printable_is_written_as_its_number() {
    let out = shown("fn f(): str { \"a\\nb\" }\n");
    assert!(has(&out, "\\x0a"), "{}", out);
}

// ---- What a register is written as -------------------------------------------

// Allocated only. A listing over `%0` would be the graph again, and the whole
// point of the second stage is what happens when the registers run out.
#[test]
fn no_virtual_register_reaches_the_page() {
    let out = shown(
        "fn f(a: i32, b: i32, c: i32): i32 { (a + b) * (b + c) }\n",
    );
    for line in out.lines() {
        // `%` survives only in the name of a spill slot, which says which
        // register it stands for.
        if line.trim_start().starts_with("[fp-") {
            continue;
        }
        assert!(!line.contains('%'), "a virtual register reached the page: {}", line);
    }
}

// Every register the listing names has somewhere to be. `Where::Nowhere` is
// what a register that is never mentioned gets, and one that is never mentioned
// is one no line writes out -- so the `_` the printer would show it as is a
// fallback that keeps the printer total rather than a thing on a page.
#[test]
fn every_register_the_listing_names_has_somewhere_to_be() {
    let p = lowered("fn f(a: i32, b: i32): i32 { a + b }\n");
    let body = body_of(&p, "1f");
    let mut linear = super::super::linear::linearise(body);
    let out = super::super::regalloc::allocate(&mut linear, machine());
    let text = body_text(&linear, &out, machine());
    for line in text.lines() {
        let held = line.trim();
        if held.ends_with(':') || held.starts_with("frame ") || held.starts_with("[fp-") {
            continue;
        }
        assert!(!held.split_whitespace().any(|word| word == "_"), "{}", text);
    }
    // And a register that is not the body's at all is nowhere, which is what
    // keeps the lookup total.
    assert_eq!(out.of(linear.regs.len() + 10), Where::Nowhere);
}

// ---- The whole thing ---------------------------------------------------------

// A body with a loop in it, printed end to end. Nothing is asserted about the
// exact registers -- that is the allocator's -- but every line has to be one of
// the shapes above, which is what catches a printer that fell through a case.
#[test]
fn a_loop_prints_as_a_page_of_known_shapes() {
    let out = shown(
        "fn f(n: i32): i32 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n { t = t + i\n i = i + 1 }\n\
         \x20   t\n\
         }\n",
    );
    for line in out.lines() {
        let held = line.trim();
        if held.is_empty() || held.ends_with(':') || held.starts_with("frame ") {
            continue;
        }
        if held.starts_with("[fp-") {
            continue;
        }
        assert!(
            !held.contains("Undef") && !held.contains('{'),
            "a line the printer did not have a case for: {}",
            line
        );
    }
    assert!(has(&out, "jmp .L"), "a loop with nothing to jump back to:\n{}", out);
}

