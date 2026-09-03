// The parts of emitting that are the same for every machine.
//
// Three of them, and each is a thing that is wrong silently. A symbol an
// assembler will not take is a build that fails loudly and is easy; a symbol
// two different fns escape to the *same* name is a program that links and
// calls the wrong one. An order of moves that writes over a value something
// else still wanted is a wrong answer in a body with enough arguments to have
// a cycle, and in no body smaller. A frame whose saved registers overlap its
// slots is a value that changes when a call is made.

use super::super::machine::{Class, Reg, AARCH64, RISCV64, X86_64};
use super::*;

fn int(name: &'static str) -> Reg {
    Reg { name, class: Class::Int }
}

// ---- Names an assembler will take ------------------------------------------

#[test]
fn a_name_that_is_already_plain_is_left_alone() {
    assert_eq!(symbol("__rt_gc_alloc"), "__rt_gc_alloc");
    assert_eq!(symbol("__F1t1f"), "__F1t1f");
    assert_eq!(symbol("__S1"), "__S1");
}

// The characters the mangling really puts in. Every one of them is a character
// a symbol may not have, and the first three turn up in any program with a
// reference, a module or an array in a signature.
#[test]
fn the_characters_a_spelling_holds_are_escaped() {
    assert_eq!(symbol("&"), ".26");
    assert_eq!(symbol("a::b"), "a.3a.3ab");
    assert_eq!(symbol("x[3]"), "x.5b3.5d");
    assert_eq!(symbol("Vec<i32>"), "Vec.3ci32.3e");
    assert_eq!(symbol("fn(i32):str"), "fn.28i32.29.3astr");
}

// The one that matters more than the rest. Two fns whose names escaped to one
// name would link, and one of them would be the other.
#[test]
fn no_two_names_escape_to_the_same_name() {
    let held = [
        "a.b", "a&b", "ab", "a:b", "a::b", "a.3ab", "a[b]", "a b", "a,b", "a<b>",
        "__F2rt4keep9&rt::Node", "__F2rt4keep9&rt::Nodf",
    ];
    let mut out: Vec<String> = held.iter().map(|one| symbol(one)).collect();
    out.sort();
    let all = out.len();
    out.dedup();
    assert_eq!(out.len(), all, "two of {:?} came out the same", held);
}

// A dot is what an escape begins with, so a dot that was in the name has to be
// escaped too -- that is the whole of why the mapping is one-to-one.
#[test]
fn a_dot_in_a_name_is_escaped_like_anything_else() {
    assert_eq!(symbol("a.b"), "a.2eb");
    assert_ne!(symbol("a.b"), symbol("a:b"));
}

#[test]
fn every_escaped_name_is_letters_digits_underscores_and_dots() {
    for one in ["&x", "a::b<c>[1]", "fn(i32):str", "$c2"] {
        for held in symbol(one).chars() {
            assert!(
                held.is_ascii_alphanumeric() || held == '_' || held == '.',
                "{} came out of {}",
                held,
                one
            );
        }
    }
}

// ---- Moving several registers at once --------------------------------------

// Read it back: what each register holds after the steps have run, given what
// each held before. Asserting on the *result* rather than on the instructions
// is the only way to check this -- there are several right orders and the
// question is whether the answer is right, not which one was picked.
fn settled(moves: &[(Reg, Reg)]) -> Vec<(&'static str, &'static str)> {
    let mut held: Vec<(&'static str, &'static str)> = Vec::new();
    for (to, from) in moves {
        for one in [to.name, from.name] {
            if !held.iter().any(|(at, _)| *at == one) {
                // Every register begins holding a value named after itself.
                held.push((one, one));
            }
        }
    }
    let mut scratch = "?";
    for step in ordered(moves) {
        match step {
            Step::Move { to, from } => {
                let one = reads(&held, from.name);
                writes(&mut held, to.name, one);
            }
            Step::Save(from) => scratch = reads(&held, from.name),
            Step::Restore(to) => writes(&mut held, to.name, scratch),
        }
    }
    held
}

fn reads(held: &[(&'static str, &'static str)], name: &str) -> &'static str {
    held.iter().find(|(at, _)| *at == name).map(|(_, one)| *one).unwrap_or("?")
}

fn writes(held: &mut [(&'static str, &'static str)], name: &str, one: &'static str) {
    for entry in held.iter_mut() {
        if entry.0 == name {
            entry.1 = one;
        }
    }
}

// What each register was asked to end up holding, whatever order it took.
fn holds(moves: &[(Reg, Reg)]) {
    let out = settled(moves);
    for (to, from) in moves {
        let got = out.iter().find(|(at, _)| *at == to.name).map(|(_, one)| *one);
        assert_eq!(
            got,
            Some(from.name),
            "{} should hold what {} held: {:?}",
            to.name,
            from.name,
            out
        );
    }
}

#[test]
fn a_move_to_itself_is_no_move_at_all() {
    assert!(ordered(&[(int("rax"), int("rax"))]).is_empty());
}

#[test]
fn moves_that_do_not_touch_each_other_all_happen() {
    holds(&[(int("rax"), int("rdi")), (int("rbx"), int("rsi"))]);
}

// A chain has one order that works and the ordering has to find it: writing
// `rax` before reading it would lose what it held.
#[test]
fn a_chain_is_made_from_the_end_that_is_not_wanted() {
    holds(&[(int("rax"), int("rbx")), (int("rbx"), int("rcx"))]);
}

// The one the first version got wrong. A swap has no order that works without
// somewhere to put one of the two, and the one to put away is the one about to
// be written over.
#[test]
fn two_registers_can_be_swapped() {
    holds(&[(int("rcx"), int("rsi")), (int("rsi"), int("rcx"))]);
}

#[test]
fn a_ring_of_three_comes_out_rotated() {
    holds(&[
        (int("rax"), int("rbx")),
        (int("rbx"), int("rcx")),
        (int("rcx"), int("rax")),
    ]);
}

// Six arguments is where a real program meets this, and the permutation that
// turned up in one was a chain and a swap at once.
#[test]
fn a_chain_and_a_ring_at_once_both_come_out_right() {
    holds(&[
        (int("rax"), int("rdi")),
        (int("rcx"), int("rsi")),
        (int("rsi"), int("rcx")),
        (int("rdi"), int("r8")),
        (int("r8"), int("r9")),
    ]);
}

// Two cycles at once, which is where reading the scratch back too early or
// too late would show as one of them holding the other's value.
#[test]
fn two_separate_rings_do_not_borrow_each_others_scratch() {
    holds(&[
        (int("rax"), int("rbx")),
        (int("rbx"), int("rax")),
        (int("rcx"), int("rdx")),
        (int("rdx"), int("rcx")),
    ]);
}

// Nothing is saved where nothing is in the way, or every call would pay for a
// cycle it did not have.
#[test]
fn nothing_is_put_aside_where_no_cycle_needs_it() {
    let held = ordered(&[(int("rax"), int("rdi")), (int("rdi"), int("r8"))]);
    assert!(!held.iter().any(|step| matches!(step, Step::Save(_))), "{:?}", held);
}

// ---- Where the arguments go ------------------------------------------------

// The two files are counted apart: the third integer argument is in the third
// integer register however many floats were written before it.
#[test]
fn the_two_files_are_counted_separately() {
    let held = passing(X86_64, &[Class::Int, Class::Float, Class::Int]);
    assert_eq!(held[0], Some(X86_64.args[0]));
    assert_eq!(held[1], Some(X86_64.fargs[0]));
    assert_eq!(held[2], Some(X86_64.args[1]), "the float did not use up an integer one");
}

// More than there are registers for, which is the case nothing here emits.
#[test]
fn a_class_that_runs_out_of_registers_says_so() {
    let many = vec![Class::Int; X86_64.args.len() + 1];
    let held = passing(X86_64, &many);
    assert!(held.last().expect("one").is_none());
    assert!(held[..many.len() - 1].iter().all(|one| one.is_some()));
}

#[test]
fn every_machine_passes_its_first_argument_in_its_first_register() {
    for m in [X86_64, AARCH64, RISCV64] {
        let held = passing(m, &[Class::Int]);
        assert_eq!(held[0], Some(m.args[0]), "{}", m.name);
    }
}

// ---- The frame -------------------------------------------------------------

use super::super::fixture::*;

fn framed(source: &str, m: super::super::machine::Machine) -> (String, Vec<String>) {
    render(&lowered(source), m)
}

// Every machine puts the saved registers under the frame pointer and the slots
// under those, so that a slot's offset does not depend on how many registers
// turned out to be worth saving.
#[test]
fn nothing_in_a_frame_overlaps_the_registers_saved_above_it() {
    let p = lowered(
        "fn f(a: i64, b: i64, c: i64, d: i64, e: i64, g: i64): i64 {\n\
         \x20   let h = a * b\n    let i = c * d\n    let j = e * g\n\
         \x20   let k = h + i\n    let l = i + j\n    h + i + j + k + l\n}\n",
    );
    for m in [X86_64, AARCH64, RISCV64] {
        let body = &p.bodies[0];
        let mut held = super::super::linear::linearise(body);
        let at = super::super::regalloc::allocate(&mut held, m);
        let one = Body::new(&held, &at, m, 0);
        let above = one.saved.len() * m.word;
        for off in &one.offsets {
            assert!(*off > above, "{}: a slot at {} is inside the saved area", m.name, off);
            assert!(*off <= one.frame, "{}: a slot at {} is past the frame", m.name, off);
        }
        for which in 0..one.saved.len() {
            assert!(one.saved_at(which) <= above, "{}", m.name);
        }
    }
}

#[test]
fn a_frame_is_a_whole_number_of_what_the_stack_stays_aligned_to() {
    for m in [X86_64, AARCH64, RISCV64] {
        let p = lowered("fn f(): i32 {\n    var x = 1\n    x\n}\n");
        let body = &p.bodies[0];
        let mut held = super::super::linear::linearise(body);
        let at = super::super::regalloc::allocate(&mut held, m);
        let one = Body::new(&held, &at, m, 0);
        assert_eq!(one.frame % m.stack, 0, "{}: {}", m.name, one.frame);
    }
}

// Only the ones it writes: saving a register the body never touches is two
// instructions for nothing.
#[test]
fn a_body_saves_only_the_registers_it_writes() {
    let p = lowered("fn f(a: i32): i32 { a }\n");
    let body = &p.bodies[0];
    let mut held = super::super::linear::linearise(body);
    let at = super::super::regalloc::allocate(&mut held, X86_64);
    let one = Body::new(&held, &at, X86_64, 0);
    assert!(one.saved.is_empty(), "{:?}", one.saved);
}

// ---- A label is a name in the whole file -----------------------------------

// Every body has a block one, and in one file they cannot all be `.L1`.
#[test]
fn two_bodies_do_not_share_a_label() {
    for m in [X86_64, AARCH64, RISCV64] {
        let (text, _) = framed(
            "fn f(a: i32): i32 { if a > 0 { 1 } else { 2 } }\n\
             fn g(a: i32): i32 { if a > 0 { 3 } else { 4 } }\n",
            m,
        );
        let mut labels: Vec<&str> = text
            .lines()
            .filter(|line| line.starts_with(".L") && line.ends_with(':'))
            .collect();
        let all = labels.len();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(labels.len(), all, "{}: a label is written twice", m.name);
        assert!(all > 2, "{}: this wants several", m.name);
    }
}

// ---- What is refused -------------------------------------------------------

// A body with no vectors in it has nothing to say.
#[test]
fn an_ordinary_body_is_not_refused() {
    for m in [X86_64, AARCH64, RISCV64] {
        let (_, said) = framed("fn f(a: i32, b: i32): i32 { a + b }\n", m);
        assert!(said.is_empty(), "{}: {:?}", m.name, said);
    }
}


// ---- The segment a global lives in ------------------------------------------

fn one(symbol: &str, bytes: Vec<u8>, align: usize) -> MIRGlobal {
    MIRGlobal { symbol: symbol.to_string(), bytes, align }
}

// `.data` and not `.rodata`, which is the whole reason this is not the pool: a
// global may be assigned to, and a store into `.rodata` faults.
#[test]
fn a_global_goes_in_a_segment_that_may_be_written_to() {
    let out = data(&[one("__G1t1g", vec![7, 0, 0, 0, 0, 0, 0, 0], 8)], false);
    assert!(out.contains(".section\t.data"), "{}", out);
    assert!(!out.contains(".rodata"), "{}", out);
    assert!(out.contains("__G1t1g:"), "{}", out);
    assert!(out.contains(".byte\t7, 0, 0, 0, 0, 0, 0, 0"), "{}", out);
    assert!(out.contains(".size\t__G1t1g, .-__G1t1g"), "{}", out);
}

// x86-64's `.align` counts bytes and the other two count the power of two,
// which is the one difference between the machines here and the same one the
// pool has.
#[test]
fn the_alignment_is_said_the_way_the_machine_says_it() {
    let held = [one("__G1t1g", vec![0; 8], 8)];
    assert!(data(&held, false).contains(".align\t8"), "{}", data(&held, false));
    assert!(data(&held, true).contains(".align\t3"), "{}", data(&held, true));
}

// Nothing at all where there are no globals: an empty `.data` directive would
// be a section in every object for the programs that have none.
#[test]
fn no_globals_is_no_segment() {
    assert_eq!(data(&[], false), "");
}
