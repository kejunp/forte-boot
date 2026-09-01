// What a machine description has to be true of before anything allocates
// against it.
//
// Every one of these is a rule an allocator leans on without asking. A
// register in neither the saved list nor the clobbered one is a register
// nothing knows whether a call keeps; one in both is a contradiction that
// would be read whichever way the code happened to ask. Neither is a mistake
// that shows up as a wrong answer -- both show up as a value that is fine
// until something calls something.

use super::*;

fn machines() -> Vec<Machine> {
    vec![X86_64, AARCH64, RISCV64]
}

fn allocatable(m: &Machine) -> Vec<Reg> {
    m.ints.iter().chain(m.floats.iter()).copied().collect()
}

#[test]
fn every_allocatable_register_is_saved_or_clobbered_and_not_both() {
    for m in machines() {
        for reg in allocatable(&m) {
            let saved = m.saved.contains(&reg);
            let gone = m.clobbered.contains(&reg);
            assert!(saved || gone, "{}: {} is in neither list", m.name, reg.name);
            assert!(!(saved && gone), "{}: {} is in both lists", m.name, reg.name);
        }
    }
}

#[test]
fn nothing_is_named_twice_in_a_file() {
    for m in machines() {
        let held = allocatable(&m);
        for (at, reg) in held.iter().enumerate() {
            assert!(
                !held[at + 1..].contains(reg),
                "{}: {} is in a file twice",
                m.name,
                reg.name
            );
        }
    }
}

#[test]
fn a_file_holds_only_its_own_class() {
    for m in machines() {
        for reg in m.ints {
            assert_eq!(reg.class, Class::Int, "{}: {} is not an integer", m.name, reg.name);
        }
        for reg in m.floats {
            assert_eq!(reg.class, Class::Float, "{}: {} is not a float", m.name, reg.name);
        }
    }
}

// An argument goes somewhere the allocator also hands out, which is what makes
// a call worth allocating around: the register is contended for, and that is
// the whole of why arguments are put in before anything else.
#[test]
fn every_argument_and_answer_register_is_allocatable() {
    for m in machines() {
        let held = allocatable(&m);
        for reg in m.args.iter().chain(m.fargs.iter()) {
            assert!(held.contains(reg), "{}: {} is passed in and never handed out", m.name, reg.name);
        }
        assert!(held.contains(&m.ret), "{}: {} answers and is never handed out", m.name, m.ret.name);
        assert!(held.contains(&m.fret), "{}: {} answers and is never handed out", m.name, m.fret.name);
    }
}

// The frame is the one register that holds the same thing for the whole of a
// body. An allocator that could hand it out would eventually give away what
// every spill slot is written against.
#[test]
fn the_frame_register_is_never_handed_out() {
    for m in machines() {
        assert!(
            !allocatable(&m).contains(&m.frame),
            "{}: {} holds the frame and is allocatable",
            m.name,
            m.frame.name
        );
    }
}

// An argument register that a call keeps would be one the callee could not
// write to, which is not what either ABI says.
#[test]
fn no_argument_register_survives_a_call() {
    for m in machines() {
        for reg in m.args.iter().chain(m.fargs.iter()) {
            assert!(!m.keeps(*reg), "{}: {} is passed in and kept", m.name, reg.name);
        }
    }
}

#[test]
fn a_class_is_allocated_and_passed_out_of_its_own_file() {
    for m in machines() {
        for class in [Class::Int, Class::Float] {
            for reg in m.file(class) {
                assert_eq!(reg.class, class, "{}: {} is in the wrong file", m.name, reg.name);
            }
            for reg in m.passing(class) {
                assert_eq!(reg.class, class, "{}: {} passes the wrong class", m.name, reg.name);
            }
            assert_eq!(m.answering(class).class, class, "{}: the wrong class answers", m.name);
        }
    }
}

// ---- Which machine a target names ------------------------------------------

#[test]
fn every_target_name_reaches_a_machine() {
    for name in target::NAMES {
        let t = target::of(name).expect("a named target");
        let m = Machine::of(t);
        assert!(m.word > 0, "{} has no pointer", name);
        assert!(!m.ints.is_empty(), "{} has no registers", name);
    }
}

// The vector variants differ in what a vector holds and in nothing else, which
// is why they are one register file carrying a different `Target`.
#[test]
fn the_x86_variants_are_one_machine_with_different_vectors() {
    let wide = Machine::of(target::X86_64_V4);
    let narrow = Machine::of(target::X86_64);
    assert_eq!(wide.ints, narrow.ints, "the same registers");
    assert_eq!(wide.name, narrow.name, "the same machine");
    assert_ne!(wide.vectors.bytes, narrow.vectors.bytes, "different vectors");
    assert_eq!(wide.vectors.bytes, target::X86_64_V4.bytes, "the target it was asked for");
}

#[test]
fn aarch64_is_its_own_machine() {
    let m = Machine::of(target::AARCH64);
    assert_eq!(m.name, "aarch64");
    assert_eq!(m.ret.name, "x0");
}

// A target with no vectors names no architecture either, so the machine
// running this is what answers -- the same fallback `sir::target` makes.
#[test]
fn a_target_with_no_vectors_falls_back_to_the_host() {
    let m = Machine::of(target::NONE);
    assert_eq!(m.name, host().name);
    assert_eq!(m.vectors.bytes, 0, "and still widens nothing");
}

// ---- What an emitter is allowed to work through ----------------------------

// A scratch register the allocator might also hand out is not scratch: the
// emitter would put a spilled operand in a register that was holding something
// else, and the something else would be gone.
#[test]
fn no_scratch_register_is_also_allocatable() {
    for m in machines() {
        for held in m.scratch.iter().chain(m.fscratch.iter()) {
            assert!(
                !allocatable(&m).contains(held),
                "{}: {} is both scratch and allocatable",
                m.name,
                held.name
            );
        }
    }
}

// Two of each, which is what the widest expansion wants: a copy reads through
// one and writes through the other.
#[test]
fn there_are_two_scratch_registers_in_each_file() {
    for m in machines() {
        assert!(m.scratch.len() >= 2, "{}: {} integer", m.name, m.scratch.len());
        assert!(m.fscratch.len() >= 2, "{}: {} float", m.name, m.fscratch.len());
    }
}

// Using one across a call would be using a register a call may write, so every
// one of them has to be one a call was already going to write.
#[test]
fn no_scratch_register_is_one_a_call_keeps() {
    for m in machines() {
        for held in m.scratch.iter().chain(m.fscratch.iter()) {
            assert!(!m.keeps(*held), "{}: {} is callee-saved", m.name, held.name);
        }
    }
}

// The two an emitter names and never hands out. A stack pointer in the
// allocatable list is a stack pointer that will one day hold an integer.
#[test]
fn neither_the_stack_pointer_nor_the_frame_pointer_is_allocatable() {
    for m in machines() {
        assert!(!allocatable(&m).contains(&m.sp), "{}: {}", m.name, m.sp.name);
        assert!(!allocatable(&m).contains(&m.frame), "{}: {}", m.name, m.frame.name);
        assert_ne!(m.sp, m.frame, "{}", m.name);
    }
}

// ---- riscv64 ---------------------------------------------------------------

#[test]
fn every_target_name_reaches_a_machine_of_its_own() {
    assert_eq!(Machine::of(target::RISCV64).name, "riscv64");
    assert_eq!(Machine::of(target::AARCH64).name, "aarch64");
    assert_eq!(Machine::of(target::X86_64).name, "x86-64");
    // The wide variants are the same registers with a different vector answer.
    assert_eq!(Machine::of(target::X86_64_V4).name, "x86-64");
    assert_eq!(Machine::of(target::X86_64_V4).vectors.bytes, 64);
}

// The baseline has none, and saying so is what keeps `sir::opt` from widening
// anything for a machine that could not run it.
#[test]
fn riscv_says_it_has_no_vectors() {
    assert_eq!(RISCV64.vectors.bytes, 0);
}

// `a0` is where the first argument arrives and where the answer goes back,
// which is one register doing two jobs and is what the ABI says.
#[test]
fn riscv_answers_where_its_first_argument_arrived() {
    assert_eq!(RISCV64.ret, RISCV64.args[0]);
    assert_eq!(RISCV64.fret, RISCV64.fargs[0]);
}
