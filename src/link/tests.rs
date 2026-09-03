// What the shim says, and what this refuses before it runs anything.
//
// Nothing here runs a linker. Whether an assembler takes the output is
// `mir::asm`'s question and its own tests ask it; what is left for this file
// is the decisions made before any tool is reached.

use super::*;
use crate::mir::machine::Machine;
use crate::sir::target;

fn machine_named(name: &str) -> Machine {
    Machine::of(target::of(name).expect("a machine this compiler has"))
}

#[test]
fn an_entry_that_answers_becomes_the_exit_status() {
    let out = shim(&Entry { symbol: "__F5hello4main".to_string(), answers: true });
    assert!(out.contains("extern long __F5hello4main(void);"), "{}", out);
    assert!(out.contains("return (int)__F5hello4main();"), "{}", out);
    // The collector's roots are noted before anything the program wrote runs.
    assert!(out.find("__rt_init();").unwrap() < out.find("return (int)").unwrap(), "{}", out);
}

// A `main` giving nothing back must not have its leftover register read as an
// exit status: the shim exits zero and never names a `long`.
#[test]
fn an_entry_that_answers_nothing_exits_zero() {
    let out = shim(&Entry { symbol: "__F3app4main".to_string(), answers: false });
    assert!(out.contains("extern void __F3app4main(void);"), "{}", out);
    assert!(out.contains("return 0;"), "{}", out);
    assert!(!out.contains("long"), "{}", out);
}

// Cross-linking is turned down before a tool is run, and the message says
// which part of the job does cross.
#[test]
fn linking_for_another_machine_is_refused_with_a_reason() {
    let elsewhere = match here() {
        "aarch64" => machine_named("riscv64"),
        _ => machine_named("aarch64"),
    };
    let entry = Entry { symbol: "__F1t4main".to_string(), answers: true };
    let why = link("", &entry, elsewhere, Path::new("/dev/null"), None)
        .expect_err("linking for another machine should be refused");
    assert!(why.contains("cannot link for"), "{}", why);
    assert!(why.contains("--emit asm"), "{}", why);
}

// A runtime named that is not there is said plainly, rather than left to the
// linker to complain about a file it was handed.
#[test]
fn a_runtime_that_is_not_there_is_said_so() {
    let entry = Entry { symbol: "__F1t4main".to_string(), answers: true };
    let why = link(
        "",
        &entry,
        machine_named(here()),
        Path::new("/dev/null"),
        Some(Path::new("/nowhere/libfortec_rt.a")),
    )
    .expect_err("a missing archive should be refused");
    assert!(why.contains("no runtime archive at"), "{}", why);
}
