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

fn program(entry: Entry) -> String {
    shim(&Start::Program(entry))
}

fn runner(names: &[&str]) -> String {
    let held: Vec<Test> = names
        .iter()
        .map(|name| Test {
            name:   (*name).to_string(),
            symbol: format!("__F1t{}{}", name.len(), name),
        })
        .collect();
    shim(&Start::Tests(held))
}

#[test]
fn an_entry_that_answers_becomes_the_exit_status() {
    let out = program(Entry { symbol: "__F5hello4main".to_string(), answers: true });
    assert!(out.contains("extern long __F5hello4main(void);"), "{}", out);
    assert!(out.contains("return (int)__F5hello4main();"), "{}", out);
    // The collector's roots are noted before anything the program wrote runs.
    assert!(out.find("__rt_init();").unwrap() < out.find("return (int)").unwrap(), "{}", out);
}

// A `main` giving nothing back must not have its leftover register read as an
// exit status: the shim exits zero and never declares the entry as answering
// one.
#[test]
fn an_entry_that_answers_nothing_exits_zero() {
    let out = program(Entry { symbol: "__F3app4main".to_string(), answers: false });
    assert!(out.contains("extern void __F3app4main(void);"), "{}", out);
    assert!(out.contains("return 0;"), "{}", out);
    assert!(!out.contains("long __F3app4main"), "{}", out);
    assert!(!out.contains("(int)"), "{}", out);
}

// What the kernel handed over reaches the runtime, and reaches it before
// anything the program wrote runs -- a first line that reads an argument is a
// first line, and there is nowhere earlier to have read them in.
#[test]
fn the_arguments_are_handed_over_before_the_program_starts() {
    for answers in [true, false] {
        let out = program(Entry { symbol: "__F3app4main".to_string(), answers });
        assert!(out.contains("int main(int argc, char **argv)"), "{}", out);
        assert!(out.contains("__rt_args((long)argc, argv);"), "{}", out);
        let args = out.find("__rt_args(").expect("the handover");
        let init = out.find("__rt_init();").expect("the init");
        let body = out.find("__F3app4main();").or_else(|| out.find("(int)__F3app4main()"));
        assert!(args < init, "{}", out);
        assert!(init < body.expect("the call"), "{}", out);
    }
}

// Cross-linking is turned down before a tool is run, and the message says
// which part of the job does cross.
#[test]
fn linking_for_another_machine_is_refused_with_a_reason() {
    let elsewhere = match here() {
        "aarch64" => machine_named("riscv64"),
        _ => machine_named("aarch64"),
    };
    let start = Start::Program(Entry { symbol: "__F1t4main".to_string(), answers: true });
    let why = link("", &start, elsewhere, Path::new("/dev/null"), None)
        .expect_err("linking for another machine should be refused");
    assert!(why.contains("cannot link for"), "{}", why);
    assert!(why.contains("--emit asm"), "{}", why);
}

// A runtime named that is not there is said plainly, rather than left to the
// linker to complain about a file it was handed.
#[test]
fn a_runtime_that_is_not_there_is_said_so() {
    let start = Start::Program(Entry { symbol: "__F1t4main".to_string(), answers: true });
    let why = link(
        "",
        &start,
        machine_named(here()),
        Path::new("/dev/null"),
        Some(Path::new("/nowhere/libfortec_rt.a")),
    )
    .expect_err("a missing archive should be refused");
    assert!(why.contains("no runtime archive at"), "{}", why);
}


// ---- The runner --------------------------------------------------------------

// Every test is declared and every test is called, and the collector's roots
// are noted before any of them runs.
#[test]
fn the_runner_declares_and_calls_every_test() {
    let out = runner(&["a::one", "b::two"]);
    assert!(out.contains("extern void __F1t6a::one(void);"), "{}", out);
    assert!(out.contains("__F1t6a::one();"), "{}", out);
    assert!(out.contains("__F1t6b::two();"), "{}", out);
    assert!(out.find("__rt_init();").unwrap() < out.find("__F1t6a::one();").unwrap(), "{}", out);
}

// The name goes out before the test runs and the stream is flushed, so that a
// test which takes the process down leaves its own name as the last thing
// written. A name printed afterwards would name every test but that one.
#[test]
fn a_name_is_written_and_flushed_before_the_test_it_names() {
    let out = runner(&["m::dies"]);
    let said = out.find("test m::dies ...").expect("the name");
    let flushed = out.find("fflush(stdout);").expect("the flush");
    let called = out.find("__F1t7m::dies();").expect("the call");
    assert!(said < flushed && flushed < called, "{}", out);
}

// The verdict is read from the runtime after the body has returned, an
// assertion that fails having counted itself rather than stopped the test.
#[test]
fn every_test_is_cleared_before_it_runs_and_read_after() {
    let out = runner(&["m::one"]);
    let start = out.find("__rt_test_start();").expect("the clearing");
    let called = out.find("__F1t6m::one();").expect("the call");
    let read = out.find("__rt_test_failed()").expect("the reading");
    assert!(start < called && called < read, "{}", out);
    assert!(out.contains("extern void __rt_test_start(void);"), "{}", out);
    assert!(out.contains("extern long __rt_test_failed(void);"), "{}", out);
}

// Whatever ran the tests is not reading the words, so the verdict is a status
// as well as a line.
#[test]
fn a_suite_that_failed_says_so_in_the_status() {
    let out = runner(&["m::one"]);
    assert!(out.contains("return failed ? 1 : 0;"), "{}", out);
    assert!(out.contains(r#"failed ? "FAILED" : "ok""#), "{}", out);
}

// A test with nothing to say still counts, and the count reads as English on
// both sides of one.
#[test]
fn the_count_agrees_with_how_many_there_are() {
    assert!(runner(&["a::x"]).contains("running 1 test\\n"), "{}", runner(&["a::x"]));
    assert!(runner(&["a::x", "a::y"]).contains("running 2 tests\\n"));
    // A suite with none of them is a runner that says so rather than a runner
    // that will not compile.
    let none = runner(&[]);
    assert!(none.contains("running 0 tests"), "{}", none);
    assert!(none.contains("int main(void)"), "{}", none);
}

// A name is a Forte path and has nothing in it to escape -- and is escaped
// anyway, that being a fact about the mangler rather than a promise the shim
// should rest on.
#[test]
fn a_name_that_would_end_the_literal_is_escaped() {
    let held = vec![Test { name: "a\"b\\c".to_string(), symbol: "__F1t1x".to_string() }];
    let out = shim(&Start::Tests(held));
    assert!(out.contains(r#"test a\"b\\c ..."#), "{}", out);
}
