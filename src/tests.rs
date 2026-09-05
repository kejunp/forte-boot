// The compiler run over Forte, rather than over a tree built to look like it.
//
// Everything else in this crate tests a pass against what the pass before it
// would have handed over. This tests the whole of it against what a program
// actually does: `std/tests.ft` is written in the language, compiled by the
// driver in this file, linked against the runtime beside it, and run -- and
// what it asserts about `Vec`, the two maps and the two sets is asserted by
// code that had to compile correctly for the assertion to mean anything.
//
// So it fails for two quite different reasons, and that is the point of it. A
// wrong answer out of `hashmap.ft` fails it, and so does a back end that
// emitted the wrong instruction for the loop that walks the table. The second
// is the one no test written in Rust in this crate can reach.
//
// **It skips itself where the tools are not there.** `mir::asm`'s tests give
// the reason and it is the same one: a suite that cannot run on a machine
// without a C toolchain is a suite nobody runs. What is wanted here is a `cc`
// and the runtime archive, and neither is this file's to build.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::{compile, sir};

// Where the sources are. Worked out while this is compiled, there being no
// other way to find the tree from a test binary that `cargo` may have put
// anywhere.
fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

// The runtime archive, which `cargo` writes beside the test binary's own
// directory rather than in it: a test runs from `target/<profile>/deps` and the
// archive is one above.
//
// `None` is not a failure. It is a tree nobody has built the runtime in, and
// what the test does about that is not run.
fn archive() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let mut at = exe.parent()?;
    for _ in 0..3 {
        let held = at.join("libfortec_rt.a");
        if held.is_file() {
            return Some(held);
        }
        at = at.parent()?;
    }
    None
}

// Whether there is a C compiler to assemble and link with.
fn have_cc() -> bool {
    Command::new("cc").arg("--version").output().is_ok_and(|held| held.status.success())
}

// Somewhere to put an executable that two of these must not share.
fn out_at(what: &str) -> PathBuf {
    std::env::temp_dir().join(format!("fortec-{}-{}", what, std::process::id()))
}

// Compiles a suite as `--test` does and runs what comes out. `None` where the
// tools to do that are not here.
//
// The runtime is named rather than found, for the reason `archive` gives, and
// the standard library is named rather than found, because `std_beside` looks
// beside the compiler and the compiler here is a test binary.
fn ran(root: &Path, what: &str) -> Option<(bool, String)> {
    let (Some(runtime), true) = (archive(), have_cc()) else { return None };
    let at = out_at(what);
    let _ = std::fs::remove_file(&at);

    let built = compile(
        root,
        vec![repo().join("std")],
        sir::opt::Level::default(),
        sir::target::Target::default(),
        None,
        Some(at.clone()),
        Some(runtime),
        true,
    );
    assert!(built, "{} was meant to compile", root.display());

    let held = Command::new(&at).output().expect("the tests to run");
    let _ = std::fs::remove_file(&at);
    let mut text = String::from_utf8_lossy(&held.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&held.stderr));
    Some((held.status.success(), text))
}

// ---- The standard library ----------------------------------------------------

// Every `%test` in `std/tests.ft`, run.
//
// The count is asserted to be more than none rather than to be a number: the
// number is whatever somebody has got round to writing, and a test that had to
// be edited every time one was added is a test that would be edited without
// being read.
#[test]
fn the_standard_library_passes_its_own_tests() {
    let Some((ok, said)) = ran(&repo().join("std/tests.ft"), "std-tests") else {
        return;
    };
    assert!(said.contains("0 failed"), "{}", said);
    assert!(!said.contains("running 0 tests"), "nothing ran:\n{}", said);
    assert!(ok, "the standard library's own tests did not pass:\n{}", said);
}

// ---- Arguments past the registers ----------------------------------------------

// A call with more arguments than the machine has registers for.
//
// The one-hot cases are the point of it. A test that only summed nine ones
// would pass on a compiler that handed the same argument over twice, or dropped
// one and read a leftover that happened to be right; asking what the seventh
// alone comes to says *which slot each argument arrived in*, which is the whole
// of what the stack-argument path has to get right.
//
// It runs on this machine only. What the other two back ends emit is checked by
// an assembler in `mir::asm`'s tests and not by running it, so a wrong offset
// there is caught as an instruction that will not encode and not as a wrong
// answer.
#[test]
fn every_argument_past_the_registers_arrives_where_it_was_put() {
    let dir = std::env::temp_dir().join(format!("fortec-many-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("many.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         import fmt::{int, float};\n\
         \n\
         %noinline\n\
         fn nine(a: i64, b: i64, c: i64, d: i64, e: i64,\n\
         \x20       f: i64, g: i64, h: i64, i: i64): i64 {\n\
         \x20   a + b*2 + c*3 + d*4 + e*5 + f*6 + g*7 + h*8 + i*9\n\
         }\n\
         \n\
         %noinline\n\
         fn ten(a: f64, b: f64, c: f64, d: f64, e: f64,\n\
         \x20      f: f64, g: f64, h: f64, i: f64, j: f64): f64 {\n\
         \x20   a + b + c + d + e + f + g + h + i + j*10.0\n\
         }\n\
         \n\
         struct P {\n    pub x: i64,\n    pub y: i64,\n}\n\
         \n\
         %noinline\n\
         fn six(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64): P {\n\
         \x20   P { x: a + b + c, y: d + e + f }\n\
         }\n\
         \n\
         %test\n\
         fn every_one_of_them_arrives_where_it_was_put() {\n\
         \x20   assert_eq(int(nine(1,1,1,1,1,1,1,1,1)), int(45), \"all nine\")\n\
         \x20   assert_eq(int(nine(0,0,0,0,0,1,0,0,0)), int(6), \"the last in a register\")\n\
         \x20   assert_eq(int(nine(0,0,0,0,0,0,1,0,0)), int(7), \"the first on the stack\")\n\
         \x20   assert_eq(int(nine(0,0,0,0,0,0,0,0,1)), int(9), \"the last on the stack\")\n\
         }\n\
         \n\
         %test\n\
         fn the_two_files_run_out_of_registers_apart() {\n\
         \x20   assert_eq(float(ten(0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0)), float(10.0),\n\
         \x20             \"the tenth float\")\n\
         }\n\
         \n\
         // Six written arguments and seven handed over: the room for the answer\n\
         // takes a register of its own, so this overflows before it looks like it.\n\
         %test\n\
         fn a_struct_handed_back_takes_a_register_too() {\n\
         \x20   let p = six(1, 2, 3, 4, 5, 6)\n\
         \x20   assert_eq(int(p.x), int(6), \"the first three\")\n\
         \x20   assert_eq(int(p.y), int(15), \"and the last three\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "many");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a call past the registers was meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- The runner itself -------------------------------------------------------

// And that it would have said so. A suite whose tests all pass says nothing
// about a runner that cannot tell -- one that reported `ok` whatever happened
// would pass the test above, and this is what stops it.
#[test]
fn a_test_that_fails_is_reported_and_leaves_a_status_behind() {
    // Not the name `out_at` gives the executable, which would be this
    // directory and would be linked over.
    let dir = std::env::temp_dir().join(format!("fortec-failing-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("failing.ft");
    std::fs::write(
        &root,
        "import test::{assert, assert_eq};\n\
         import fmt::int;\n\
         \n\
         %test\n\
         fn this_one_holds() {\n\
         \x20   assert(true, \"true is true\")\n\
         }\n\
         \n\
         %test\n\
         fn this_one_does_not() {\n\
         \x20   assert_eq(int(1), int(2), \"one is two\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "failing");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(!ok, "a suite with a failing test was meant to exit non-zero:\n{}", said);
    assert!(said.contains("1 passed; 1 failed"), "{}", said);
    assert!(said.contains("this_one_does_not ..."), "{}", said);
    // What the two sides were, which is the whole reason `assert_eq` is worth
    // having over `assert(a == b)`.
    assert!(said.contains("one is two"), "{}", said);
    assert!(said.contains("left: 1"), "{}", said);
    assert!(said.contains("right: 2"), "{}", said);
}
