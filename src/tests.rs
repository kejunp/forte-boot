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
//
// The name is the caller's word and the pid, so two of these running at once in
// one test binary are told apart by the word alone -- and two tests that pick
// the same word are one file written twice and one directory each deletes at
// the end of itself. What that looks like is a test that fails once in four
// runs saying the program it just built is not there, which is what it did.
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
    built(root, what, true)
}

// And the same for an ordinary build, which starts at the suite's own `main`
// rather than at a runner over its tests. What a program *does* is the only way
// to ask some things -- whether a `never` really does stop one, above all.
fn ran_program(root: &Path, what: &str) -> Option<(bool, String)> {
    built(root, what, false)
}

// And the same for an ordinary build handed arguments and an environment,
// which is the one thing a `%test` cannot ask about: a test runner's shim
// hands over none, so what a program does with what it was started with has to
// be asked of a program that was started.
fn ran_with(
    root: &Path,
    what: &str,
    args: &[&str],
    env: &[(&str, &str)],
) -> Option<(bool, String)> {
    with(root, what, false, args, env)
}

fn built(root: &Path, what: &str, tests: bool) -> Option<(bool, String)> {
    with(root, what, tests, &[], &[])
}

fn with(
    root: &Path,
    what: &str,
    tests: bool,
    args: &[&str],
    env: &[(&str, &str)],
) -> Option<(bool, String)> {
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
        tests,
    );
    assert!(built, "{} was meant to compile", root.display());

    let mut held = Command::new(&at);
    held.args(args);
    for (name, value) in env {
        held.env(name, value);
    }
    let held = held.output().expect("the tests to run");
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
         \n\
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
         \x20   assert_eq(&nine(1,1,1,1,1,1,1,1,1), &45, \"all nine\")\n\
         \x20   assert_eq(&nine(0,0,0,0,0,1,0,0,0), &6, \"the last in a register\")\n\
         \x20   assert_eq(&nine(0,0,0,0,0,0,1,0,0), &7, \"the first on the stack\")\n\
         \x20   assert_eq(&nine(0,0,0,0,0,0,0,0,1), &9, \"the last on the stack\")\n\
         }\n\
         \n\
         %test\n\
         fn the_two_files_run_out_of_registers_apart() {\n\
         \x20   assert_eq(&ten(0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0), &10.0,\n\
         \x20             \"the tenth float\")\n\
         }\n\
         \n\
         // Six written arguments and seven handed over: the room for the answer\n\
         // takes a register of its own, so this overflows before it looks like it.\n\
         %test\n\
         fn a_struct_handed_back_takes_a_register_too() {\n\
         \x20   let p = six(1, 2, 3, 4, 5, 6)\n\
         \x20   assert_eq(&p.x, &6, \"the first three\")\n\
         \x20   assert_eq(&p.y, &15, \"and the last three\")\n\
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

// ---- Slices --------------------------------------------------------------------

// A slice, read and written, and the elements outside it left alone.
//
// The values are the point. A view is two words -- where the elements begin
// and how many there are -- so a slice that took the address without the length
// reads whatever is next in the frame as its length, and one that forgot to
// scale the start by the stride reads the right array from the wrong place.
// Both compile, link and run; only the answers tell them apart.
#[test]
fn a_slice_is_a_view_of_the_elements_it_names() {
    let dir = std::env::temp_dir().join(format!("fortec-slice-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("slice.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         fn sum(xs: &i64[], n: i64): i64 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n {\n\
         \x20       t = t + xs[i]\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   t\n\
         }\n\
         \n\
         fn bump(xs: *i64[], n: i64) {\n\
         \x20   var i = 0\n\
         \x20   while i < n {\n\
         \x20       xs[i] = xs[i] + 100\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn a_slice_reads_the_elements_it_names_and_no_others() {\n\
         \x20   let a: i64[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   assert_eq(&sum(&a[1..4], 3), &9, \"2 and 3 and 4\")\n\
         \x20   assert_eq(&sum(&a[0..8], 8), &36, \"the whole of it\")\n\
         \x20   assert_eq(&sum(&a[7..8], 1), &8, \"the last one alone\")\n\
         }\n\
         \n\
         %test\n\
         fn a_slice_that_writes_leaves_the_rest_alone() {\n\
         \x20   var a: i64[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   bump(*a[2..4], 2)\n\
         \x20   assert_eq(&a[2], &103, \"the first it names\")\n\
         \x20   assert_eq(&a[3], &104, \"and the last\")\n\
         \x20   assert_eq(&a[1], &2, \"the one before is untouched\")\n\
         \x20   assert_eq(&a[4], &5, \"and the one after\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "slice");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "slices were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}

// ---- A reference to an array is a view of it ------------------------------------

// "The length moving out of the type and into the value" (§3), which is the
// half only a running program can check: a conversion that took the address and
// left the length behind still compiles, links, and reads whatever was next in
// the frame as how many there are.
#[test]
fn a_reference_to_an_array_carries_the_length_it_left_behind() {
    let dir = std::env::temp_dir().join(format!("fortec-view-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("view.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         fn sum(xs: &i64[], n: i64): i64 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n {\n\
         \x20       t = t + xs[i]\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   t\n\
         }\n\
         \n\
         fn bump(xs: *i64[], n: i64) {\n\
         \x20   var i = 0\n\
         \x20   while i < n {\n\
         \x20       xs[i] = xs[i] + 1\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn an_array_stands_where_a_view_is_wanted() {\n\
         \x20   let a: i64[4] = [10, 20, 30, 40]\n\
         \x20   let s: &i64[] = &a\n\
         \x20   assert_eq(&sum(s, 4), &100, \"through a name that says so\")\n\
         \x20   assert_eq(&sum(&a, 4), &100, \"and at a parameter that does\")\n\
         }\n\
         \n\
         %test\n\
         fn a_writing_reference_to_an_array_writes_through_the_view() {\n\
         \x20   var a: i64[4] = [10, 20, 30, 40]\n\
         \x20   bump(*a, 4)\n\
         \x20   assert_eq(&a[0], &11, \"the first\")\n\
         \x20   assert_eq(&a[3], &41, \"and the last\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "view");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a reference to an array was meant to be a view:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}

// ---- Stopping ---------------------------------------------------------------------

// A program that finds it cannot go on, and stops.
//
// §8 named this as the gap and said an external `exit` was "not an answer for
// this one", so what is checked is the whole of the answer: the words reach the
// error stream, the status is not nought, and *nothing after the call runs* --
// which is the part a `never` return type promises and the only part a reader
// cannot see for themselves.
#[test]
fn a_program_that_cannot_go_on_says_so_and_stops() {
    let dir = std::env::temp_dir().join(format!("fortec-stop-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("stop.ft");
    std::fs::write(
        &root,
        "import panic::panic;\n\
         import fmt::println;\n\
         \n\
         fn checked(n: i64): i64 {\n\
         \x20   if n < 0 {\n\
         \x20       panic(\"a length cannot be negative\")\n\
         \x20   }\n\
         \x20   n * 2\n\
         }\n\
         \n\
         fn main(): i32 {\n\
         \x20   println(\"BEFORE\", &[])\n\
         \x20   let held = checked(-1)\n\
         \x20   println(\"AFTER\", &[])\n\
         \x20   held as i32\n\
         }\n",
    )
    .expect("a file");

    let held = ran_program(&root, "stop");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(!ok, "a program that panicked was meant to exit non-zero:\n{}", said);
    assert!(said.contains("BEFORE"), "what ran before it should still be there:\n{}", said);
    assert!(!said.contains("AFTER"), "nothing after a `never` may run:\n{}", said);
    assert!(said.contains("a length cannot be negative"), "{}", said);
}

// ---- Dispatch through a bound ---------------------------------------------------

// A method called through a trait bound, and the generic it is called in made
// once per type it is used with.
//
// Two types answering one trait is the whole of it. A test with one impl passes
// on a compiler that ignores the receiver entirely and calls whatever it found
// first -- and one did: `share` merged the two `Item` values that named the
// generic, because a generic names its declaration and nothing about what it
// stands for, so both calls ran the second instance and neither the assembler
// nor the linker had anything to say.
#[test]
fn a_method_reached_through_a_bound_runs_the_impl_of_the_type_it_was_given() {
    let dir = std::env::temp_dir().join(format!("fortec-bound-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("bound.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         trait Show {\n\
         \x20   fn show(&self): i64\n\
         \x20   fn scaled(&self, by: i64): i64\n\
         }\n\
         \n\
         struct P { pub x: i64 }\n\
         struct Q { pub y: i64 }\n\
         \n\
         impl Show for P {\n\
         \x20   fn show(&self): i64 { self.x * 2 }\n\
         \x20   fn scaled(&self, by: i64): i64 { self.x * by }\n\
         }\n\
         \n\
         impl Show for Q {\n\
         \x20   fn show(&self): i64 { self.y + 100 }\n\
         \x20   fn scaled(&self, by: i64): i64 { self.y + by }\n\
         }\n\
         \n\
         fn twice<T: Show>(v: &T): i64 { v.show() }\n\
         \n\
         // A generic handing its own parameter on to another bounded generic.\n\
         fn through<T: Show>(v: &T): i64 { twice(v) + v.scaled(10) }\n\
         \n\
         %test\n\
         fn a_bound_dispatches_to_the_impl_of_the_receiver() {\n\
         \x20   let p = P { x: 21 }\n\
         \x20   let q = Q { y: 5 }\n\
         \x20   assert_eq(&twice(&p), &42, \"P answers Show\")\n\
         \x20   assert_eq(&twice(&q), &105, \"and so does Q, differently\")\n\
         }\n\
         \n\
         %test\n\
         fn a_generic_may_hand_its_own_parameter_on() {\n\
         \x20   let p = P { x: 21 }\n\
         \x20   let q = Q { y: 5 }\n\
         \x20   assert_eq(&through(&p), &252, \"42 and 21 by ten\")\n\
         \x20   assert_eq(&through(&q), &120, \"105 and 5 and ten\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "bound");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a method through a bound was meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
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
         \n\
         \n\
         %test\n\
         fn this_one_holds() {\n\
         \x20   assert(true, \"true is true\")\n\
         }\n\
         \n\
         %test\n\
         fn this_one_does_not() {\n\
         \x20   assert_eq(&1, &2, \"one is two\")\n\
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

// ---- Closures ------------------------------------------------------------------

// What a closure comes to when it runs, which is the half nothing in this crate
// could reach before this file existed.
//
// Every one of these compiled and linked while the compiler was wrong about it.
// A closure's body was lowered with no parameters at all -- the caller put the
// arguments in the registers the ABI names and the body read the registers an
// allocator happened to pick -- so `add(2, 3)` gave back a word of whatever the
// frame held last. The tests that existed were the checker's, and a closure
// that type checks is exactly what this one was.
//
// So the assertions are on *values* and not on shapes. Each of the five asks
// something a wrong lowering answers differently:
//
//   - the parameters arrive, and in the order they were written. `a - b` and
//     not `a + b`, because two arguments swapped is the failure a sum hides.
//   - a capture is read through the environment. A closure with captures takes
//     one parameter more than it declares, and the run it points at is built
//     where the closure is made.
//   - a capture is *written* through it: "assigning to one takes a `*`" (§5),
//     so what the closure did is what the frame outside holds afterwards. That
//     one also asks a question of `sir::alias` -- the store before the call and
//     the read after it are a store and a load of one slot, and the pass has to
//     know the call between them writes it.
//   - a `move` closure outlives the frame it took from. The value is copied
//     into room of the collector's, so what it reads is not a word of a frame
//     that has since been used for something else.
//   - a declared fn and a closure go down one call. Both are a fn value, the
//     environment is the last argument either way, and the one with nothing to
//     find in it never looks.
//   - a body written in braces is a block. That one is the lexer's (§7) and
//     not the lowering's, and it is here rather than only in `lex` because
//     what a block *yields* is the other half of it: the value of the closure
//     is the tail of the block and not the last thing that happened in it.
#[test]
fn a_closure_runs_as_what_it_was_written_as() {
    let dir = std::env::temp_dir().join(format!("fortec-closure-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("closure.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         fn twice(f: fn(i64): i64, x: i64): i64 {\n\
         \x20   f(f(x))\n\
         }\n\
         \n\
         fn ten(x: i64): i64 {\n\
         \x20   x + 10\n\
         }\n\
         \n\
         fn made(): fn(i64): i64 {\n\
         \x20   let base = 100\n\
         \x20   move |x: i64| x + &base\n\
         }\n\
         \n\
         fn churn(a: i64, b: i64, c: i64): i64 {\n\
         \x20   a * 7777 + b * 8888 + c * 9999\n\
         }\n\
         \n\
         %test\n\
         fn the_arguments_arrive_in_the_order_they_were_written() {\n\
         \x20   let less = |a: i64, b: i64| a - b\n\
         \x20   assert_eq(&less(9, 4), &5, \"the first less the second\")\n\
         \x20   let seven = |p1: i64, p2: i64, p3: i64, p4: i64, p5: i64, p6: i64, p7: i64| \
         p7 - p1\n\
         \x20   assert_eq(&seven(1, 0, 0, 0, 0, 0, 8), &7, \"past the registers\")\n\
         }\n\
         \n\
         %test\n\
         fn a_capture_is_read_through_the_environment() {\n\
         \x20   let n = 5\n\
         \x20   let add = |x: i64| x + &n\n\
         \x20   assert_eq(&add(1), &6, \"what the frame outside holds\")\n\
         \x20   assert_eq(&add(2), &7, \"and it is still there\")\n\
         }\n\
         \n\
         %test\n\
         fn a_capture_that_is_assigned_to_is_written_through() {\n\
         \x20   var n = 0\n\
         \x20   let bump = |d: i64| n = n + d\n\
         \x20   bump(3)\n\
         \x20   bump(4)\n\
         \x20   assert_eq(&n, &7, \"the name outside, not a copy of it\")\n\
         }\n\
         \n\
         %test\n\
         fn a_move_closure_outlives_the_frame_it_took_from() {\n\
         \x20   let f = made()\n\
         \x20   assert_eq(&churn(1, 2, 3), &55550, \"something else uses the stack\")\n\
         \x20   assert_eq(&f(1), &101, \"and what it took is still what it took\")\n\
         }\n\
         \n\
         %test\n\
         fn a_declared_fn_and_a_closure_are_called_the_same_way() {\n\
         \x20   assert_eq(&twice(ten, 1), &21, \"a fn with no environment\")\n\
         \x20   let k = 10\n\
         \x20   assert_eq(&twice(|x: i64| x + &k, 1), &21, \"and one with\")\n\
         }\n\
         \n\
         %test\n\
         fn a_body_in_braces_is_a_block() {\n\
         \x20   var n = 1\n\
         \x20   let step = |d: i64| { n = n * d }\n\
         \x20   step(6)\n\
         \x20   assert_eq(&n, &6, \"one statement, and it ran\")\n\
         \x20   let twice_over = |x: i64| {\n\
         \x20       let a = x * 2\n\
         \x20       a + 1\n\
         \x20   }\n\
         \x20   assert_eq(&twice_over(5), &11, \"and its value is the tail\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "closure");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "closures were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 6 tests"), "{}", said);
}

// ---- An impl's own parameters ----------------------------------------------------

// A generic impl, run.
//
// The half `sema`'s tests cannot reach is `mir::mono`: an impl's parameters are
// answered by the *receiver* and by nothing else -- a method call writes no type
// arguments, there being nowhere to write them -- so what makes `Box<i32>` and
// `Box<bool>` two bodies is a match of the receiver's type against the one the
// declaration wrote. Getting that wrong compiles: what comes out is a call to a
// symbol with the parameters still written into its name, and the failure is a
// linker's rather than a compiler's, or two instances collapsed into one and a
// `bool` read as an `i64`.
//
// So the assertions are on values from two instances at once, and on a method
// that reaches its own impl's parameter through a bound.
#[test]
fn a_generic_impl_is_made_once_for_each_receiver() {
    let dir = std::env::temp_dir().join(format!("fortec-impl-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("impls.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         struct Box<T> {\n\
         \x20   pub v: T,\n\
         }\n\
         \n\
         impl<T> Box<T> {\n\
         \x20   fn get(&self): T { self.v }\n\
         \x20   // One member of the impl reaching another, which is the call\n\
         \x20   // whose arguments come from the body it stands in.\n\
         \x20   fn again(&self): T { self.get() }\n\
         }\n\
         \n\
         struct Pair<A, B> {\n\
         \x20   pub a: A,\n\
         \x20   pub b: B,\n\
         }\n\
         \n\
         impl<A, B> Pair<A, B> {\n\
         \x20   // `B` appears in neither the answer nor an argument, so it is\n\
         \x20   // recovered from the receiver or from nowhere.\n\
         \x20   fn first(&self): A { self.a }\n\
         }\n\
         \n\
         struct Counter {\n\
         \x20   pub n: i64,\n\
         }\n\
         \n\
         impl Counter {\n\
         \x20   fn bump(*self, by: i64) { self.n = self.n + by }\n\
         \x20   fn read(&self): i64 { self.n }\n\
         }\n\
         \n\
         fn through<T>(b: &Box<T>): T { b.get() }\n\
         \n\
         %test\n\
         fn one_impl_answers_two_receivers() {\n\
         \x20   let n: Box<i64> = Box { v: 7 }\n\
         \x20   let t: Box<bool> = Box { v: true }\n\
         \x20   assert_eq(&n.get(), &7, \"the i64 instance\")\n\
         \x20   assert_eq(&t.get(), &true, \"and the bool one\")\n\
         \x20   assert_eq(&n.again(), &7, \"one member reaching another\")\n\
         }\n\
         \n\
         %test\n\
         fn a_parameter_only_the_receiver_names_is_still_found() {\n\
         \x20   let p: Pair<i64, bool> = Pair { a: 3, b: false }\n\
         \x20   assert_eq(&p.first(), &3, \"and `B` came from the receiver\")\n\
         }\n\
         \n\
         %test\n\
         fn an_impls_parameter_reaches_through_a_generic_fn() {\n\
         \x20   let n: Box<i64> = Box { v: 41 }\n\
         \x20   assert_eq(&through(&n), &41, \"a `T` handed on to a method\")\n\
         }\n\
         \n\
         %test\n\
         fn an_impl_with_no_parameters_still_works() {\n\
         \x20   var c = Counter { n: 0 }\n\
         \x20   c.bump(5)\n\
         \x20   c.bump(2)\n\
         \x20   assert_eq(&c.read(), &7, \"a `*self` that wrote through\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "impls");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "generic impls were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- An `unsafe` in front of the last thing in a body ----------------------------

// A guarded read as a fn's answer, which is the shape every container that
// manages its own room wants: `fn elem(&self, i: i64): T { unsafe self.at[i] }`.
//
// It compiled before and gave back nought. The word made a statement of what it
// prefixed, so the block had no tail and yielded `null` -- and `null` "belongs
// to every type" (§3), so the signature agreed with it and nothing was said. A
// wrong answer with no diagnostic is the worst of the three ways this could
// have gone, which is why it is asserted here on values rather than on a tree.
//
// The four shapes are the four an `unsafe` tail can have: a read through a
// pointer, a `deref`, a block, and a declaration -- the last of which is not a
// value however it is written, so the word has nothing to guard and the fn
// answers `null` as it always did.
#[test]
fn an_unsafe_tail_is_the_value_of_the_body_it_ends() {
    let dir = std::env::temp_dir().join(format!("fortec-unsafe-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("guard.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         import mem::room;\n\
         \n\
         fn indexed(p: ptr i64): i64 { unsafe p[0] }\n\
         fn dereffed(p: ptr i64): i64 { unsafe deref p }\n\
         fn blocked(p: ptr i64): i64 { unsafe { p[0] } }\n\
         // Twice over, to say the word nests the way the grammar has it:\n\
         // `<unterminated_stmt>` takes another one after the word.\n\
         fn twice(p: ptr i64): i64 { unsafe unsafe p[0] }\n\
         \n\
         %test\n\
         fn a_guarded_read_is_what_the_fn_answers() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 9\n\
         \x20   assert_eq(&indexed(p), &9, \"through an index\")\n\
         \x20   assert_eq(&dereffed(p), &9, \"through a `deref`\")\n\
         \x20   assert_eq(&blocked(p), &9, \"through a block\")\n\
         \x20   assert_eq(&twice(p), &9, \"and through the word twice\")\n\
         }\n\
         \n\
         %test\n\
         fn a_guarded_write_still_happens() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 1\n\
         \x20   unsafe p[0] = 2\n\
         \x20   assert_eq(&indexed(p), &2, \"the last write is what is there\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "guard");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a guarded tail was meant to be a value:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}

// ---- What stands between two reads of one place ----------------------------------

// An element read, with something that writes it standing in between.
//
// `p[i]` is the one read in the SIR that does not name the address it reads:
// it is a `SIRInstKind::Index`, and `sir::opt` had it in the list of
// instructions that "make the same value from the same operands". That list is
// for arithmetic. Two reads of one place are two answers whenever anything
// wrote between them, and three passes were getting it wrong in three ways --
// `share` called the second read the first, `overwritten` dropped a store an
// `Index` was reading, and `hoist` would lift one out of a loop that wrote it.
//
// None of it showed below `-O2`, and none of it is visible in a tree: what
// comes out is a program that links and answers with a value from before the
// write. So every one of these is a value asserted after something wrote, and
// the suite is built at the default level, which is where the passes run.
//
// The last one is here to say the fix did not simply turn the sharing off:
// three reads of one place with nothing between them still come to one, by the
// pass that knows what stands between two reads rather than the one that does
// not.
#[test]
fn a_read_of_a_place_is_not_the_read_before_the_write() {
    let dir = std::env::temp_dir().join(format!("fortec-alias-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("alias.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         import mem::room;\n\
         \n\
         fn read(p: ptr i64): i64 { unsafe p[0] }\n\
         fn poke(p: ptr i64) { unsafe p[0] = 6 }\n\
         \n\
         %test\n\
         fn a_call_between_two_reads_is_a_call_that_may_write() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 1\n\
         \x20   let before = read(p)\n\
         \x20   poke(p)\n\
         \x20   let after = read(p)\n\
         \x20   assert_eq(&before, &1, \"what was there\")\n\
         \x20   assert_eq(&after, &6, \"and what the call put there\")\n\
         }\n\
         \n\
         %test\n\
         fn a_read_keeps_the_store_it_reads_alive() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 1\n\
         \x20   unsafe let v = p[0]\n\
         \x20   unsafe p[0] = 2\n\
         \x20   assert_eq(&v, &1, \"the store under the read did happen\")\n\
         }\n\
         \n\
         %test\n\
         fn a_read_a_loop_writes_stays_in_the_loop() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 5\n\
         \x20   var total = 0\n\
         \x20   var i = 0\n\
         \x20   while i < 3 {\n\
         \x20       unsafe let v = p[0]\n\
         \x20       total = total + v\n\
         \x20       unsafe p[0] = v + 1\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   assert_eq(&total, &18, \"5 and 6 and 7\")\n\
         }\n\
         \n\
         %test\n\
         fn two_elements_are_two_places_and_one_is_one() {\n\
         \x20   unsafe let p = room(32) as ptr i64\n\
         \x20   unsafe p[0] = 3\n\
         \x20   unsafe p[1] = 4\n\
         \x20   unsafe let apart = p[0] + p[1]\n\
         \x20   assert_eq(&apart, &7, \"two places, two values\")\n\
         \x20   unsafe let same = p[0] + p[0] + p[0]\n\
         \x20   assert_eq(&same, &9, \"and one place read three times\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "alias");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a read after a write was meant to see it:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- A field and a method of one name ---------------------------------------------

// The shape every container has: a field called `len` and a `len()` beside it.
//
// A field of the same name used to win outright, so the method was unreachable
// and what came out was "`i64` is not a fn" -- a message about a name the
// reader was not talking about, with nothing offered to write instead. The rule
// is narrower now: the field wins where it could be the thing called, and where
// it could not, the method answers.
//
// Run rather than checked, because both readings have to still *work*. It is
// easy to make the method reachable and the field not, and a tree says the call
// resolved somewhere without saying it resolved to the right one -- so the
// assertions are on two values that differ, `len` being four and `len()` being
// forty.
#[test]
fn a_field_and_a_method_of_one_name_are_both_reachable() {
    let dir = std::env::temp_dir().join(format!("fortec-named-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("named.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         struct Buf {\n\
         \x20   pub len: i64,\n\
         }\n\
         \n\
         impl Buf {\n\
         \x20   fn len(&self): i64 { self.len * 10 }\n\
         }\n\
         \n\
         struct Held {\n\
         \x20   pub run: fn(i64): i64,\n\
         }\n\
         \n\
         impl Held {\n\
         \x20   // Unreachable, and that is the rule: a callable field is what\n\
         \x20   // `h.run(..)` meant, and it wins as it always did.\n\
         \x20   fn run(&self): i64 { 99 }\n\
         }\n\
         \n\
         %test\n\
         fn a_field_that_is_not_a_fn_does_not_hide_the_method() {\n\
         \x20   let b = Buf { len: 4 }\n\
         \x20   assert_eq(&b.len, &4, \"the field, read\")\n\
         \x20   assert_eq(&b.len(), &40, \"and the method, called\")\n\
         }\n\
         \n\
         %test\n\
         fn a_field_that_is_a_fn_still_wins() {\n\
         \x20   let h = Held { run: |x: i64| x * 2 }\n\
         \x20   assert_eq(&h.run(21), &42, \"the field and not the method\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "named");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a field and a method of one name were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}

// ---- A call that reaches a different body every time it runs ----------------------

// Dynamic dispatch, run.
//
// Nothing about this can be checked in a tree. What a `&dyn Shape` *is* is two
// words -- where the value is, and where the routines that answer for it are --
// and what a call through one does is read the second, step to the member's
// place in it, and call what is there. Getting the place wrong calls the wrong
// member of the right type; getting the order wrong in the table calls the
// right member of the wrong one; and both compile, link and run.
//
// So the two members answer differently in a way that says which was reached:
// `area` differs per type and `sides` differs between the square and the
// triangle, and one number carries both. One body of `describe` does all three,
// which is the whole of what makes it dynamic -- a static call would want three.
//
// The generic impl is here because a table's entries have to be the *instance*
// symbols: `impl<T> Shape for Box<T>` answers with a body that does not exist
// until something says what `T` is, and the thing that says it is the coercion.
#[test]
fn a_call_through_a_trait_object_reaches_the_type_it_was_made_from() {
    let dir = std::env::temp_dir().join(format!("fortec-dyn-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("dyn.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         trait Shape {\n\
         \x20   fn area(&self): i64\n\
         \x20   fn sides(&self): i64\n\
         }\n\
         \n\
         struct Sq { pub s: i64 }\n\
         struct Rect { pub w: i64, pub h: i64 }\n\
         struct Tri { pub b: i64, pub h: i64 }\n\
         struct Box<T> { pub v: T }\n\
         \n\
         impl Shape for Sq {\n\
         \x20   fn area(&self): i64 { self.s * self.s }\n\
         \x20   fn sides(&self): i64 { 4 }\n\
         }\n\
         impl Shape for Rect {\n\
         \x20   fn area(&self): i64 { self.w * self.h }\n\
         \x20   fn sides(&self): i64 { 4 }\n\
         }\n\
         impl Shape for Tri {\n\
         \x20   fn area(&self): i64 { self.b * self.h / 2 }\n\
         \x20   fn sides(&self): i64 { 3 }\n\
         }\n\
         impl<T> Shape for Box<T> {\n\
         \x20   fn area(&self): i64 { 11 }\n\
         \x20   fn sides(&self): i64 { 1 }\n\
         }\n\
         \n\
         // One body, and the only thing that tells the three apart is the\n\
         // table each of them arrived with.\n\
         fn described(s: &dyn Shape): i64 { s.area() * 100 + s.sides() }\n\
         \n\
         %test\n\
         fn one_body_answers_for_every_type_that_answers_the_trait() {\n\
         \x20   let a = Sq { s: 5 }\n\
         \x20   let b = Rect { w: 3, h: 7 }\n\
         \x20   let c = Tri { b: 6, h: 4 }\n\
         \x20   assert_eq(&described(&a), &2504, \"the square\")\n\
         \x20   assert_eq(&described(&b), &2104, \"the rectangle\")\n\
         \x20   assert_eq(&described(&c), &1203, \"and the triangle\")\n\
         }\n\
         \n\
         %test\n\
         fn a_generic_impl_answers_through_its_instance() {\n\
         \x20   let b: Box<i64> = Box { v: 1 }\n\
         \x20   assert_eq(&described(&b), &1101, \"a table of instance symbols\")\n\
         }\n\
         \n\
         %test\n\
         fn the_member_reached_is_the_one_the_trait_names() {\n\
         \x20   // `sides` is the second member, so a table read at the first\n\
         \x20   // place answers with the area and this is what says so.\n\
         \x20   let c = Tri { b: 6, h: 4 }\n\
         \x20   let s: &dyn Shape = &c\n\
         \x20   assert_eq(&s.sides(), &3, \"the second member, not the first\")\n\
         \x20   assert_eq(&s.area(), &12, \"and the first, not the second\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "dyn");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "trait objects were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- What the collector holds ----------------------------------------------------

// A `gc` value, run.
//
// The word had been spent entirely in the front end: `let gc b = ...` compiled,
// worked, and allocated nothing, and `Ty::GC` was plumbed through twenty places
// and constructed by none of them. §8 said why -- until it was settled whether
// `gc` reaches a type, "a `gc` binding allocates nothing at all".
//
// So every one of these is a value asserted after something that could only be
// right if the room is really the collector's:
//
//   - a value outlives the frame that made it, with another call using the
//     stack in between. That is the whole of what a collector is for, and a
//     frame slot would have been written over.
//   - two hundred thousand of them, which is more than the heap holds at once,
//     so the answer is only right if what is unreachable is being taken back.
//   - and a value made before all that is still what it was, which is the other
//     half: what is *reachable* has to survive, and the roots are guessed at.
//   - a handle is copied and not moved, so a binding it was handed from still
//     holds it -- §8 asked, and this is the answer.
//   - a container of them, which §8 names as the thing that could not be
//     written.
#[test]
fn a_collected_value_outlives_the_frame_that_made_it() {
    let dir = std::env::temp_dir().join(format!("fortec-gc-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("held.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         import vec::{Vec, empty, push, at, len};\n\
         \n\
         struct Buf { pub n: i64 }\n\
         struct Inner { pub v: i64 }\n\
         struct Outer { pub tag: i64, pub inner: gc Inner }\n\
         \n\
         fn made(n: i64): gc Buf {\n\
         \x20   let gc b = Buf { n: n }\n\
         \x20   b\n\
         }\n\
         \n\
         fn churn(a: i64): i64 { a * 7777 + a * 8888 }\n\
         fn held(b: gc Buf): i64 { b.n }\n\
         \n\
         %test\n\
         fn it_survives_the_frame_it_was_made_in() {\n\
         \x20   let one = made(11)\n\
         \x20   assert_eq(&churn(3), &49995, \"something else uses the stack\")\n\
         \x20   assert_eq(&one.n, &11, \"and it is still what it was\")\n\
         }\n\
         \n\
         %test\n\
         fn a_handle_is_copied_and_not_moved() {\n\
         \x20   let one = made(5)\n\
         \x20   assert_eq(&held(one), &5, \"handed over\")\n\
         \x20   assert_eq(&held(one), &5, \"and handed over again\")\n\
         \x20   assert_eq(&one.n, &5, \"and the name still holds it\")\n\
         }\n\
         \n\
         %test\n\
         fn what_is_reachable_lives_and_what_is_not_is_taken_back() {\n\
         \x20   let gc i = Inner { v: 42 }\n\
         \x20   let gc o = Outer { tag: 7, inner: i }\n\
         \x20   var k = 0\n\
         \x20   var total = 0\n\
         \x20   while k < 200000 {\n\
         \x20       let gc t = Inner { v: 1 }\n\
         \x20       total = total + t.v\n\
         \x20       k = k + 1\n\
         \x20   }\n\
         \x20   assert_eq(&total, &200000, \"every one of them was there\")\n\
         \x20   assert_eq(&o.inner.v, &42, \"and what was reachable stayed\")\n\
         }\n\
         \n\
         %test\n\
         fn a_container_of_them_is_written() {\n\
         \x20   var v: Vec<gc Buf> = empty()\n\
         \x20   var i = 0\n\
         \x20   while i < 5 {\n\
         \x20       let gc b = Buf { n: i * i }\n\
         \x20       push(*v, b)\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   assert_eq(&len(&v), &5, \"five of them\")\n\
         \x20   assert_eq(&at(&v, 3).n, &9, \"and the fourth is the fourth\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "held");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "collected values were meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- Where a conversion may happen ------------------------------------------------

// The three conversions, made where the value is *written* rather than only
// where it is handed to something.
//
// A conversion happens where a type is expected of a value: `&T[8]` becomes a
// view, `&Sq` becomes a `&dyn Shape`, and a `Buf` becomes a `gc Buf`. What used
// to be expected of nothing was a branch, a tail and a body -- so
// `fn f(q: &Sq): &dyn Shape { q }` was "this body gives back `&Sq`", and
// `let s: &dyn Shape = if c { x } else { y }` was two branches compared against
// each other, disagreeing, and never getting as far as a conversion.
//
// All three are asserted through each of the four places, because the machinery
// is one and a conversion missing in one position is missing in all of them.
// The `if` is run both ways: a branch that converts only on the path taken is a
// program that works until the condition changes.
#[test]
fn a_conversion_happens_wherever_a_type_is_expected() {
    let dir = std::env::temp_dir().join(format!("fortec-expect-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("expect.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         trait Shape {\n\
         \x20   fn area(&self): i64\n\
         }\n\
         struct Sq { pub s: i64 }\n\
         struct Ci { pub r: i64 }\n\
         struct Buf { pub n: i64 }\n\
         impl Shape for Sq {\n\
         \x20   fn area(&self): i64 { self.s * self.s }\n\
         }\n\
         impl Shape for Ci {\n\
         \x20   fn area(&self): i64 { self.r * 3 }\n\
         }\n\
         \n\
         fn summed(xs: &i64[], n: i64): i64 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n {\n\
         \x20       t = t + xs[i]\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   t\n\
         }\n\
         \n\
         // The body's answer, held to what the signature says.\n\
         fn as_object(q: &Sq): &dyn Shape { q }\n\
         fn as_collected(n: i64): gc Buf { Buf { n: n } }\n\
         fn as_view(a: &i64[4]): &i64[] { a }\n\
         \n\
         // And through a branch, an arm, and a block's tail.\n\
         fn by_branch(c: bool, x: &Sq, y: &Ci): i64 {\n\
         \x20   let s: &dyn Shape = if c { x } else { y }\n\
         \x20   s.area()\n\
         }\n\
         fn by_arm(k: i64, x: &Sq, y: &Ci): i64 {\n\
         \x20   let s: &dyn Shape = match k { 0 => x, _ => y }\n\
         \x20   s.area()\n\
         }\n\
         fn by_tail(c: bool, x: &Sq, y: &Ci): i64 {\n\
         \x20   let s: &dyn Shape = {\n\
         \x20       let held = 1\n\
         \x20       if c { x } else { y }\n\
         \x20   }\n\
         \x20   s.area()\n\
         }\n\
         \n\
         %test\n\
         fn a_body_converts_to_what_its_signature_says() {\n\
         \x20   let q = Sq { s: 5 }\n\
         \x20   assert_eq(&as_object(&q).area(), &25, \"a trait object\")\n\
         \x20   assert_eq(&as_collected(9).n, &9, \"a collected value\")\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   assert_eq(&summed(as_view(&a), 4), &10, \"and a view\")\n\
         }\n\
         \n\
         %test\n\
         fn each_way_out_of_a_branch_converts() {\n\
         \x20   let q = Sq { s: 5 }\n\
         \x20   let c = Ci { r: 4 }\n\
         \x20   assert_eq(&by_branch(true, &q, &c), &25, \"the way taken\")\n\
         \x20   assert_eq(&by_branch(false, &q, &c), &12, \"and the other one\")\n\
         \x20   assert_eq(&by_arm(0, &q, &c), &25, \"an arm\")\n\
         \x20   assert_eq(&by_arm(1, &q, &c), &12, \"and another arm\")\n\
         \x20   assert_eq(&by_tail(true, &q, &c), &25, \"and a block's tail\")\n\
         }\n\
         \n\
         %test\n\
         fn what_is_expected_reaches_one_expression_and_no_further() {\n\
         \x20   // The `if` is the argument, so what is expected of it is the\n\
         \x20   // parameter's type -- and the two numbers inside it are the\n\
         \x20   // `if`'s own business, not the call's.\n\
         \x20   assert_eq(&summed(&[1, 2, 3, 4], if true { 2 } else { 4 }), &3,\n\
         \x20             \"the branches are numbers and stay numbers\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "expect");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "conversions were meant to reach these places:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- What the process was started with --------------------------------------------

// The arguments and the environment, read by a program that was started with
// some.
//
// §8: "there is no spelling for the arguments a process was started with and
// none for its environment, so the only program that can be written is one that
// computes what it was going to compute anyway." This is the half that could
// only be asked by running a program *with* something -- a `%test` is run by a
// shim that hands over none, so every other test in this file is exactly the
// program §8 was describing.
//
// So it is `ran_with` and not `ran`, and the assertions are on what came back
// out: the count includes the program's own name as a C `main` counts it, each
// argument is the bytes it was and not the one beside it, an index past the end
// is empty rather than whatever was next in memory, and a name the environment
// holds is told from one it does not.
#[test]
fn a_program_reads_what_it_was_started_with() {
    let dir = std::env::temp_dir().join(format!("fortec-args-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("args.ft");
    std::fs::write(
        &root,
        "import fmt::println;\n\
         import env::{count, arg, get, has};\n\
         \n\
         fn main(): i64 {\n\
         \x20   println(\"count={}\", &[&count()])\n\
         \x20   var i = 1\n\
         \x20   while i < count() {\n\
         \x20       println(\"arg{}={}\", &[&i, &arg(i)])\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   // Past the end, which is empty and not the next thing along.\n\
         \x20   println(\"past=[{}]\", &[&arg(count())])\n\
         \x20   println(\"held={}\", &[&get(\"FORTEC_HELD\")])\n\
         \x20   let held: i64 = if has(\"FORTEC_HELD\") { 1 } else { 0 }\n\
         \x20   println(\"has={}\", &[&held])\n\
         \x20   let gone: i64 = if has(\"FORTEC_MISSING\") { 1 } else { 0 }\n\
         \x20   println(\"missing={}\", &[&gone])\n\
         \x20   0\n\
         }\n",
    )
    .expect("a file");

    let held = ran_with(
        &root,
        "args",
        &["one", "two three", ""],
        &[("FORTEC_HELD", "yes")],
    );
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a program was meant to read its arguments:\n{}", said);
    // The name and the three, which is what a C `main` is handed.
    assert!(said.contains("count=4"), "{}", said);
    assert!(said.contains("arg1=one"), "{}", said);
    // A space in one is one argument and not two: what the shell separated is
    // separated already, and nothing here separates it again.
    assert!(said.contains("arg2=two three"), "{}", said);
    assert!(said.contains("arg3=\n"), "an empty argument is still one:\n{}", said);
    assert!(said.contains("past=[]"), "{}", said);
    assert!(said.contains("held=yes"), "{}", said);
    assert!(said.contains("has=1"), "{}", said);
    assert!(said.contains("missing=0"), "{}", said);
}

// ---- A release and a collector, which are two answers to one question -------------

// `gc` and `Drop` together, refused; and a cycle asked for, which runs.
//
// §8 left two things about a `gc` open and these are both of them. The first is
// what happened when a type with a release was collected: nothing ran. The
// compiler placed no release, because the value is not the frame's; the
// collector placed none, because nothing ever told it there was one. A `drop`
// that silently never happens is worse than one that happens late, and it said
// nothing about it -- which is the shape of every wrong answer this suite was
// written to catch.
//
// So the pair is refused, and this is the running half: everything the refusal
// does *not* close still works, and a program may ask for a cycle and carry on.
#[test]
fn a_program_asks_for_a_cycle_and_what_it_holds_survives_one() {
    let dir = std::env::temp_dir().join(format!("fortec-cycle-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("cycle.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         import heap::collect;\n\
         \n\
         struct Buf { pub n: i64 }\n\
         struct Held { pub tag: i64, pub inner: gc Buf }\n\
         \n\
         %test\n\
         fn a_cycle_keeps_what_is_still_reachable() {\n\
         \x20   let gc keep = Buf { n: 42 }\n\
         \x20   let gc deep = Held { tag: 1, inner: keep }\n\
         \x20   var i = 0\n\
         \x20   while i < 50000 {\n\
         \x20       let gc t = Buf { n: i }\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   // Three of them, so a cycle that ran on the last one's rubbish\n\
         \x20   // is not what is being asserted.\n\
         \x20   collect()\n\
         \x20   collect()\n\
         \x20   collect()\n\
         \x20   assert_eq(&keep.n, &42, \"what a name still holds\")\n\
         \x20   assert_eq(&deep.inner.n, &42, \"and what one holds through another\")\n\
         }\n\
         \n\
         %test\n\
         fn a_cycle_may_be_asked_for_with_nothing_to_do() {\n\
         \x20   collect()\n\
         \x20   assert_eq(&1, &1, \"and it comes back\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "cycle");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a cycle was meant to keep what is reachable:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}

// ---- A global the linker has to finish ------------------------------------------

// A `str` global and a `str` const, both of which used to be nothing.
//
// §8: "a `str` global writes no bytes, an address not being known until the
// linker has run; it wants a relocation into the pool, which nothing has asked
// for yet." What it wrote was sixteen noughts, so a program reading one read
// the empty string and was told nothing at all -- and a `str` const was worse,
// being left out of the folding table and staying a symbol that linked against
// nothing.
//
// The values are the assertion because the shape cannot be: an image with the
// length right and the pointer left at nought reads empty, and so does one with
// no relocation at all. Only what comes back tells them apart.
#[test]
fn a_str_global_holds_the_bytes_it_was_written_with() {
    let dir = std::env::temp_dir().join(format!("fortec-strg-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("strg.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         const TAG: str = \"tag\"\n\
         var name: str = \"forte\"\n\
         var blank: str = \"\"\n\
         var unset: str\n\
         // Two globals of one text, which is one run of bytes in the pool and\n\
         // two relocations to it.\n\
         var same: str = \"forte\"\n\
         \n\
         %test\n\
         fn a_global_starts_as_what_it_was_written_as() {\n\
         \x20   assert_eq(&name, &\"forte\", \"the bytes and not none\")\n\
         \x20   assert_eq(&same, &\"forte\", \"and the same ones again\")\n\
         \x20   assert_eq(&blank, &\"\", \"an empty one is still written\")\n\
         \x20   assert_eq(&unset, &\"\", \"and one nothing filled is empty\")\n\
         }\n\
         \n\
         %test\n\
         fn a_const_folds_into_the_use_that_names_it() {\n\
         \x20   assert_eq(&TAG, &\"tag\", \"a const of text\")\n\
         }\n\
         \n\
         %test\n\
         fn a_global_may_be_written_over() {\n\
         \x20   name = \"changed\"\n\
         \x20   assert_eq(&name, &\"changed\", \"a global is a place\")\n\
         \x20   // And what was there is not what is there: the store went to\n\
         \x20   // the global and not to a copy of it.\n\
         \x20   assert_eq(&same, &\"forte\", \"and the other one is untouched\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "strg");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a `str` global was meant to hold its bytes:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A global that holds more than one number ------------------------------------

// A structure, an array and a tuple in the data segment, and every one of them
// used to be noughts.
//
// Only a folded *literal* was ever written into a global's image, so
// `Point { x: 3, y: 4 }` reached the segment as sixteen zero bytes and a program
// reading it was told nothing at all -- the same silence a `str` global had, and
// the same shape of wrong answer.
//
// The cause was one thing and it cost three: a global's initialiser was never
// lowered as an expression. So nothing about it was type checked either, and a
// `gc` global got a handle of nought. Walking it in the `bodies` pass answers
// all three, and this is the half a running program can see.
#[test]
fn a_global_holds_the_aggregate_it_was_written_with() {
    let dir = std::env::temp_dir().join(format!("fortec-aggg-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("aggg.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         struct Point { pub x: i64, pub y: i64 }\n\
         struct Held { pub tag: i64, pub at: Point, pub name: str }\n\
         \n\
         var p: Point = Point { x: 3, y: 4 }\n\
         var a: i64[4] = [7, 8, 9, 10]\n\
         var t: (i64, i64) = (11, 12)\n\
         // Nested, and with a `str` inside it -- so the relocation has to land\n\
         // at an offset rather than at the front.\n\
         var deep: Held = Held { tag: 1, at: Point { x: 5, y: 6 }, name: \"held\" }\n\
         // And the folding evaluator's answer still wins where it folds.\n\
         var folded: i64 = 6 * 7\n\
         \n\
         %test\n\
         fn a_structure_holds_its_fields() {\n\
         \x20   assert_eq(&p.x, &3, \"the first\")\n\
         \x20   assert_eq(&p.y, &4, \"and the second, at its offset\")\n\
         }\n\
         \n\
         %test\n\
         fn an_array_holds_its_elements() {\n\
         \x20   assert_eq(&a[0], &7, \"the first\")\n\
         \x20   assert_eq(&a[3], &10, \"and the last, at its stride\")\n\
         \x20   assert_eq(&t.0, &11, \"a tuple is a structure numbered\")\n\
         \x20   assert_eq(&t.1, &12, \"and its second\")\n\
         }\n\
         \n\
         %test\n\
         fn one_inside_another_holds_too() {\n\
         \x20   assert_eq(&deep.tag, &1, \"the field before it\")\n\
         \x20   assert_eq(&deep.at.y, &6, \"a structure inside a structure\")\n\
         \x20   assert_eq(&deep.name, &\"held\", \"and a `str` after it\")\n\
         \x20   assert_eq(&folded, &42, \"what the evaluator folded\")\n\
         }\n\
         \n\
         %test\n\
         fn a_global_is_still_a_place() {\n\
         \x20   p = Point { x: 30, y: 40 }\n\
         \x20   assert_eq(&p.x, &30, \"written over\")\n\
         \x20   assert_eq(&a[0], &7, \"and the one beside it is untouched\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "aggg");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a global was meant to hold its fields:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- A global the collector holds ------------------------------------------------

// A `gc` global, run.
//
// It used to segfault on the first read, and nothing said a word: a `gc T` is
// one word holding an address from `__rt_gc_alloc`, a global's image is bytes
// written when the program is compiled, and the allocator has not run then. So
// the handle was nought and reading through it dereferenced null.
//
// What this asserts is the half a program can see: the handle is filled in
// before `main`, from an expression as ordinary as any other. That the object
// then *survives a cycle* is the other half, and it is asserted in
// `runtime/src/gc/tests.rs` and not here -- a conservative root scan finds
// whatever the last few calls left on the stack, so a running program cannot
// tell a collector that kept its globals from one that merely had not written
// over the word yet. That file's header says so, and its `cycle_from` is what
// answers it.
#[test]
fn a_gc_global_is_filled_in_before_the_program_starts() {
    let dir = std::env::temp_dir().join(format!("fortec-gcg-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("gcg.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         import heap::collect;\n\
         \n\
         struct Buf { pub n: i64 }\n\
         struct Held { pub tag: i64, pub inner: gc Buf }\n\
         \n\
         fn made(n: i64): gc Buf {\n\
         \x20   let gc b = Buf { n: n }\n\
         \x20   b\n\
         }\n\
         \n\
         var kept: gc Buf = Buf { n: 4242 }\n\
         // In source order, and the second names a call rather than a literal --\n\
         // a global initialised by one had been nought too, with nothing said.\n\
         var also: gc Buf = made(7)\n\
         var deep: gc Held = Held { tag: 1, inner: kept }\n\
         \n\
         %test\n\
         fn a_gc_global_holds_what_it_was_written_with() {\n\
         \x20   assert_eq(&kept.n, &4242, \"read before anything else runs\")\n\
         \x20   assert_eq(&also.n, &7, \"and one a call gave back\")\n\
         \x20   assert_eq(&deep.inner.n, &4242, \"and one holding another\")\n\
         }\n\
         \n\
         %test\n\
         fn a_gc_global_is_a_place_like_any_other() {\n\
         \x20   kept = made(9)\n\
         \x20   assert_eq(&kept.n, &9, \"written over\")\n\
         \x20   assert_eq(&also.n, &7, \"and the one beside it is untouched\")\n\
         }\n\
         \n\
         %test\n\
         fn it_is_still_there_after_a_cycle() {\n\
         \x20   var i = 0\n\
         \x20   while i < 100000 {\n\
         \x20       let gc junk = Buf { n: i }\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   collect()\n\
         \x20   collect()\n\
         \x20   assert_eq(&also.n, &7, \"and reads as what it was\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "gcg");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a `gc` global was meant to be filled in:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A trait answered by a primitive ---------------------------------------------

// `impl Show for i64`, reached three ways.
//
// The declaration always worked -- `sema::lower::bounds` has keyed impls by a
// *head* since it was written, and says so: "`impl Copy for i32` is written for
// the primitive and not for a name", so a `T: Show` bound with `T = i64` has
// always passed. What did not work was reaching the body. Four lookups asked
// which impl a type's is, and all four asked it by `Ty::Named`, so a primitive
// fell out of every one of them:
//
//   - a method call found nothing and said "no field";
//   - a generic resolved to the *trait's* member, which has no body, and the
//     build failed at the link step;
//   - a `dyn` built no table at all;
//   - and `&5` was refused where a `&dyn Show` was wanted.
//
// So the three paths are all asserted here, and each answers differently per
// type: a lookup that found the wrong impl runs and gives a wrong number, and
// only the number tells them apart.
//
// The last of the four wanted a second thing on top of the head, and gets a
// fourth test below. An unsuffixed number is not a primitive yet -- it is a
// hole -- and nobody writes an impl for a hole, so asking by head found
// nothing however the head was worked out. What answers it is the type the
// hole would settle as, which `Types::standing` hands over.
#[test]
fn a_primitive_answers_a_trait_like_anything_else() {
    let dir = std::env::temp_dir().join(format!("fortec-prim-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("prim.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         trait Tagged {\n\
         \x20   fn tag(&self): i64\n\
         }\n\
         \n\
         struct Sq { pub s: i64 }\n\
         impl Tagged for Sq   { fn tag(&self): i64 { 100 } }\n\
         impl Tagged for i64  { fn tag(&self): i64 { 1 } }\n\
         impl Tagged for i32  { fn tag(&self): i64 { 4 } }\n\
         impl Tagged for bool { fn tag(&self): i64 { 2 } }\n\
         impl Tagged for str  { fn tag(&self): i64 { 3 } }\n\
         \n\
         fn by_bound<T: Tagged>(x: &T): i64 { x.tag() }\n\
         fn by_table(x: &dyn Tagged): i64 { x.tag() }\n\
         fn by_both<T: Tagged>(x: &T): i64 { by_table(x) }\n\
         \n\
         %test\n\
         fn a_method_is_called_on_a_primitive() {\n\
         \x20   let n: i64 = 7\n\
         \x20   let b: bool = true\n\
         \x20   let s: str = \"hi\"\n\
         \x20   assert_eq(&n.tag(), &1, \"an i64\")\n\
         \x20   assert_eq(&b.tag(), &2, \"a bool\")\n\
         \x20   assert_eq(&s.tag(), &3, \"and a str\")\n\
         }\n\
         \n\
         %test\n\
         fn a_bound_reaches_the_primitives_own_body() {\n\
         \x20   let n: i64 = 7\n\
         \x20   let s: str = \"hi\"\n\
         \x20   let q = Sq { s: 1 }\n\
         \x20   assert_eq(&by_bound(&n), &1, \"the i64 instance\")\n\
         \x20   assert_eq(&by_bound(&s), &3, \"the str one\")\n\
         \x20   assert_eq(&by_bound(&q), &100, \"and a struct still works\")\n\
         }\n\
         \n\
         %test\n\
         fn a_table_is_built_for_a_primitive() {\n\
         \x20   let n: i64 = 7\n\
         \x20   let b: bool = true\n\
         \x20   let q = Sq { s: 1 }\n\
         \x20   assert_eq(&by_table(&n), &1, \"one body, three tables\")\n\
         \x20   assert_eq(&by_table(&b), &2, \"the second\")\n\
         \x20   assert_eq(&by_table(&q), &100, \"and the struct's\")\n\
         }\n\
         \n\
         %test\n\
         fn a_number_with_nothing_said_about_it_is_an_object_too() {\n\
         \x20   // The guess and nothing else: an `i32`, so the `i32` body runs.\n\
         \x20   assert_eq(&by_table(&5), &4, \"a bare literal\")\n\
         \x20   // And the guess is not taken -- a line below still says what\n\
         \x20   // the number is, and the table is built for what it ended as.\n\
         \x20   let n = 5\n\
         \x20   let held: &dyn Tagged = &n\n\
         \x20   let m: i64 = n\n\
         \x20   assert_eq(&held.tag(), &1, \"filled from below\")\n\
         \x20   assert_eq(&m, &5, \"and it is still the value it was\")\n\
         }\n\
         \n\
         %test\n\
         fn a_bound_is_enough_to_make_an_object_of() {\n\
         \x20   // The bound already said this type answers the trait, so the\n\
         \x20   // object may be made -- and which table, the instance says.\n\
         \x20   let n: i64 = 7\n\
         \x20   let b: bool = true\n\
         \x20   let q = Sq { s: 1 }\n\
         \x20   assert_eq(&by_both(&n), &1, \"the i64 table\")\n\
         \x20   assert_eq(&by_both(&b), &2, \"the bool one\")\n\
         \x20   assert_eq(&by_both(&q), &100, \"and the struct's\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "prim");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a primitive was meant to answer a trait:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 5 tests"), "{}", said);
}

// ---- A method on a place is a method on its address --------------------------------

// "A place is reached through one `*` or through any number of `&`" (§3), and a
// method call on a place is one of those reaches: a body that declares `&self`
// is handed the *address* of the receiver. Nothing was doing it -- what such a
// body got was the receiver's own bits read as an address.
//
// It hid for as long as it did because no `&self` body in the tree read its
// receiver. Every method here either ignored `self` or was called on something
// that was an address already, so a wrong address was handed over and never
// followed. The moment one was followed -- `n.show(into)` on an `i64` holding
// seven -- it dereferenced the number seven.
//
// So the assertions are on *values read through the receiver*, which is the
// only thing that can tell the two apart: a body that ignores `self` passes
// either way, and only running says which address it was given.
#[test]
fn a_method_that_declares_a_reference_is_handed_the_receivers_address() {
    let dir = std::env::temp_dir().join(format!("fortec-recv-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("recv.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         trait Held {\n\
         \x20   fn held(&self): i64\n\
         \x20   fn twice(&self): i64\n\
         }\n\
         \n\
         struct Sq { pub s: i64 }\n\
         impl Held for Sq {\n\
         \x20   fn held(&self): i64 { self.s }\n\
         \x20   fn twice(&self): i64 { self.s * 2 }\n\
         }\n\
         impl Held for i64 {\n\
         \x20   fn held(&self): i64 { self }\n\
         \x20   fn twice(&self): i64 { self * 2 }\n\
         }\n\
         \n\
         %test\n\
         fn a_value_receiver_is_addressed() {\n\
         \x20   // A local holding the value, which is the shape that crashed.\n\
         \x20   let n: i64 = 7\n\
         \x20   assert_eq(&n.held(), &7, \"the number it was called on\")\n\
         \x20   assert_eq(&n.twice(), &14, \"and read more than once\")\n\
         \x20   let q = Sq { s: 9 }\n\
         \x20   assert_eq(&q.held(), &9, \"a struct receiver, same rule\")\n\
         }\n\
         \n\
         %test\n\
         fn a_receiver_that_is_already_an_address_is_left_alone() {\n\
         \x20   let n: i64 = 7\n\
         \x20   let r: &i64 = &n\n\
         \x20   assert_eq(&r.held(), &7, \"a reference is an address already\")\n\
         \x20   let q = Sq { s: 9 }\n\
         \x20   let p: &Sq = &q\n\
         \x20   assert_eq(&p.twice(), &18, \"and so is one to a struct\")\n\
         }\n\
         \n\
         %test\n\
         fn a_field_and_an_element_are_places_too() {\n\
         \x20   let q = Sq { s: 9 }\n\
         \x20   assert_eq(&q.s.held(), &9, \"a field of one\")\n\
         \x20   let a: i64[3] = [4, 5, 6]\n\
         \x20   assert_eq(&a[1].held(), &5, \"and an element\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "recv");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a receiver was meant to be addressed:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A reference read as what it refers to ---------------------------------------

// "A reference stands for the place it refers to and is read, called, indexed
// and reached into exactly as that place is" (§3) -- and that was true of every
// one of those but *read*. `read_through` is the rule and it was wired into one
// place only, the operands of a binary operator: `a + &b` worked, `f(&b)` did
// not, and neither did giving one back where the signature says the value.
#[test]
fn a_reference_is_read_as_what_it_refers_to() {
    let dir = std::env::temp_dir().join(format!("fortec-reads-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("reads.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         fn takes(n: i64): i64 { n * 2 }\n\
         fn handed(r: &i64): i64 { takes(r) }\n\
         fn given(r: &i64): i64 { r }\n\
         fn bound(r: &i64): i64 {\n\
         \x20   let held: i64 = r\n\
         \x20   held + 1\n\
         }\n\
         \n\
         %test\n\
         fn a_reference_stands_where_the_value_was_wanted() {\n\
         \x20   let x: i64 = 21\n\
         \x20   assert_eq(&handed(&x), &42, \"handed to a call\")\n\
         \x20   assert_eq(&given(&x), &21, \"given back\")\n\
         \x20   assert_eq(&bound(&x), &22, \"and bound to a name\")\n\
         \x20   // The rule it always had: an operand of an operator.\n\
         \x20   assert_eq(&(&x + 1), &22, \"which is where it started\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "reads");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a reference was meant to read as its value:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 1 test"), "{}", said);
}

// ---- One `println`, and one of everything else -----------------------------------

// Twenty printing routines became four, and the tag a caller wrote became a
// body the value answers with.
//
// Both halves were the same missing thing and §8 named it: "traits with code
// behind them". Without one there was no way to ask a value what it was, so
// every argument was wrapped at the call -- `int(x)`, `text(s)` -- and no way
// to take "a format string and whatever follows it", so the arity was in the
// name and stopped at four.
//
// What this asserts is what only running can say: that each value reached its
// own `show`, that the count is the view's own length and not something the
// caller was trusted to get right, and that a `str` and an `i64` in one call
// come out in the order they were written.
#[test]
fn one_println_prints_whatever_it_was_handed() {
    let dir = std::env::temp_dir().join(format!("fortec-say-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("say.ft");
    std::fs::write(
        &root,
        "import fmt::{println, print, eprintln, Show, Sink, put};\n\
         \n\
         struct Point { pub x: i64, pub y: i64 }\n\
         \n\
         impl Show for Point {\n\
         \x20   fn show(&self, into: &Sink) {\n\
         \x20       put(into, \"Point { x: \")\n\
         \x20       self.x.show(into)\n\
         \x20       put(into, \", y: \")\n\
         \x20       self.y.show(into)\n\
         \x20       put(into, \" }\")\n\
         \x20   }\n\
         }\n\
         \n\
         fn main(): i64 {\n\
         \x20   // Nought, one, and more than the old ladder could take.\n\
         \x20   println(\"none\", &[])\n\
         \x20   let n: i64 = 5\n\
         \x20   println(\"one={}\", &[&n])\n\
         \x20   let s: str = \"text\"\n\
         \x20   let b: bool = true\n\
         \x20   let f: f64 = 1.5\n\
         \x20   println(\"five={} {} {} {} {}\", &[&n, &s, &b, &f, &n])\n\
         \x20   // A `str` and a number in one call, in the order written.\n\
         \x20   println(\"{}-{}\", &[&s, &n])\n\
         \x20   // The other three families are the same routine with a flag.\n\
         \x20   print(\"nolinebreak \", &[])\n\
         \x20   println(\"after\", &[])\n\
         \x20   eprintln(\"to the error stream {}\", &[&n])\n\
         \x20   // A value written in more than one piece, which is what a\n\
         \x20   // struct is and what an `Arg` could never have said.\n\
         \x20   let p = Point { x: 3, y: 4 }\n\
         \x20   println(\"{}\", &[&p])\n\
         \x20   // The room around it is the room around the whole of it.\n\
         \x20   println(\"[{:>24}]\", &[&p])\n\
         \x20   // And it goes in a line beside anything else.\n\
         \x20   println(\"{} and {}\", &[&p, &n])\n\
         \x20   0\n\
         }\n",
    )
    .expect("a file");

    let held = ran_program(&root, "say");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "printing was meant to work:\n{}", said);
    assert!(said.contains("none\n"), "{}", said);
    assert!(said.contains("one=5\n"), "{}", said);
    assert!(said.contains("five=5 text true 1.5 5\n"), "{}", said);
    assert!(said.contains("text-5\n"), "{}", said);
    // `print` ended no line, so the next one runs on from it.
    assert!(said.contains("nolinebreak after\n"), "{}", said);
    assert!(said.contains("to the error stream 5\n"), "{}", said);
    // A value written in more than one piece, which is the thing an `Arg`
    // could not say: it held one number or one piece of text, and a struct is
    // a name and its fields and the punctuation between them.
    assert!(said.contains("Point { x: 3, y: 4 }\n"), "{}", said);
    // The room around it is the room around the whole of it and not around
    // each piece.
    assert!(said.contains("[    Point { x: 3, y: 4 }]\n"), "{}", said);
    assert!(said.contains("Point { x: 3, y: 4 } and 5\n"), "{}", said);
}

// ---- A reference to what a pointer points at -----------------------------------------

// `&(deref p)` is `p`, and it has to be a value of its own all the same.
//
// `sir::lower` gives an address the type the source wrote over it rather than
// wrapping it in an instruction that does nothing, and every place it reaches
// for one is an instruction it makes on the spot -- except `deref`, which gives
// back the operand itself, there being nothing between an address and the place
// it addresses. So the type went onto a `Load` that `promote` was entitled to
// take out, and what every later use named was the `ptr i64` that had been
// stored.
//
// Nothing minds two names for one word until `mir::mono` recovers a call's type
// arguments from what the values say they are: `assert_eq(&(deref p), ..)` came
// out instantiated with a `ptr i64` for its `T`, for which there is no
// `impl Show`, so the table beside the value held an address nothing made and
// the runtime followed it.
//
// Which is why the test is written through a generic and run: the tree is right
// at every level above the SIR, and the wrong type is one only the symbol in
// the table shows.
#[test]
fn a_reference_to_what_a_pointer_points_at_keeps_its_own_type() {
    let dir = std::env::temp_dir().join(format!("fortec-deref-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("deref.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         import fmt::println;\n\
         \n\
         struct P { pub x: i64 }\n\
         \n\
         fn same(r: &i64): i64 { r }\n\
         \n\
         %test\n\
         fn it_reaches_a_generic_as_what_the_source_wrote() {\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[0]\n\
         \x20       // Through `assert_eq<T: Show>`, which is where the type\n\
         \x20       // the value says it is becomes the instance that is made.\n\
         \x20       assert_eq(&(deref p), &1, \"the first\")\n\
         \x20       // And bound to a name of its own first, which did not help.\n\
         \x20       let h: &i64 = &(deref p)\n\
         \x20       assert_eq(h, &1, \"and through a name\")\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn it_is_a_reference_everywhere_else_too() {\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[2]\n\
         \x20       // Handed to something that takes a reference, and read.\n\
         \x20       assert_eq(&same(&(deref p)), &3, \"handed on\")\n\
         \x20       // And the word it holds is still the address it was.\n\
         \x20       let q = addr (deref p)\n\
         \x20       assert_eq(&(deref q), &3, \"and back again\")\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn a_struct_through_one_is_reached_into() {\n\
         \x20   let a: P[2] = [P { x: 1 }, P { x: 9 }]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[1]\n\
         \x20       assert_eq(&(deref p).x, &9, \"a field of what it points at\")\n\
         \x20   }\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "deref");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a reference to a deref was meant to keep its type:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- The address n elements along ----------------------------------------------------

// `p + n` and `p - n`, which section 2 has been calling the general pointer
// arithmetic and saying is not written. `p[i]` was "the whole of the pointer
// arithmetic a container needs" and left this with no spelling at all -- so
// code that wanted the address of the element after the one it held had to
// index a place and take its address back, which is a read the program did not
// want and a word it should not have needed.
//
// It steps by the *element's stride* and not by bytes, which is what makes it
// arithmetic on a `ptr T` rather than on a number, and that is what only
// running can say: an unscaled step compiles and reads the wrong bytes.
#[test]
fn a_pointer_steps_by_the_element_it_points_at() {
    let dir = std::env::temp_dir().join(format!("fortec-step-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("step.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         struct P { pub x: i64, pub y: i64 }\n\
         \n\
         %test\n\
         fn a_pointer_steps_forward_and_back() {\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[0]\n\
         \x20       assert_eq(&(deref (p + 3)), &4, \"three along\")\n\
         \x20       let q = addr a[3]\n\
         \x20       assert_eq(&(deref (q - 2)), &2, \"and two back\")\n\
         \x20       // Nought is where it was.\n\
         \x20       assert_eq(&(deref (p + 0)), &1, \"and nowhere at all\")\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn the_step_is_the_elements_own_width() {\n\
         \x20   // A byte, which is the one width an unscaled step would have\n\
         \x20   // got right by accident.\n\
         \x20   let b: u8[4] = [1, 2, 3, 4]\n\
         \x20   unsafe {\n\
         \x20       let p = addr b[0]\n\
         \x20       assert_eq(&((deref (p + 2)) as i64), &3, \"a byte apiece\")\n\
         \x20   }\n\
         \x20   // And something wider than a word.\n\
         \x20   let a: P[2] = [P { x: 1, y: 2 }, P { x: 9, y: 8 }]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[0]\n\
         \x20       assert_eq(&(deref (p + 1)).x, &9, \"sixteen apiece\")\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn what_it_gives_back_is_a_pointer_like_any_other() {\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   unsafe {\n\
         \x20       let p = addr a[0]\n\
         \x20       // Stepped again, and indexed, and compared.\n\
         \x20       let q = (p + 1) + 1\n\
         \x20       assert_eq(&(deref q), &3, \"stepped twice\")\n\
         \x20       assert_eq(&q[1], &4, \"and indexed from there\")\n\
         \x20       let r = p + 2\n\
         \x20       assert_eq(&(q == r), &true, \"two of one address\")\n\
         \x20   }\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "step");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a pointer was meant to step by its element:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A table built for a generic impl ------------------------------------------------

// `impl<A: T> T for Box<A>`, made into a trait object.
//
// The entry a table holds is a *symbol*, and for a generic impl it has to be
// the instance's -- `mir::mono` works out what `A` stands for by matching the
// receiver it was handed against the receiver the impl declared. It handed
// that over as a one-item parameter list, and `recover` pairs a list against
// the member's declared parameters by *length*: a member taking anything
// besides its receiver never matched, so the table named the declaration and
// the linker had nothing to point it at.
//
// So a trait whose member takes one argument is the whole of the test, and
// nothing below the linker could have caught it: every symbol in the table was
// spelled, and one of them was spelled for a type no body was made for.
#[test]
fn a_table_for_a_generic_impl_names_the_instance() {
    let dir = std::env::temp_dir().join(format!("fortec-gentab-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("gentab.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         trait T {\n\
         \x20   // Two parameters, which is what it took: a member of one\n\
         \x20   // matched by length and this one never did.\n\
         \x20   fn f(&self, k: i64): i64\n\
         }\n\
         \n\
         struct Box<A> { pub held: A }\n\
         impl<A: T> T for Box<A> { fn f(&self, k: i64): i64 { self.held.f(k) * 2 } }\n\
         impl T for i64 { fn f(&self, k: i64): i64 { self + k } }\n\
         impl T for bool { fn f(&self, k: i64): i64 { k * 10 } }\n\
         \n\
         fn by_table(s: &dyn T): i64 { s.f(1) }\n\
         \n\
         %test\n\
         fn a_generic_impl_answers_through_a_table() {\n\
         \x20   let b: Box<i64> = Box { held: 20 }\n\
         \x20   assert_eq(&by_table(&b), &42, \"the i64 instance\")\n\
         }\n\
         \n\
         %test\n\
         fn one_instance_is_not_another() {\n\
         \x20   // Two of them, so a table naming the declaration would be one\n\
         \x20   // symbol where two bodies are wanted.\n\
         \x20   let a: Box<i64> = Box { held: 20 }\n\
         \x20   let b: Box<bool> = Box { held: true }\n\
         \x20   assert_eq(&by_table(&a), &42, \"one\")\n\
         \x20   assert_eq(&by_table(&b), &20, \"and the other\")\n\
         }\n\
         \n\
         %test\n\
         fn one_inside_another_is_the_same_question_twice() {\n\
         \x20   let held: Box<Box<i64>> = Box { held: Box { held: 20 } }\n\
         \x20   assert_eq(&by_table(&held), &84, \"nested\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "gentab");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a generic impl was meant to answer through a table:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- What a written-out call leaves behind ------------------------------------------

// A fn that gives back a reference it was handed, called and then read through.
//
// It was a wrong answer at `-O2` and above, and only there. `opt::inline` makes
// a call's answer with a phi over the blocks that returned one, so a callee
// that gives back a reference it was handed puts the *caller's own address* in
// a phi -- and `promote` read every instruction and both terminators looking
// for an address that escapes and read no phis. So the slot came out from under
// the phi and what was left was a load from a register nothing had written.
//
// Every program here is built at the level it happened at, so what this asserts
// is what nothing else did: the same answer at every level. A test that only
// checked the tree would have passed, the tree being right; the SIR was not.
#[test]
fn a_call_that_gives_back_a_reference_is_written_out_soundly() {
    let dir = std::env::temp_dir().join(format!("fortec-inref-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("inref.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         struct B { pub n: i64 }\n\
         \n\
         // The shape: what comes back is what went in, so the phi the\n\
         // inlining makes carries the caller's own address.\n\
         fn same(n: &i64): &i64 { n }\n\
         fn whole(b: &B): &B { b }\n\
         // And one with two ways back, which is a phi with two edges.\n\
         fn pick(c: bool, a: &i64, b: &i64): &i64 { if c { a } else { b } }\n\
         \n\
         %test\n\
         fn a_reference_handed_in_and_back_reads_what_it_points_at() {\n\
         \x20   let x: i64 = 7\n\
         \x20   let h = same(&x)\n\
         \x20   assert_eq(&(h + 0), &7, \"read through what came back\")\n\
         \x20   // Straight through, with nothing to bind it to.\n\
         \x20   assert_eq(&(same(&x) + 0), &7, \"and without a name\")\n\
         }\n\
         \n\
         %test\n\
         fn a_struct_handed_in_and_back_is_reached_into() {\n\
         \x20   let b = B { n: 9 }\n\
         \x20   assert_eq(&whole(&b).n, &9, \"a field of what came back\")\n\
         }\n\
         \n\
         %test\n\
         fn two_ways_back_are_two_edges_of_one_phi() {\n\
         \x20   let x: i64 = 3\n\
         \x20   let y: i64 = 4\n\
         \x20   assert_eq(&(pick(true, &x, &y) + 0), &3, \"the first\")\n\
         \x20   assert_eq(&(pick(false, &x, &y) + 0), &4, \"and the second\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "inref");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a written-out call was meant to be sound:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A value of no bytes ------------------------------------------------------------

// A struct with no fields, whose *address* is a word like any other.
//
// It did not assemble. An address is a word however wide the thing it points at
// is, and the width the four address-computing instructions asked for was the
// definition's -- which is the same number for every type held by its address
// anyway (`mir::lower`, `indirect`), so the two coincided everywhere they were
// ever tried. A value of no bytes is the one type they come apart on: it is
// held directly, its register is a byte, and `leaq -42(%rbp), %al` is not an
// instruction.
//
// So this is a test that has to *assemble and run*, which is the only kind that
// could have caught it: every pass above the emitter was already right.
#[test]
fn a_value_of_no_bytes_has_an_address_like_anything_else() {
    let dir = std::env::temp_dir().join(format!("fortec-empty-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("empty.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         struct Unit {}\n\
         trait T {\n\
         \x20   fn t(&self): i64\n\
         }\n\
         impl T for Unit { fn t(&self): i64 { 5 } }\n\
         \n\
         struct Held { pub u: Unit, pub n: i64 }\n\
         \n\
         fn by_table(x: &dyn T): i64 { x.t() }\n\
         fn by_ref(u: &Unit): i64 { 7 }\n\
         \n\
         %test\n\
         fn its_address_is_taken_and_handed_round() {\n\
         \x20   let u = Unit {}\n\
         \x20   // A name of reference type, which is where the address gets a\n\
         \x20   // register of its own and where this used to stop.\n\
         \x20   let p = &u\n\
         \x20   assert_eq(&by_ref(p), &7, \"handed on\")\n\
         \x20   assert_eq(&by_ref(&u), &7, \"and taken at the call\")\n\
         }\n\
         \n\
         %test\n\
         fn a_method_on_one_is_handed_its_address() {\n\
         \x20   let u = Unit {}\n\
         \x20   assert_eq(&u.t(), &5, \"a receiver of no bytes\")\n\
         \x20   assert_eq(&T::t(&u), &5, \"named through what declared it\")\n\
         }\n\
         \n\
         %test\n\
         fn one_becomes_a_trait_object() {\n\
         \x20   // Two words, the first of which is the address of nothing.\n\
         \x20   let u = Unit {}\n\
         \x20   assert_eq(&by_table(&u), &5, \"through a table\")\n\
         }\n\
         \n\
         %test\n\
         fn one_sits_in_a_struct_beside_something() {\n\
         \x20   let h = Held { u: Unit {}, n: 4 }\n\
         \x20   assert_eq(&h.n, &4, \"the field beside it is where it was\")\n\
         \x20   assert_eq(&h.u.t(), &5, \"and it is reachable through the field\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "empty");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a value of no bytes was meant to have an address:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- A method named through what declared it ---------------------------------------

// A method was reachable through a `.` and through nothing else, and a `.`
// answers with the nearest thing -- so a field that could be the thing called
// won and the method of that name could not be reached at all (§5, §8). There
// is a second spelling now, and what only running can say is which body it
// reached: every one of these answers a different number.
#[test]
fn a_method_is_named_through_the_declaration_it_belongs_to() {
    let dir = std::env::temp_dir().join(format!("fortec-through-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("through.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         trait T {\n\
         \x20   fn f(&self): i64\n\
         }\n\
         trait A {\n\
         \x20   fn both(&self): i64\n\
         }\n\
         trait B {\n\
         \x20   fn both(&self): i64\n\
         }\n\
         \n\
         // A struct whose field is callable and whose method has the field's\n\
         // name, which is the shape that had no spelling.\n\
         struct Q { pub f: fn(): i64, pub n: i64 }\n\
         impl T for Q { fn f(&self): i64 { self.n * 10 } }\n\
         impl Q { fn own(&self): i64 { self.n * 100 } }\n\
         impl A for Q { fn both(&self): i64 { 1 } }\n\
         impl B for Q { fn both(&self): i64 { 2 } }\n\
         \n\
         fn seven(): i64 { 7 }\n\
         \n\
         fn by_a<P: A + B>(p: &P): i64 { A::both(p) }\n\
         fn by_b<P: A + B>(p: &P): i64 { B::both(p) }\n\
         \n\
         %test\n\
         fn a_field_and_the_method_it_hides_are_both_reachable() {\n\
         \x20   let q = Q { f: seven, n: 3 }\n\
         \x20   // The `.` is the field, which is what it always was.\n\
         \x20   assert_eq(&q.f(), &7, \"the field is nearer\")\n\
         \x20   // And the method is reached through what declared it.\n\
         \x20   assert_eq(&T::f(&q), &30, \"the trait that declared it\")\n\
         \x20   assert_eq(&Q::f(&q), &30, \"or the type an impl wrote it in\")\n\
         }\n\
         \n\
         %test\n\
         fn an_impl_that_answers_no_trait_is_named_by_its_type() {\n\
         \x20   let q = Q { f: seven, n: 3 }\n\
         \x20   assert_eq(&Q::own(&q), &300, \"an inherent impl\")\n\
         }\n\
         \n\
         %test\n\
         fn a_bound_naming_two_of_one_name_is_settled_by_saying_which() {\n\
         \x20   let q = Q { f: seven, n: 3 }\n\
         \x20   assert_eq(&by_a(&q), &1, \"the one A declared\")\n\
         \x20   assert_eq(&by_b(&q), &2, \"and the one B did\")\n\
         }\n\
         \n\
         %test\n\
         fn the_receiver_may_be_the_value_and_not_a_reference_to_it() {\n\
         \x20   let q = Q { f: seven, n: 3 }\n\
         \x20   assert_eq(&Q::f(q), &30, \"a place is addressed where a method asks\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "through");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a method was meant to be named through its declaration:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- The number a variant is -------------------------------------------------------

// "A variant with no payload may fix its discriminant instead, which is what
// makes an enum of plain constants" (§2). It could not: what a written `D = 4`
// came to wanted a const evaluator and there was none.
//
// What only running can say is that the number written is the number *stored*:
// the tag is what a `match` reads, and every other pass -- the layout that
// sizes it, the load that reads it, the comparison that tests it -- has to
// agree with the checker about what it is. A negative one is where they came
// apart: a byte holding -3 read back with the bytes above it filled with
// noughts is a 253, and every arm of the match missed.
#[test]
fn a_variant_is_the_number_it_was_given() {
    let dir = std::env::temp_dir().join(format!("fortec-tags-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("tags.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         const BASE: i64 = 100\n\
         \n\
         enum Code {\n\
         \x20   Ok = 0,\n\
         \x20   Missing = 404,\n\
         \x20   Next,\n\
         \x20   Shifted = 1 << 5,\n\
         \x20   Named = BASE + 1,\n\
         \x20   Low = 0 - 3,\n\
         }\n\
         \n\
         fn number(c: &Code): i64 {\n\
         \x20   match c {\n\
         \x20       Code::Ok => 0,\n\
         \x20       Code::Missing => 404,\n\
         \x20       Code::Next => 405,\n\
         \x20       Code::Shifted => 32,\n\
         \x20       Code::Named => 101,\n\
         \x20       Code::Low => 0 - 3,\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn a_written_number_is_the_one_stored() {\n\
         \x20   let a = Code::Ok\n\
         \x20   assert_eq(&number(&a), &0, \"nought\")\n\
         \x20   let b = Code::Missing\n\
         \x20   assert_eq(&number(&b), &404, \"one that does not fit in a byte\")\n\
         \x20   let c = Code::Shifted\n\
         \x20   assert_eq(&number(&c), &32, \"one written as a shift\")\n\
         \x20   let d = Code::Named\n\
         \x20   assert_eq(&number(&d), &101, \"one written off a const\")\n\
         }\n\
         \n\
         %test\n\
         fn counting_carries_on_from_the_last_one_written() {\n\
         \x20   let held = Code::Next\n\
         \x20   assert_eq(&number(&held), &405, \"one more than the 404 above it\")\n\
         }\n\
         \n\
         %test\n\
         fn a_negative_number_is_read_back_as_one() {\n\
         \x20   // The tag is a signed integer, so the bytes above what the\n\
         \x20   // load read are filled by sign and not with noughts.\n\
         \x20   let held = Code::Low\n\
         \x20   assert_eq(&number(&held), &(0 - 3), \"below nought\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "tags");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a variant was meant to be the number it was given:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 3 tests"), "{}", said);
}

// ---- A match on a reference --------------------------------------------------------

// "A reference stands for the place it refers to and is read, called, indexed
// and reached into exactly as that place is" (§3) -- and matched. It was not:
// `match r { .. }` on a `&E` was "this tests `E` against `&E`", so nothing could
// look at an enum it had been lent, and every routine that wanted to had to be
// handed the value instead.
//
// What only running can say is the half this is about: a binding takes a
// *reference* to the part. So the scrutinee is still there afterwards -- it was
// borrowed and not taken apart -- and a payload that does not copy is readable
// without being moved out of a borrow, which is what a derived `Show` of an
// enum needs and could not have had.
#[test]
fn a_match_on_a_reference_borrows_what_it_looks_at() {
    let dir = std::env::temp_dir().join(format!("fortec-matchref-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("matchref.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         struct Sq { pub s: i64 }\n\
         enum E {\n\
         \x20   One,\n\
         \x20   Two(i64, str),\n\
         \x20   Held(Sq),\n\
         \x20   Named { a: i64, b: Sq },\n\
         }\n\
         \n\
         fn tag(e: &E): i64 {\n\
         \x20   match e {\n\
         \x20       E::One => 1,\n\
         \x20       E::Two(n, _) => n,\n\
         \x20       E::Held(q) => q.s,\n\
         \x20       E::Named { a, b } => a + b.s,\n\
         \x20   }\n\
         }\n\
         \n\
         fn held(e: gc E): i64 {\n\
         \x20   match e {\n\
         \x20       E::One => 1,\n\
         \x20       E::Two(n, _) => n,\n\
         \x20       E::Held(q) => q.s,\n\
         \x20       E::Named { a, b } => a + b.s,\n\
         \x20   }\n\
         }\n\
         \n\
         %test\n\
         fn a_reference_is_matched_as_what_it_refers_to() {\n\
         \x20   let a = E::One\n\
         \x20   assert_eq(&tag(&a), &1, \"a variant carrying nothing\")\n\
         \x20   let b = E::Two(7, \"x\")\n\
         \x20   assert_eq(&tag(&b), &7, \"one carrying two things\")\n\
         \x20   let c = E::Held(Sq { s: 9 })\n\
         \x20   assert_eq(&tag(&c), &9, \"and one carrying what does not copy\")\n\
         \x20   // The shorthand `{ a, b }` binds as `{ a: a }` does, which\n\
         \x20   // is what it was not: it took the value while the\n\
         \x20   // projection above it gave an address.\n\
         \x20   let d = E::Named { a: 4, b: Sq { s: 6 } }\n\
         \x20   assert_eq(&tag(&d), &10, \"one that names what it carries\")\n\
         }\n\
         \n\
         %test\n\
         fn what_was_matched_is_still_there() {\n\
         \x20   // Twice, which is the whole of what borrowing rather than\n\
         \x20   // taking apart buys: the payload was read and not moved.\n\
         \x20   let c = E::Held(Sq { s: 9 })\n\
         \x20   assert_eq(&(tag(&c) + tag(&c)), &18, \"read twice\")\n\
         }\n\
         \n\
         %test\n\
         fn a_collected_value_is_matched_the_same_way() {\n\
         \x20   let gc g = E::Two(4, \"y\")\n\
         \x20   assert_eq(&held(g), &4, \"a `gc` is reached through as a reference is\")\n\
         }\n\
         \n\
         %test\n\
         fn a_value_scrutinee_is_what_it_always_was() {\n\
         \x20   // Bound by value, which is the reading that did work and has\n\
         \x20   // to keep working.\n\
         \x20   let n = match E::Two(3, \"z\") {\n\
         \x20       E::One => 0,\n\
         \x20       E::Two(n, _) => n,\n\
         \x20       E::Held(q) => q.s,\n\
         \x20       E::Named { a, b } => a + b.s,\n\
         \x20   }\n\
         \x20   assert_eq(&n, &3, \"a value taken apart\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "matchref");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a match on a reference was meant to work:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 4 tests"), "{}", said);
}

// ---- The impl a reader would have written -----------------------------------------

// `%derive(Show)`, which is the first thing the attribute list said was waiting
// on "traits with code behind them" and is the last of the three that arrived
// with them.
//
// What it asserts is what only running can say: that the derived body reaches
// each field's *own* `show` -- so a field that is a struct with a derive of its
// own answers with its own body, three levels down -- and that a derived impl
// stands beside a hand-written one with nothing to tell them apart.
#[test]
fn a_derive_writes_the_impl_a_reader_would_have() {
    let dir = std::env::temp_dir().join(format!("fortec-derive-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("derive.ft");
    std::fs::write(
        &root,
        "import fmt::{Show, Sink, put, println};\n\
         \n\
         %derive(Show)\n\
         struct Point { pub x: i64, pub y: i64 }\n\
         \n\
         %derive(Show)\n\
         struct Wrap { pub name: str, pub at: Point, pub on: bool }\n\
         \n\
         // A hand-written one, which the derived bodies reach exactly as they\n\
         // reach a derived one: what answers is the impl and not how it got\n\
         // there.\n\
         struct Tick { pub n: i64 }\n\
         impl Show for Tick {\n\
         \x20   fn show(&self, into: &Sink) {\n\
         \x20       put(into, \"tick(\")\n\
         \x20       self.n.show(into)\n\
         \x20       put(into, \")\")\n\
         \x20   }\n\
         }\n\
         \n\
         %derive(Show)\n\
         struct Both { pub one: Tick, pub two: Wrap }\n\
         \n\
         // An enum is a choice among shapes, and each variant is written the\n\
         // way it was declared: a name, a parenthesis, or a brace.\n\
         // With parameters, each bounded by the trait: every field of a\n\
         // `T` has to answer `Show` for the body to be able to ask it.\n\
         %derive(Show)\n\
         struct Box<T> { pub held: T }\n\
         \n\
         %derive(Show)\n\
         enum Maybe<T> { Nothing, Just(T) }\n\
         \n\
         %derive(Show)\n\
         enum Held {\n\
         \x20   Nothing,\n\
         \x20   Some(i64, str),\n\
         \x20   Deep(Point),\n\
         \x20   Named { a: i64, b: Tick },\n\
         }\n\
         \n\
         fn main(): i64 {\n\
         \x20   println(\"{}\", &[&Point { x: 3, y: 4 }])\n\
         \x20   // A field that is a struct answers with its own body.\n\
         \x20   let w = Wrap { name: \"here\", at: Point { x: 1, y: 2 }, on: true }\n\
         \x20   println(\"{}\", &[&w])\n\
         \x20   // Three deep, and the hand-written one in the middle of it.\n\
         \x20   let b = Both {\n\
         \x20       one: Tick { n: 9 },\n\
         \x20       two: Wrap { name: \"x\", at: Point { x: 5, y: 6 }, on: false },\n\
         \x20   }\n\
         \x20   println(\"{}\", &[&b])\n\
         \x20   // The room around it is the room around the whole of it.\n\
         \x20   println(\"[{:>22}]\", &[&Point { x: 7, y: 8 }])\n\
         \x20   // And a spec about the value, said of a value that is several.\n\
         \x20   println(\"{:x}\", &[&Point { x: 1, y: 2 }])\n\
         \x20   // An enum, one line per shape a variant can have. The\n\
         \x20   // `match` it is written as runs on a `&self`, so a payload\n\
         \x20   // that does not copy is read where it lies.\n\
         \x20   let n = Held::Nothing\n\
         \x20   println(\"{}\", &[&n])\n\
         \x20   let s = Held::Some(3, \"hi\")\n\
         \x20   println(\"{}\", &[&s])\n\
         \x20   let d = Held::Deep(Point { x: 5, y: 6 })\n\
         \x20   println(\"{}\", &[&d])\n\
         \x20   let m = Held::Named { a: 7, b: Tick { n: 8 } }\n\
         \x20   println(\"{}\", &[&m])\n\
         \x20   // A declaration with parameters, once per set of them.\n\
         \x20   println(\"{}\", &[&Box { held: 7 }])\n\
         \x20   println(\"{}\", &[&Box { held: Point { x: 1, y: 2 } }])\n\
         \x20   let j: Maybe<str> = Maybe::Just(\"here\")\n\
         \x20   let e: Maybe<i64> = Maybe::Nothing\n\
         \x20   println(\"{} {}\", &[&j, &e])\n\
         \x20   0\n\
         }\n",
    )
    .expect("a file");

    let held = ran_program(&root, "derive");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a derive was meant to work:\n{}", said);
    assert!(said.contains("Point { x: 3, y: 4 }\n"), "{}", said);
    assert!(
        said.contains("Wrap { name: here, at: Point { x: 1, y: 2 }, on: true }\n"),
        "{}",
        said
    );
    assert!(
        said.contains(
            "Both { one: tick(9), two: Wrap { name: x, at: Point { x: 5, y: 6 }, \
             on: false } }\n"
        ),
        "{}",
        said
    );
    assert!(said.contains("[  Point { x: 7, y: 8 }]\n"), "{}", said);
    assert!(said.contains("several pieces"), "{}", said);
    // An enum, one line per shape a variant can have: carrying nothing,
    // carrying values by place, carrying one that does not copy, and naming
    // what it carries.
    assert!(said.contains("Nothing\n"), "{}", said);
    assert!(said.contains("Some(3, hi)\n"), "{}", said);
    assert!(said.contains("Deep(Point { x: 5, y: 6 })\n"), "{}", said);
    assert!(said.contains("Named { a: 7, b: tick(8) }\n"), "{}", said);
    // With parameters: once per set of them, and the field's own `show` is
    // whatever the parameter turned out to be.
    assert!(said.contains("Box { held: 7 }\n"), "{}", said);
    assert!(said.contains("Box { held: Point { x: 1, y: 2 } }\n"), "{}", said);
    assert!(said.contains("Just(here) Nothing\n"), "{}", said);
}

// ---- A view's own length ---------------------------------------------------------

// "The length moving out of the type and into the value" (§3) is what a view
// is, and the value has been two words since -- where the elements begin and
// how many there are -- with only the first of them reachable. So every routine
// taking a view took a count beside it and was trusted to be told the truth.
//
// It is what let the printing above take one parameter rather than two.
#[test]
fn a_view_answers_how_many_it_names() {
    let dir = std::env::temp_dir().join(format!("fortec-vlen-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("vlen.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         \n\
         \n\
         fn counted(xs: &i64[]): i64 { xs.len }\n\
         // And summed by its own length rather than by a number handed beside\n\
         // it, which is what every routine over a view had to take.\n\
         fn summed(xs: &i64[]): i64 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < xs.len {\n\
         \x20       t = t + xs[i]\n\
         \x20       i = i + 1\n\
         \x20   }\n\
         \x20   t\n\
         }\n\
         \n\
         %test\n\
         fn a_view_knows_how_many_it_names() {\n\
         \x20   let a: i64[4] = [1, 2, 3, 4]\n\
         \x20   assert_eq(&counted(&a), &4, \"the whole of it\")\n\
         \x20   assert_eq(&counted(&a[1..3]), &2, \"and a slice of it\")\n\
         \x20   assert_eq(&summed(&a), &10, \"walked by its own length\")\n\
         \x20   assert_eq(&summed(&a[1..3]), &5, \"and the slice too\")\n\
         \x20   let none: i64[4] = [9, 9, 9, 9]\n\
         \x20   assert_eq(&summed(&none[2..2]), &0, \"an empty one names none\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "vlen");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a view was meant to know its length:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 1 test"), "{}", said);
}

// ---- A cast of a reference -------------------------------------------------------

// "A reference stands for the place it refers to and is read, called, indexed
// and reached into exactly as that place is" (§3) -- and a cast had been the one
// thing that took the reference itself. `r as i64` on a `&i32` widened the
// *address*, and said nothing about it.
//
// What that looked like is worth writing down, because it is why this is a test
// and not a note: an assertion reported `left: 140721311482340` where a 5 was
// meant to be. The value was never wrong; the thing being widened was.
//
// A `ptr` is deliberately not read through, and the second test is that half:
// "`p as i64`, `n as ptr u8` and `p as ptr i32` all lower to a conversion of the
// width they are" (§8), so an address is exactly what a `ptr` cast is about.
#[test]
fn a_reference_is_cast_as_the_place_it_refers_to() {
    let dir = std::env::temp_dir().join(format!("fortec-cast-src-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("a directory");
    let root = dir.join("cast.ft");
    std::fs::write(
        &root,
        "import test::assert_eq;\n\
         import mem::room;\n\
         \n\
         fn widened(r: &i32): i64 { r as i64 }\n\
         fn narrowed(r: &i64): i32 { r as i32 }\n\
         fn floated(r: &i64): f64 { r as f64 }\n\
         \n\
         %test\n\
         fn a_cast_reads_through_the_reference() {\n\
         \x20   let small: i32 = 7\n\
         \x20   let big: i64 = 300\n\
         \x20   assert_eq(&widened(&small), &7, \"the value and not its address\")\n\
         \x20   assert_eq(&narrowed(&big), &300, \"and the other way round\")\n\
         \x20   assert_eq(&floated(&big), &300.0, \"and into a float\")\n\
         }\n\
         \n\
         %test\n\
         fn a_pointer_is_still_cast_as_the_address_it_is() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 9\n\
         \x20   // Out to a number and back, which is only a round trip if what\n\
         \x20   // went out was the address.\n\
         \x20   unsafe let held = p as i64\n\
         \x20   unsafe let back = held as ptr i64\n\
         \x20   unsafe let read = back[0]\n\
         \x20   assert_eq(&read, &9, \"a `ptr` keeps its address\")\n\
         }\n",
    )
    .expect("a file");

    let held = ran(&root, "cast");
    let _ = std::fs::remove_dir_all(&dir);
    let Some((ok, said)) = held else { return };

    assert!(ok, "a cast was meant to read through a reference:\n{}", said);
    assert!(said.contains("0 failed"), "{}", said);
    assert!(said.contains("running 2 tests"), "{}", said);
}
