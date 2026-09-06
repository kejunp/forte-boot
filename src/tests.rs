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
    built(root, what, true)
}

// And the same for an ordinary build, which starts at the suite's own `main`
// rather than at a runner over its tests. What a program *does* is the only way
// to ask some things -- whether a `never` really does stop one, above all.
fn ran_program(root: &Path, what: &str) -> Option<(bool, String)> {
    built(root, what, false)
}

fn built(root: &Path, what: &str, tests: bool) -> Option<(bool, String)> {
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
         import fmt::int;\n\
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
         \x20   assert_eq(int(sum(&a[1..4], 3)), int(9), \"2 and 3 and 4\")\n\
         \x20   assert_eq(int(sum(&a[0..8], 8)), int(36), \"the whole of it\")\n\
         \x20   assert_eq(int(sum(&a[7..8], 1)), int(8), \"the last one alone\")\n\
         }\n\
         \n\
         %test\n\
         fn a_slice_that_writes_leaves_the_rest_alone() {\n\
         \x20   var a: i64[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   bump(*a[2..4], 2)\n\
         \x20   assert_eq(int(a[2]), int(103), \"the first it names\")\n\
         \x20   assert_eq(int(a[3]), int(104), \"and the last\")\n\
         \x20   assert_eq(int(a[1]), int(2), \"the one before is untouched\")\n\
         \x20   assert_eq(int(a[4]), int(5), \"and the one after\")\n\
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
         import fmt::int;\n\
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
         \x20   assert_eq(int(sum(s, 4)), int(100), \"through a name that says so\")\n\
         \x20   assert_eq(int(sum(&a, 4)), int(100), \"and at a parameter that does\")\n\
         }\n\
         \n\
         %test\n\
         fn a_writing_reference_to_an_array_writes_through_the_view() {\n\
         \x20   var a: i64[4] = [10, 20, 30, 40]\n\
         \x20   bump(*a, 4)\n\
         \x20   assert_eq(int(a[0]), int(11), \"the first\")\n\
         \x20   assert_eq(int(a[3]), int(41), \"and the last\")\n\
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
         \x20   println(\"BEFORE\")\n\
         \x20   let held = checked(-1)\n\
         \x20   println(\"AFTER\")\n\
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
         import fmt::int;\n\
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
         \x20   assert_eq(int(twice(&p)), int(42), \"P answers Show\")\n\
         \x20   assert_eq(int(twice(&q)), int(105), \"and so does Q, differently\")\n\
         }\n\
         \n\
         %test\n\
         fn a_generic_may_hand_its_own_parameter_on() {\n\
         \x20   let p = P { x: 21 }\n\
         \x20   let q = Q { y: 5 }\n\
         \x20   assert_eq(int(through(&p)), int(252), \"42 and 21 by ten\")\n\
         \x20   assert_eq(int(through(&q)), int(120), \"105 and 5 and ten\")\n\
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
         import fmt::int;\n\
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
         \x20   assert_eq(int(less(9, 4)), int(5), \"the first less the second\")\n\
         \x20   let seven = |p1: i64, p2: i64, p3: i64, p4: i64, p5: i64, p6: i64, p7: i64| \
         p7 - p1\n\
         \x20   assert_eq(int(seven(1, 0, 0, 0, 0, 0, 8)), int(7), \"past the registers\")\n\
         }\n\
         \n\
         %test\n\
         fn a_capture_is_read_through_the_environment() {\n\
         \x20   let n = 5\n\
         \x20   let add = |x: i64| x + &n\n\
         \x20   assert_eq(int(add(1)), int(6), \"what the frame outside holds\")\n\
         \x20   assert_eq(int(add(2)), int(7), \"and it is still there\")\n\
         }\n\
         \n\
         %test\n\
         fn a_capture_that_is_assigned_to_is_written_through() {\n\
         \x20   var n = 0\n\
         \x20   let bump = |d: i64| n = n + d\n\
         \x20   bump(3)\n\
         \x20   bump(4)\n\
         \x20   assert_eq(int(n), int(7), \"the name outside, not a copy of it\")\n\
         }\n\
         \n\
         %test\n\
         fn a_move_closure_outlives_the_frame_it_took_from() {\n\
         \x20   let f = made()\n\
         \x20   assert_eq(int(churn(1, 2, 3)), int(55550), \"something else uses the stack\")\n\
         \x20   assert_eq(int(f(1)), int(101), \"and what it took is still what it took\")\n\
         }\n\
         \n\
         %test\n\
         fn a_declared_fn_and_a_closure_are_called_the_same_way() {\n\
         \x20   assert_eq(int(twice(ten, 1)), int(21), \"a fn with no environment\")\n\
         \x20   let k = 10\n\
         \x20   assert_eq(int(twice(|x: i64| x + &k, 1)), int(21), \"and one with\")\n\
         }\n\
         \n\
         %test\n\
         fn a_body_in_braces_is_a_block() {\n\
         \x20   var n = 1\n\
         \x20   let step = |d: i64| { n = n * d }\n\
         \x20   step(6)\n\
         \x20   assert_eq(int(n), int(6), \"one statement, and it ran\")\n\
         \x20   let twice_over = |x: i64| {\n\
         \x20       let a = x * 2\n\
         \x20       a + 1\n\
         \x20   }\n\
         \x20   assert_eq(int(twice_over(5)), int(11), \"and its value is the tail\")\n\
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
         import fmt::{int, truth};\n\
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
         \x20   assert_eq(int(n.get()), int(7), \"the i64 instance\")\n\
         \x20   assert_eq(truth(t.get()), truth(true), \"and the bool one\")\n\
         \x20   assert_eq(int(n.again()), int(7), \"one member reaching another\")\n\
         }\n\
         \n\
         %test\n\
         fn a_parameter_only_the_receiver_names_is_still_found() {\n\
         \x20   let p: Pair<i64, bool> = Pair { a: 3, b: false }\n\
         \x20   assert_eq(int(p.first()), int(3), \"and `B` came from the receiver\")\n\
         }\n\
         \n\
         %test\n\
         fn an_impls_parameter_reaches_through_a_generic_fn() {\n\
         \x20   let n: Box<i64> = Box { v: 41 }\n\
         \x20   assert_eq(int(through(&n)), int(41), \"a `T` handed on to a method\")\n\
         }\n\
         \n\
         %test\n\
         fn an_impl_with_no_parameters_still_works() {\n\
         \x20   var c = Counter { n: 0 }\n\
         \x20   c.bump(5)\n\
         \x20   c.bump(2)\n\
         \x20   assert_eq(int(c.read()), int(7), \"a `*self` that wrote through\")\n\
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
         import fmt::int;\n\
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
         \x20   assert_eq(int(indexed(p)), int(9), \"through an index\")\n\
         \x20   assert_eq(int(dereffed(p)), int(9), \"through a `deref`\")\n\
         \x20   assert_eq(int(blocked(p)), int(9), \"through a block\")\n\
         \x20   assert_eq(int(twice(p)), int(9), \"and through the word twice\")\n\
         }\n\
         \n\
         %test\n\
         fn a_guarded_write_still_happens() {\n\
         \x20   unsafe let p = room(16) as ptr i64\n\
         \x20   unsafe p[0] = 1\n\
         \x20   unsafe p[0] = 2\n\
         \x20   assert_eq(int(indexed(p)), int(2), \"the last write is what is there\")\n\
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
