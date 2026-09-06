// The assembly made into something that runs.
//
//     MIR -> asm      a page for `as`
//         -> link     a file the kernel will start
//
// `mir::asm` says it writes "a page for `as`" and stops there, which was the
// right place to stop while nothing could say what to do with the page. This
// is what does something with it: an assembler is run over it, the runtime is
// put beside it, and a linker is asked for a file.
//
// **The work here is not compilation.** Every decision about the program was
// taken upstream and none of them is revisited; what is left is knowing which
// tool to run, what to hand it, and what to say when it refuses. That is why
// this is one small file of process invocation rather than a back end.
//
// **Why there is an entry at all.** The runtime's `__rt_init` says it is
// "called once, from the program's outermost frame", and gives the reason: the
// collector's roots start at the bottom of the mutator's stack, and nothing
// inside can work out where that is. Nothing in the language calls it -- a
// Forte `main` is a fn like any other and knows nothing about a collector. So
// something has to stand between the kernel's entry and the program's, and
// that something is written here.
//
// It is written in C and not in assembly, though this compiler can write
// assembly for three machines. Three shims would be three chances to write a
// prologue wrongly, and the difference between them would be nothing to do
// with anything the language decides -- while one line of C is one line on
// every machine, and the compiler that assembles the output is already there
// to compile it.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::mir::machine::Machine;

// The program's own entry: what the linker calls it, and whether what it hands
// back is a number.
//
// A `main` returning `i32` is a process exit status and a `main` returning
// `null` is not: the register the answer would have been in holds whatever the
// body last put there, and handing that to the kernel would make an exit code
// out of a leftover. So the shim reads the answer only where there is one, and
// exits zero where there is not.
pub struct Entry {
    pub symbol:  String,
    pub answers: bool,
}

// One `%test`: what it is called where it was written, and what it compiled to.
//
// The name is for the reader and is never the symbol -- a mangled name carries
// the parameter types and the module path spelled as lengths, and a runner that
// printed one would be asking the reader to decode it.
pub struct Test {
    pub name:   String,
    pub symbol: String,
}

// What the program the linker makes begins at: the `main` somebody wrote, or a
// runner over the tests they wrote instead.
//
// Two shapes and not a flag, because they have nothing in common past
// `__rt_init`: one calls a single fn and may hand its answer to the kernel, and
// the other calls however many and hands back nothing.
pub enum Start {
    Program(Entry),
    Tests(Vec<Test>),
}

// What the shim is, given what the program starts at. Kept apart from running
// the tools so that what is handed to the C compiler can be looked at, and
// asserted on.
pub fn shim(start: &Start) -> String {
    match start {
        Start::Program(entry) => program_shim(entry),
        Start::Tests(tests) => tests_shim(tests),
    }
}

fn program_shim(entry: &Entry) -> String {
    // `argc` and `argv` come from the kernel through this and nowhere else,
    // and they are handed over before `__rt_init` so that the first line the
    // program runs can already read them. `std/env.ft` is what reads them.
    //
    // `main` still takes nothing, which is §1's rule and not an omission: a
    // `main` with parameters is mangled with them and is not the one a process
    // starts at. What was missing was somewhere for an argument to come from,
    // and this is it.
    let head = "extern void __rt_init(void);\n\
                extern void __rt_args(long, char **);\n";
    if entry.answers {
        format!(
            "{head}\
             extern long {sym}(void);\n\
             int main(int argc, char **argv) {{\n\
             \x20   __rt_args((long)argc, argv);\n\
             \x20   __rt_init();\n\
             \x20   return (int){sym}();\n\
             }}\n",
            head = head,
            sym = entry.symbol
        )
    } else {
        format!(
            "{head}\
             extern void {sym}(void);\n\
             int main(int argc, char **argv) {{\n\
             \x20   __rt_args((long)argc, argv);\n\
             \x20   __rt_init();\n\
             \x20   {sym}();\n\
             \x20   return 0;\n\
             }}\n",
            head = head,
            sym = entry.symbol
        )
    }
}

// The runner: `__rt_init`, then every test in the order they were collected,
// each between a `__rt_test_start` that clears what has failed and a
// `__rt_test_failed` that reads it back.
//
// A test fails by asserting something that does not hold (`std/test.ft`), and
// what that does is count itself rather than stop the test -- so the verdict
// cannot be read until the body has returned, and a test that fails four
// assertions is one failure here.
//
// The name goes out *before* the test runs and the stream is flushed, which is
// the other half of the design. An assertion cannot stop a test but a
// segmentation fault can, and a test that takes the process down leaves its own
// name as the last thing on the screen. A name printed afterwards would name
// every test but the one the reader is looking for.
//
// `<stdio.h>` rather than the bare `extern` declarations the other shim writes:
// that one needs two names and this one needs `printf`, `fflush` and `stdout`,
// and spelling a variadic and a `FILE *` out by hand would be three chances to
// disagree with the header that is already there.
fn tests_shim(tests: &[Test]) -> String {
    let mut out = String::from(
        "#include <stdio.h>\n\n\
         extern void __rt_init(void);\n\
         extern void __rt_test_start(void);\n\
         extern long __rt_test_failed(void);\n",
    );
    for test in tests {
        out.push_str(&format!("extern void {}(void);\n", test.symbol));
    }
    out.push_str("\nint main(void) {\n    __rt_init();\n    long passed = 0, failed = 0;\n");
    out.push_str(&format!(
        "    printf(\"\\nrunning {} test{}\\n\");\n",
        tests.len(),
        if tests.len() == 1 { "" } else { "s" }
    ));
    for test in tests {
        out.push_str(&format!(
            "    printf(\"test {} ... \");\n             \x20   fflush(stdout);\n             \x20   __rt_test_start();\n             \x20   {}();\n             \x20   if (__rt_test_failed()) {{ failed++; printf(\"FAILED\\n\"); }}\n             \x20   else {{ passed++; printf(\"ok\\n\"); }}\n",
            quoted(&test.name),
            test.symbol
        ));
    }
    // The verdict, and then the same thing again as a status: whatever ran this
    // is not reading the words.
    out.push_str(
        "\n    printf(\"\\ntest result: %s. %ld passed; %ld failed\\n\",\n         \x20          failed ? \"FAILED\" : \"ok\", passed, failed);\n         \x20   return failed ? 1 : 0;\n}\n",
    );
    out
}

// A name as C spells a string. Nothing the mangler makes needs it -- a Forte
// path is letters, digits, `_` and `::` -- and it is escaped anyway, because
// that is a fact about the mangler and not a promise this file should rest on.
fn quoted(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        match c {
            '"' | '\\' => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 => out.push_str(&format!("\\{:03o}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

// Which machine this is running on, said the way `Machine::name` says it.
//
// The comparison is against the machine and not against a triple because the
// only question here is whether the output can be linked at all: a cross
// assembler is common and a cross runtime is not -- the archive beside this
// compiler was built for the machine that built it, and no flag makes it
// something else.
fn here() -> &'static str {
    match std::env::consts::ARCH {
        "x86_64" => "x86-64",
        "aarch64" => "aarch64",
        "riscv64" => "riscv64",
        other => other,
    }
}

// The runtime archive: beside this compiler, which is where `cargo` puts it.
//
// `fortec` and `fortec-rt` are default members of one workspace, so a plain
// `cargo build` writes both into the same directory and the archive is the
// executable's neighbour. Nothing searches any further: a runtime found
// somewhere else would be one whose version nothing checked.
fn runtime_beside() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let at = exe.parent()?.join("libfortec_rt.a");
    at.is_file().then_some(at)
}

// Assemble, link, and leave an executable at `out`.
//
// `Err` carries what to tell the reader, already worded for them: a linker's
// own message where there is one, and a sentence of this compiler's where the
// refusal is this compiler's.
pub fn link(
    asm: &str,
    start: &Start,
    m: Machine,
    out: &Path,
    runtime: Option<&Path>,
) -> Result<(), String> {
    if m.name != here() {
        return Err(format!(
            "cannot link for {} on {}: the runtime beside this compiler was built \
             for {}, and no flag makes it something else.\n\
             `--emit asm` writes the assembly, which is the part that does cross",
            m.name,
            here(),
            here()
        ));
    }

    let archive = match runtime {
        Some(given) if given.is_file() => given.to_path_buf(),
        Some(given) => {
            return Err(format!("no runtime archive at {}", given.display()));
        }
        None => match runtime_beside() {
            Some(at) => at,
            None => {
                return Err(
                    "no `libfortec_rt.a` beside this compiler. `cargo build` makes one \
                     -- the runtime is a member of the same workspace -- or `--runtime` \
                     says where another is"
                        .to_string(),
                );
            }
        },
    };

    // Two files the reader never asked for, so they go where such things go and
    // are taken away again. The pid is in the name because two compilations at
    // once must not be one another's -- and a count after it because "at once"
    // includes twice inside one process, which is what a test binary linking
    // two programs on two threads does. The pid alone was enough until there
    // was something that did.
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir();
    let tag = format!(
        "fortec-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    );
    let at_s = dir.join(format!("{}.s", tag));
    let at_c = dir.join(format!("{}.c", tag));

    let written = std::fs::write(&at_s, asm).and_then(|()| std::fs::write(&at_c, shim(start)));
    if let Err(why) = written {
        let _ = std::fs::remove_file(&at_s);
        let _ = std::fs::remove_file(&at_c);
        return Err(format!("could not write what the linker was to read: {}", why));
    }

    // `cc` and not `ld`: what the runtime needs beside it -- the C library, the
    // threads, the unwinder Rust's own code expects -- is what a C compiler
    // driver already knows to pass on, and spelling that list out here would be
    // spelling out one that differs per system.
    let held = Command::new("cc")
        .arg(&at_c)
        .arg(&at_s)
        .arg(&archive)
        .arg("-o")
        .arg(out)
        .args(["-lpthread", "-ldl", "-lm"])
        .output();

    let _ = std::fs::remove_file(&at_s);
    let _ = std::fs::remove_file(&at_c);

    match held {
        Err(why) => Err(format!("could not run `cc`: {}", why)),
        Ok(held) if held.status.success() => Ok(()),
        Ok(held) => Err(String::from_utf8_lossy(&held.stderr).trim().to_string()),
    }
}

#[cfg(test)]
mod tests;
