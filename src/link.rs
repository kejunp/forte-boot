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

// What the shim is, given the entry. Kept apart from running the tools so that
// what is handed to the C compiler can be looked at, and asserted on.
pub fn shim(entry: &Entry) -> String {
    if entry.answers {
        format!(
            "extern void __rt_init(void);\n\
             extern long {sym}(void);\n\
             int main(void) {{\n\
             \x20   __rt_init();\n\
             \x20   return (int){sym}();\n\
             }}\n",
            sym = entry.symbol
        )
    } else {
        format!(
            "extern void __rt_init(void);\n\
             extern void {sym}(void);\n\
             int main(void) {{\n\
             \x20   __rt_init();\n\
             \x20   {sym}();\n\
             \x20   return 0;\n\
             }}\n",
            sym = entry.symbol
        )
    }
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
    entry: &Entry,
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
    // once must not be one another's.
    let dir = std::env::temp_dir();
    let tag = format!("fortec-{}", std::process::id());
    let at_s = dir.join(format!("{}.s", tag));
    let at_c = dir.join(format!("{}.c", tag));

    let written = std::fs::write(&at_s, asm).and_then(|()| std::fs::write(&at_c, shim(entry)));
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
