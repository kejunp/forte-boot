// The listing made into something an assembler will take.
//
//     MIR (linear) -> regalloc -> text     a page for a person
//                              -> asm      a page for `as`
//
// `mir::text` says what it is and is not: "It is a listing and not an
// assembler's input, and the difference is the point." This is the other
// answer to the same question. Everything about a body is already decided by
// the time either of them runs -- which register, which offset, how many bytes
// -- so what is left is the difference between writing `copy.24` and writing
// the instructions a machine has that come to the same thing.
//
// Two machines so far, and the parts that are the same for both are here; the
// parts that are not are in a file each, because they are not nearly the same.
// x86-64 has an instruction that adds a value in memory to a register and
// aarch64 has nothing of the kind; one of them writes the destination first
// and the other writes it last. A single emitter parameterised over that would
// be a file about the differences rather than a file about either machine. x86-64 has an instruction
// that adds a value in memory to a register and RISC-V has no instruction that
// touches memory except a load and a store; aarch64 writes the destination
// first and x86-64 writes it last; one of the three has a link register and two
// of them do not. A single emitter parameterised over that would be a file
// about the differences rather than a file about any of the machines.
//
// **What is shared is the frame and the calling convention**, and those really
// are shared. Every one of the three keeps a frame pointer, puts the callee-
// saved registers it uses just under it, puts the slots under those, and keeps
// the stack aligned to sixteen. Every one of them takes its arguments in a
// list of registers and answers in one. So `Body` below works all of that out
// once, and what a machine's own file does is write it down.
//
// **The prologue and the epilogue arrive here.** `mir::regalloc` says it does
// not write them and says why: they are instructions around a body rather than
// decisions about it, and they belong with whatever turns a listing into an
// object file. This is that.
//
// **What is not here is a peephole.** Nothing folds an offset into an
// addressing mode, nothing turns a multiply by eight into a shift, nothing
// notices that a value was already in the register it is being moved to. The
// output is what the MIR said, instruction for instruction, and it is slow in
// exactly the way that is easy to see. That is the right first back end: it
// can be read against the listing line by line, and the listing can be read
// against the source.

use std::fmt::Write;

use super::linear::{linearise, Linear};
use super::machine::{Class, Machine, Reg};
use super::mir_nodes::*;
use super::regalloc::{allocate, Allocation, Where};
use super::text;

pub mod aarch64;
pub mod x86_64;

// Where a virtual register turned out to live.
//
// `Where` says the same thing in the allocator's terms -- a register or a slot
// number -- and this says it in the emitter's: a slot number is not an address
// and how far below the frame pointer it sits is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Site {
    In(Reg),
    // How far below the frame pointer, in bytes.
    At(usize),
    // Nothing writes it and nothing reads it. An instruction that makes one is
    // still emitted -- it may have an effect -- and its answer goes nowhere.
    Nowhere,
}

// Everything a machine's own file needs to know about one body.
pub struct Body<'a> {
    pub held:    &'a Linear,
    pub at:      &'a Allocation,
    pub m:       Machine,
    // How far below the frame pointer each slot begins, and how big the whole
    // frame is once the saved registers and the alignment are in it.
    pub offsets: Vec<usize>,
    pub frame:   usize,
    // The callee-saved registers this body writes, which are exactly the ones
    // it has to put back. A body that touches none saves none.
    pub saved:   Vec<Reg>,
    // Which body of the program this is, for numbering its labels. A label is
    // a name in the whole file and a block number is a name in one body, so
    // without this every body's `.L1` would be the same `.L1`.
    pub index:   usize,
}

impl<'a> Body<'a> {
    pub fn new(held: &'a Linear, at: &'a Allocation, m: Machine, index: usize) -> Body<'a> {
        let saved = kept(held, at, m);
        // The saved registers sit directly under the frame pointer and the
        // slots under them, so that a slot's offset does not depend on how
        // many registers turned out to be worth saving until now.
        let above = saved.len() * m.word;
        let (offsets, size) = text::frame(&held.frame, m);
        let offsets: Vec<usize> = offsets.iter().map(|held| held + above).collect();
        let stack = m.stack.max(1);
        Body {
            held,
            at,
            m,
            offsets,
            frame: (above + size).div_ceil(stack) * stack,
            saved,
            index,
        }
    }

    // Where a virtual register ended up.
    pub fn site(&self, reg: MIRRegId) -> Site {
        match self.at.of(reg) {
            Where::In(held) => Site::In(held),
            Where::Spilled(slot) => {
                Site::At(self.offsets.get(slot).copied().unwrap_or(self.m.word))
            }
            Where::Nowhere => Site::Nowhere,
        }
    }

    // How wide a value is, which is what says the width of the instruction
    // that moves it. Never nought and never more than a word: anything bigger
    // than a word is held by its address, and an address is a word.
    pub fn bytes(&self, reg: MIRRegId) -> usize {
        let held = self.held.regs.get(reg).map_or(self.m.word, |one| one.bytes);
        held.clamp(1, self.m.word)
    }

    pub fn class(&self, reg: MIRRegId) -> Class {
        self.held.regs.get(reg).map_or(Class::Int, |one| one.class)
    }

    // How far below the frame pointer one of the saved registers goes.
    pub fn saved_at(&self, which: usize) -> usize {
        (which + 1) * self.m.word
    }
}

// The callee-saved registers a body writes.
//
// Only the ones it writes: saving a register the body never touches is two
// instructions for nothing, and the list is short enough that working it out
// is a walk over the allocation rather than anything cleverer.
fn kept(held: &Linear, at: &Allocation, m: Machine) -> Vec<Reg> {
    let mut out = Vec::new();
    for reg in 0..held.regs.len() {
        if let Where::In(one) = at.of(reg) {
            if m.keeps(one) && !out.contains(&one) {
                out.push(one);
            }
        }
    }
    out
}

// ---- Where the arguments go ------------------------------------------------

// Which register each argument of a call goes in, by the order of the two
// files. The third integer argument goes in the third integer register
// however many floats came before it, which is what `Machine::passing` means
// by keeping two lists.
//
// `None` where a call has more arguments of a class than there are registers
// for. Nothing here puts one on the stack -- see `render`, which refuses such
// a call rather than emitting one that would run and be wrong.
pub fn passing(m: Machine, classes: &[Class]) -> Vec<Option<Reg>> {
    let (mut ints, mut floats) = (0usize, 0usize);
    classes
        .iter()
        .map(|class| {
            let (which, held) = match class {
                Class::Int => (&mut ints, m.args),
                Class::Float => (&mut floats, m.fargs),
            };
            let out = held.get(*which).copied();
            *which += 1;
            out
        })
        .collect()
}

// ---- Moving several registers at once --------------------------------------

// The order to make a set of moves in so that none of them writes over
// something a later one still wants.
//
// This is the same question `mir::linear` answers for phis, and the answer is
// the same shape: a move whose destination nothing else reads may go now, and
// what is left when there are no such moves is a cycle. The difference is that
// here the registers are the machine's, so what a cycle is broken with is the
// scratch register rather than a fresh one -- there are no fresh ones left.
//
// **What is saved is the destination, not the source.** A move writes over its
// destination, and the register that is about to be lost is exactly the one
// something else still wants to read. Saving the source instead saves a
// register nothing was going to lose, and the swap it was meant to make comes
// out as two copies of one value -- which is a wrong answer, not a crash, and
// only in a body with enough arguments to have a cycle at all.
//
// **And what was saved is read back in its turn, not at once.** Round a cycle
// of three, the move that wanted the saved register is itself a register a
// third move is waiting on; reading the scratch back the moment it is
// available writes over that third move's source. So the move becomes an
// ordinary one with the scratch as its source and waits like any other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    Move { to: Reg, from: Reg },
    Save(Reg),
    Restore(Reg),
}

pub fn ordered(moves: &[(Reg, Reg)]) -> Vec<Step> {
    // `None` for a source means the scratch register: the move wanted a
    // register whose old value has been put aside.
    let mut left: Vec<(Reg, Option<Reg>)> = moves
        .iter()
        .filter(|(to, from)| to != from)
        .map(|(to, from)| (*to, Some(*from)))
        .collect();
    let mut out = Vec::new();

    while !left.is_empty() {
        // Anything whose destination is not still wanted as a source.
        let ready: Vec<usize> = left
            .iter()
            .enumerate()
            .filter(|(_, (to, _))| !left.iter().any(|(_, from)| *from == Some(*to)))
            .map(|(at, _)| at)
            .collect();

        if ready.is_empty() {
            // Every one that is left is in a cycle. Put aside what the first
            // of them is about to write over, and say that whatever wanted to
            // read that register reads the scratch -- but do not read it back
            // yet. The move that does is now an ordinary one, and it goes when
            // its own turn comes: doing it here would write over a register a
            // third move round the cycle still wants.
            let (to, _) = left[0];
            out.push(Step::Save(to));
            for held in left.iter_mut() {
                if held.1 == Some(to) {
                    held.1 = None;
                }
            }
            continue;
        }

        for at in ready.iter().rev() {
            let (to, from) = left[*at];
            match from {
                Some(one) => out.push(Step::Move { to, from: one }),
                None => out.push(Step::Restore(to)),
            }
            left.remove(*at);
        }
    }
    out
}

// ---- The whole program -----------------------------------------------------

// Every body, and the pool under them.
//
// The answer is the text and everything that could not be written. A body with
// a complaint against it is still emitted, minus the instruction that could
// not be: what comes out is assembly that is wrong in a way something said out
// loud, rather than assembly that is wrong.
pub fn render(p: &MIRProgram, m: Machine) -> (String, Vec<String>) {
    let mut out = String::new();
    let mut said = Vec::new();

    for (index, body) in p.bodies.iter().enumerate() {
        let mut held = linearise(body);
        let at = allocate(&mut held, m);
        let one = Body::new(&held, &at, m, index);
        let (text, complaints) = match m.name {
            "x86-64" => x86_64::body(&one),
            "aarch64" => aarch64::body(&one),
            // A machine with no file of its own. Emitting one machine's
            // instructions under another's name would assemble and would not
            // run, so what comes out is nothing and a line saying so.
            _ => (
                String::new(),
                vec![format!("{}: nothing here emits for {}", one.held.symbol, m.name)],
            ),
        };
        out.push_str(&text);
        said.extend(complaints);
    }

    // The linker asks. Without it an object is assumed to want an executable
    // stack, which is a thing nothing here wants and every linker now warns
    // about.
    let _ = writeln!(out, "\t.section\t.note.GNU-stack, \"\", @progbits");

    if !p.pool.is_empty() {
        let text = match m.name {
            "aarch64" => aarch64::pool(&p.pool),
            _ => x86_64::pool(&p.pool),
        };
        out.push_str(&text);
    }
    (out, said)
}

// ---- What every machine's file writes the same way -------------------------

// A block's label.
//
// Local to the object -- an assembler treats a label beginning `.L` as one it
// need not keep -- and numbered by the body as well as the block. The block
// number alone is what the listing calls it, and it is a name inside one body:
// every body has a `.L1`, and in one file they would all be the same one.
pub fn label(b: &Body, at: MIRBlockId) -> String {
    format!(".LB{}_{}", b.index, at)
}

// A symbol an assembler will take.
//
// The names `sema::names::Mangler` builds hold whatever the type spelling held
// -- `__F2rt4keep9&rt::Node` is a real one -- and an ampersand is not a
// character a symbol may have. Nor is a colon, a bracket, an angle, a comma or
// a space, and the mangling puts all six in.
//
// So everything outside letters, digits and an underscore becomes a dot and
// two hexadecimal digits. A dot is itself escaped, which is what makes the
// mapping one-to-one: an escape always begins with a dot and a dot is never
// anything else, so no two names can come out the same. `&` becomes `.26` and
// `::` becomes `.3a.3a`, which is longer than it looks it should be and is
// readable enough that a linker error still says which fn it was about.
//
// The mangling itself is left alone. It is the compiler's own scheme, it is
// what `--emit mir` prints and what `mir::runtime` builds a release's name
// with, and narrowing its alphabet to please an assembler would be letting the
// last pass in the compiler decide what every pass before it may call things.
pub fn symbol(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for held in name.chars() {
        if held.is_ascii_alphanumeric() || held == '_' {
            out.push(held);
        } else {
            for byte in held.to_string().as_bytes() {
                out.push_str(&format!(".{:02x}", byte));
            }
        }
    }
    out
}

// The bytes of a pool entry, as directives. One `.byte` per byte rather than
// anything cleverer: a descriptor is not a string and a string is not aligned,
// and the one form that is right for both is the dull one.
pub fn bytes_of(held: &MIRConstant) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{}:", symbol(&held.symbol));
    for line in held.bytes.chunks(16) {
        let held: Vec<String> = line.iter().map(|byte| byte.to_string()).collect();
        let _ = writeln!(out, "\t.byte\t{}", held.join(", "));
    }
    if held.bytes.is_empty() {
        let _ = writeln!(out, "\t.zero\t1");
    }
    out
}

// Whether a body holds something no machine's file here can emit.
//
// The vector four. They reach the MIR only where `sir::opt` widened something,
// which is `-O3` and nothing below it, and emitting one properly is a fourth
// project: what a vector register *is* differs between these three machines far
// more than an integer one does, and RISC-V's baseline has none at all. So a
// body holding one is refused by name rather than emitted wrongly.
pub fn refuses(held: &Linear) -> Vec<String> {
    let mut out = Vec::new();
    for line in &held.lines {
        let super::linear::Line::Inst(inst) = line else { continue };
        let what = match inst.kind {
            MIRInstKind::Pack(_) => "a vector built by hand",
            MIRInstKind::Lane { .. } => "one lane of a vector",
            MIRInstKind::VecLoad { .. } => "a vector read",
            MIRInstKind::VecStore { .. } => "a vector written",
            _ => continue,
        };
        let said = format!(
            "{}: {} is not emitted -- widening is on, and nothing here writes vectors",
            held.symbol, what
        );
        if !out.contains(&said) {
            out.push(said);
        }
    }
    out
}

// ---- Handing it to an assembler --------------------------------------------

// Whether an assembler took it, and what it said where it did not.
//
// This is what the tests of the three machines' files rest on, and it is worth
// saying why rather than only asserting on the text. Every one of these
// emitters can write a line that reads perfectly and is not an instruction: a
// register named at a width the mnemonic does not allow, two operands the
// right way round for the other machine, a mnemonic that exists on a machine
// this is not. None of those is a thing a test written against the text would
// catch, because the text is what the file meant to write. An assembler is the
// only reader that knows.
//
// `None` where there is no assembler for that machine, and the test passes.
// That is worse than an answer and better than a suite that only runs where a
// cross toolchain happens to be installed.
#[cfg(test)]
pub fn tried(text: &str, triple: &str) -> Option<String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);

    let at = std::env::temp_dir().join(format!(
        "fortec-{}-{}-{}.s",
        triple,
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    if std::fs::write(&at, text).is_err() {
        return None;
    }
    let held = std::process::Command::new("clang")
        .args([&format!("--target={}", triple), "-c", "-o", "/dev/null"])
        .arg(&at)
        .output();
    let _ = std::fs::remove_file(&at);

    let Ok(held) = held else { return None };
    if held.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&held.stderr).trim().to_string())
}

#[cfg(test)]
mod tests;
