// x86-64, in the syntax GNU `as` takes without being told otherwise.
//
// AT&T, so the source comes first and the destination second, a register wears
// a `%` and an immediate a `$`, and the width of an instruction is a letter on
// the end of it rather than a fact about the operands. That last one is why
// `suffix` is called as often as it is: this machine has no idea how wide an
// addition is unless the mnemonic says.
//
// **A register's name depends on its width.** `%rax`, `%eax`, `%ax` and `%al`
// are one register, and writing the wrong one is not an error an assembler
// catches -- it assembles, and it works on the wrong number of bytes. So a
// register is never written out here; `named` is asked for it, and it is asked
// with the width the value actually is.
//
// **A value is kept at its own width and no wider.** A four-byte value in a
// register leaves the top four bytes as whatever was there, and nothing reads
// them: every instruction over that value is a four-byte instruction. The
// alternative -- keeping everything sign-extended to eight -- means an extra
// instruction after every narrow load, and the MIR already says how wide each
// value is, so there is nothing to be gained by not believing it.
//
// **Two of this machine's instructions want particular registers**, and both
// are worked around the same way: what is in the way is pushed, the
// instruction is given what it wants, the answer is put somewhere neutral, and
// what was pushed is put back. A division wants the dividend in `rdx:rax` and
// writes both; a shift wants its count in `cl`. Neither register is one the
// allocator knows to keep clear, so neither can simply be used.
//
// That is three or four instructions of overhead on every division and every
// shift, and it is the price of an allocator that does not model fixed
// registers. Teaching it to would be the right fix and it is a change to
// `mir::regalloc` rather than to this file.

use std::fmt::Write;

use super::super::linear::Line;
use super::super::machine::{Class, Reg};
use super::super::mir_nodes::*;
use super::{Body, Passed, Site, Step, label, ordered, passing, refuses, symbol};

// ---- Naming ----------------------------------------------------------------

fn suffix(bytes: usize) -> char {
    match bytes {
        1 => 'b',
        2 => 'w',
        4 => 'l',
        _ => 'q',
    }
}

// A register at a width. The eight the machine started with have names of
// their own at each width; the eight that came with the sixty-four-bit mode
// take a letter on the end.
fn named(reg: Reg, bytes: usize) -> String {
    if reg.class == Class::Float {
        return format!("%{}", reg.name);
    }
    let held: [&str; 4] = match reg.name {
        "rax" => ["rax", "eax", "ax", "al"],
        "rbx" => ["rbx", "ebx", "bx", "bl"],
        "rcx" => ["rcx", "ecx", "cx", "cl"],
        "rdx" => ["rdx", "edx", "dx", "dl"],
        "rsi" => ["rsi", "esi", "si", "sil"],
        "rdi" => ["rdi", "edi", "di", "dil"],
        "rbp" => ["rbp", "ebp", "bp", "bpl"],
        "rsp" => ["rsp", "esp", "sp", "spl"],
        _ => {
            let at = match bytes {
                1 => "b",
                2 => "w",
                4 => "d",
                _ => "",
            };
            return format!("%{}{}", reg.name, at);
        }
    };
    let at = match bytes {
        1 => 3,
        2 => 2,
        4 => 1,
        _ => 0,
    };
    format!("%{}", held[at])
}

// And the other way: a word the caller left *above* the frame pointer, which is
// the one address in this file that is not below it. It is spelled here and
// used in one place -- `params` copies such an argument into wherever the
// allocator put it, and after that it is an ordinary value with an ordinary
// site.
fn frame_at_above(off: usize) -> String {
    format!("{}(%rbp)", off)
}

fn frame_at(off: usize) -> String {
    format!("-{}(%rbp)", off)
}

// ---- Reading and writing ---------------------------------------------------

// Where a value is, as an operand. This machine takes a memory operand almost
// everywhere, so a spilled value mostly needs no instruction of its own.
fn place(b: &Body, reg: MIRRegId) -> String {
    match b.site(reg) {
        Site::In(held) => named(held, b.bytes(reg)),
        Site::At(off) => frame_at(off),
        Site::Nowhere => named(scratch(b, 0, b.class(reg)), b.bytes(reg)),
    }
}

fn scratch(b: &Body, which: usize, class: Class) -> Reg {
    let held = match class {
        Class::Int => b.m.scratch,
        Class::Float => b.m.fscratch,
    };
    held[which.min(held.len() - 1)]
}

// A value in a register, whatever it took to get it there. Used where an
// instruction will not take a memory operand in that position, and where both
// operands would otherwise be memory.
fn into(out: &mut String, b: &Body, reg: MIRRegId, sc: Reg) -> String {
    match b.site(reg) {
        Site::In(held) => named(held, b.bytes(reg)),
        _ => {
            let held = named(sc, b.bytes(reg));
            let _ = writeln!(out, "\t{}\t{}, {}", mov(b, reg), place(b, reg), held);
            held
        }
    }
}

// The same, at a width the caller names rather than the value's own. A store
// says how many bytes it writes and that is the width the operand has to be
// written at, whatever the register was called a moment ago.
fn read_at(out: &mut String, b: &Body, reg: MIRRegId, sc: Reg, bytes: usize) -> String {
    match b.site(reg) {
        Site::In(held) => named(held, bytes),
        _ => {
            let what = match b.class(reg) {
                Class::Float => if bytes <= 4 { "movss".into() } else { "movsd".into() },
                Class::Int => format!("mov{}", suffix(bytes)),
            };
            let held = named(sc, bytes);
            let _ = writeln!(out, "\t{}\t{}, {}", what, place(b, reg), held);
            held
        }
    }
}

// The move that carries a value of this register's width and file.
fn mov(b: &Body, reg: MIRRegId) -> String {
    match b.class(reg) {
        Class::Float => if b.bytes(reg) <= 4 { "movss".into() } else { "movsd".into() },
        Class::Int => format!("mov{}", suffix(b.bytes(reg))),
    }
}

// Where to compute an answer, and what has to happen afterwards. A destination
// in a register is written straight into; one in the frame is computed in the
// scratch register and stored.
fn writing(b: &Body, def: MIRRegId, sc: Reg) -> (String, Option<usize>) {
    match b.site(def) {
        Site::In(held) => (named(held, b.bytes(def)), None),
        Site::At(off) => (named(sc, b.bytes(def)), Some(off)),
        Site::Nowhere => (named(sc, b.bytes(def)), None),
    }
}

fn stored(out: &mut String, b: &Body, def: MIRRegId, held: &str, back: Option<usize>) {
    if let Some(off) = back {
        let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), held, frame_at(off));
    }
}

// ---- One body --------------------------------------------------------------

pub fn body(b: &Body) -> (String, Vec<String>) {
    let mut said = refuses(b.held);
    let mut out = String::new();
    let mut floats: Vec<(String, MIRConst, usize)> = Vec::new();

    let _ = writeln!(out, "\t.text");
    let name = symbol(&b.held.symbol);
    let _ = writeln!(out, "\t.globl\t{}", name);
    let _ = writeln!(out, "\t.type\t{}, @function", name);
    let _ = writeln!(out, "{}:", name);
    prologue(&mut out, b);

    for line in &b.held.lines {
        match line {
            Line::Label(at) => {
                let _ = writeln!(out, "{}:", label(b, *at));
            }
            Line::Inst(inst) => {
                if let Some(complaint) = inst_of(&mut out, b, inst, &mut floats) {
                    said.push(complaint);
                }
            }
            Line::Term(held) => term(&mut out, b, held),
        }
    }
    let _ = writeln!(out, "\t.size\t{}, .-{}", name, name);

    // The floating literals this body wanted, under it rather than in one pool
    // at the end: a constant is used by the body that named it and by nothing
    // else, and keeping the two together is what lets the page be read.
    if !floats.is_empty() {
        let _ = writeln!(out, "\t.section\t.rodata");
        for (name, held, bytes) in floats {
            let _ = writeln!(out, "\t.align\t{}", bytes.max(4));
            let _ = writeln!(out, "{}:", name);
            match held {
                MIRConst::Float(n) if bytes <= 4 => {
                    let _ = writeln!(out, "\t.long\t{}", (n as f32).to_bits());
                }
                MIRConst::Float(n) => {
                    let _ = writeln!(out, "\t.quad\t{}", n.to_bits());
                }
                MIRConst::Int(n) => {
                    let _ = writeln!(out, "\t.quad\t{}", n);
                }
            }
        }
        let _ = writeln!(out, "\t.text");
    }
    (out, said)
}

fn prologue(out: &mut String, b: &Body) {
    let _ = writeln!(out, "\tpushq\t%rbp");
    let _ = writeln!(out, "\tmovq\t%rsp, %rbp");
    if b.frame > 0 {
        let _ = writeln!(out, "\tsubq\t${}, %rsp", b.frame);
    }
    for (which, held) in b.saved.iter().enumerate() {
        let at = b.saved_at(which);
        match held.class {
            Class::Float => {
                let _ = writeln!(out, "\tmovsd\t{}, {}", named(*held, 8), frame_at(at));
            }
            Class::Int => {
                let _ = writeln!(out, "\tmovq\t{}, {}", named(*held, 8), frame_at(at));
            }
        }
    }
    params(out, b);
}

// The arguments a caller left in the ABI's registers, put where the allocator
// decided they live.
//
// The ones going to the frame are written first. A store reads a register and
// writes memory, so none of them can be in the way of anything; doing them
// first means the register-to-register moves that follow are the only ones
// that have to be ordered at all.
fn params(out: &mut String, b: &Body) {
    let classes: Vec<Class> = b.held.params.iter().map(|&reg| b.class(reg)).collect();
    let held = passing(b.m, &classes);
    let mut moves: Vec<(Reg, Reg)> = Vec::new();

    for (at, &reg) in b.held.params.iter().enumerate() {
        let Some(Passed::In(from)) = held.get(at).copied() else { continue };
        match b.site(reg) {
            Site::At(off) => {
                let _ = writeln!(
                    out,
                    "\t{}\t{}, {}",
                    mov(b, reg),
                    named(from, b.bytes(reg)),
                    frame_at(off)
                );
            }
            Site::In(to) => moves.push((to, from)),
            Site::Nowhere => {}
        }
    }
    shuffle(out, b, &moves);

    // The ones that arrived on the stack, read from above the frame pointer.
    //
    // *After* the shuffle, and this is the opposite of the order the call site
    // wants -- for the mirror reason. There the stack words are written from
    // registers the shuffle is about to overwrite, so they go first; here they
    // are read into registers the shuffle still has to read, so they go last. A
    // load placed first wrote `%r9` while `%r9` was still the sixth argument,
    // and the sixth argument was gone by the time the shuffle wanted it.
    //
    // A load reads nothing but the frame pointer, so once the shuffle is done
    // there is nothing left for it to disturb: every parameter is in its own
    // register by then, and no two share one.
    for (at, &reg) in b.held.params.iter().enumerate() {
        let Some(Passed::On(which)) = held.get(at).copied() else { continue };
        let bytes = b.bytes(reg);
        let from = frame_at_above(b.incoming_at(which));
        match b.site(reg) {
            Site::In(to) => {
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, reg), from, named(to, bytes));
            }
            Site::At(off) => {
                // Through a scratch of the parameter's own file, for the reason
                // the call site gives: memory to memory is two instructions
                // here, and a float goes through an `xmm`.
                let sc = named(scratch(b, 0, b.class(reg)), bytes);
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, reg), from, sc);
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, reg), sc, frame_at(off));
            }
            Site::Nowhere => {}
        }
    }
}

// A set of register-to-register moves, in an order where none writes over
// something a later one wants.
fn shuffle(out: &mut String, b: &Body, moves: &[(Reg, Reg)]) {
    for step in ordered(moves) {
        match step {
            Step::Move { to, from } => {
                let held = if to.class == Class::Float { "movsd" } else { "movq" };
                let _ = writeln!(out, "\t{}\t{}, {}", held, named(from, 8), named(to, 8));
            }
            Step::Save(from) => {
                let sc = scratch(b, 1, from.class);
                let held = if from.class == Class::Float { "movsd" } else { "movq" };
                let _ = writeln!(out, "\t{}\t{}, {}", held, named(from, 8), named(sc, 8));
            }
            Step::Restore(to) => {
                let sc = scratch(b, 1, to.class);
                let held = if to.class == Class::Float { "movsd" } else { "movq" };
                let _ = writeln!(out, "\t{}\t{}, {}", held, named(sc, 8), named(to, 8));
            }
        }
    }
}

fn epilogue(out: &mut String, b: &Body) {
    for (which, held) in b.saved.iter().enumerate() {
        let at = b.saved_at(which);
        match held.class {
            Class::Float => {
                let _ = writeln!(out, "\tmovsd\t{}, {}", frame_at(at), named(*held, 8));
            }
            Class::Int => {
                let _ = writeln!(out, "\tmovq\t{}, {}", frame_at(at), named(*held, 8));
            }
        }
    }
    // `leave` is `movq %rbp, %rsp` and `popq %rbp` in one, which is exactly
    // what has to happen and says so.
    let _ = writeln!(out, "\tleave");
    let _ = writeln!(out, "\tret");
}

// ---- The terminators -------------------------------------------------------

fn term(out: &mut String, b: &Body, held: &MIRTerm) {
    match held {
        MIRTerm::Goto(to) => {
            let _ = writeln!(out, "\tjmp\t{}", label(b, *to));
        }
        // A flag holds a nought or a one, so the test is against nought and
        // the branch is on "not equal". At whatever width the flag is: a
        // comparison the lowering made for itself is a whole word wide, and
        // one it made for a source comparison is a byte.
        MIRTerm::Branch { cond, then, els } => {
            let _ = writeln!(
                out,
                "\tcmp{}\t$0, {}",
                suffix(b.bytes(*cond)),
                place(b, *cond)
            );
            let _ = writeln!(out, "\tjne\t{}", label(b, *then));
            let _ = writeln!(out, "\tjmp\t{}", label(b, *els));
        }
        MIRTerm::Return(value) => {
            if let Some(reg) = value {
                let want = b.m.answering(b.class(*reg));
                let held = named(want, b.bytes(*reg));
                if place(b, *reg) != held {
                    let _ = writeln!(out, "\t{}\t{}, {}", mov(b, *reg), place(b, *reg), held);
                }
            }
            epilogue(out, b);
        }
        // Nothing reaches it, and an instruction that faults says so louder
        // than falling into whatever is next.
        MIRTerm::Unreachable => {
            let _ = writeln!(out, "\tud2");
        }
    }
}

// ---- The instructions ------------------------------------------------------

fn inst_of(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    floats: &mut Vec<(String, MIRConst, usize)>,
) -> Option<String> {
    let sc0 = |class| scratch(b, 0, class);
    let sc1 = |class| scratch(b, 1, class);

    match &inst.kind {
        MIRInstKind::Const(held) => {
            let def = inst.def?;
            match held {
                MIRConst::Int(n) => {
                    let bytes = b.bytes(def);
                    // An immediate is thirty-two bits and is sign-extended, so
                    // anything that does not fit has to be built in a register
                    // first -- and `movabsq` is the one instruction that takes
                    // a whole one.
                    if *n >= i32::MIN as i64 && *n <= i32::MAX as i64 {
                        let _ = writeln!(
                            out,
                            "\tmov{}\t${}, {}",
                            suffix(bytes),
                            n,
                            place(b, def)
                        );
                    } else {
                        let held = named(sc0(Class::Int), 8);
                        let _ = writeln!(out, "\tmovabsq\t${}, {}", n, held);
                        let _ = writeln!(out, "\tmovq\t{}, {}", held, place(b, def));
                    }
                }
                MIRConst::Float(_) => {
                    let bytes = b.bytes(def);
                    let name = format!(".LC{}_{}", b.index, floats.len());
                    floats.push((name.clone(), held.clone(), bytes));
                    let (held, back) = writing(b, def, sc0(Class::Float));
                    let one = if bytes <= 4 { "movss" } else { "movsd" };
                    let _ = writeln!(out, "\t{}\t{}(%rip), {}", one, name, held);
                    stored(out, b, def, &held, back);
                }
            }
        }

        MIRInstKind::Move(of) => {
            let def = inst.def?;
            let bytes = b.bytes(def);
            let held = match b.class(def) {
                Class::Float => into(out, b, *of, sc0(Class::Float)),
                Class::Int => widened(out, b, *of, sc0(Class::Int), bytes, false),
            };
            let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), held, place(b, def));
        }

        MIRInstKind::Un { op, operand } => {
            let def = inst.def?;
            let bytes = b.bytes(def);
            let (held, back) = writing(b, def, sc0(b.class(def)));
            match op {
                MIRUnOp::Neg | MIRUnOp::Not => {
                    let one = into(out, b, *operand, sc1(Class::Int));
                    if one != held {
                        let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(bytes), one, held);
                    }
                    let what = if matches!(op, MIRUnOp::Neg) { "neg" } else { "not" };
                    let _ = writeln!(out, "\t{}{}\t{}", what, suffix(bytes), held);
                }
                // The sign bit turned over, which is what negating a float is.
                // A subtraction from nought is not the same thing: it gets the
                // sign of nought itself wrong.
                MIRUnOp::FNeg => {
                    let name = format!(".LCn{}_{}", b.index, floats.len());
                    let mask = if bytes <= 4 {
                        MIRConst::Int(0x8000_0000)
                    } else {
                        MIRConst::Int(i64::MIN)
                    };
                    floats.push((name.clone(), mask, 8));
                    let one = into(out, b, *operand, sc1(Class::Float));
                    let what = if bytes <= 4 { "movss" } else { "movsd" };
                    if one != held {
                        let _ = writeln!(out, "\t{}\t{}, {}", what, one, held);
                    }
                    let _ = writeln!(out, "\txorpd\t{}(%rip), {}", name, held);
                }
            }
            stored(out, b, def, &held, back);
        }

        MIRInstKind::Bin { op, lhs, rhs } => return binary(out, b, inst, *op, *lhs, *rhs),

        MIRInstKind::Cmp { op, lhs, rhs } => compare(out, b, inst, *op, *lhs, *rhs),

        MIRInstKind::Convert { of, from, to } => convert(out, b, inst, *of, *from, *to),

        MIRInstKind::Frame(slot) => {
            let def = inst.def?;
            let off = b.offsets.get(*slot).copied().unwrap_or(b.m.word);
            let (held, back) = writing(b, def, sc0(Class::Int));
            let _ = writeln!(out, "\tleaq\t{}, {}", frame_at(off), held);
            stored(out, b, def, &held, back);
        }

        MIRInstKind::Symbol(name) => {
            let def = inst.def?;
            let (held, back) = writing(b, def, sc0(Class::Int));
            let _ = writeln!(out, "\tleaq\t{}(%rip), {}", symbol(name), held);
            stored(out, b, def, &held, back);
        }

        MIRInstKind::Offset { base, bytes } => {
            let def = inst.def?;
            let one = read_at(out, b, *base, sc1(Class::Int), 8);
            let (held, back) = writing(b, def, sc0(Class::Int));
            let _ = writeln!(out, "\tleaq\t{}({}), {}", bytes, one, held);
            stored(out, b, def, &held, back);
        }

        // The machine's own addressing mode where the stride is one of the four
        // it knows, and a multiply first where it is not.
        MIRInstKind::Scaled { base, index, scale } => {
            let def = inst.def?;
            let one = read_at(out, b, *base, sc1(Class::Int), 8);
            let mut step = widened(out, b, *index, sc0(Class::Int), 8, true);
            let mut by = *scale;
            if !matches!(by, 1 | 2 | 4 | 8) {
                let held = named(sc0(Class::Int), 8);
                let _ = writeln!(out, "\timulq\t${}, {}, {}", by, step, held);
                step = held;
                by = 1;
            }
            let (held, back) = writing(b, def, sc0(Class::Int));
            let _ = writeln!(out, "\tleaq\t({}, {}, {}), {}", one, step, by, held);
            stored(out, b, def, &held, back);
        }

        MIRInstKind::Load { from, bytes } => {
            let def = inst.def?;
            let one = read_at(out, b, *from, sc1(Class::Int), 8);
            let (held, back) = writing(b, def, sc0(b.class(def)));
            let want = b.bytes(def);
            match b.class(def) {
                Class::Float => {
                    let what = if *bytes <= 4 { "movss" } else { "movsd" };
                    let _ = writeln!(out, "\t{}\t({}), {}", what, one, held);
                }
                // Reading fewer bytes than the register holds leaves the rest
                // as they were, so the ones above are filled with noughts
                // rather than left to whatever was there.
                Class::Int if *bytes < want => {
                    let to = reg_of(b, def, sc0(Class::Int));
                    if *bytes == 4 {
                        let _ = writeln!(out, "\tmovl\t({}), {}", one, named(to, 4));
                    } else {
                        let _ = writeln!(
                            out,
                            "\tmovz{}{}\t({}), {}",
                            suffix(*bytes),
                            suffix(want.max(4)),
                            one,
                            named(to, want.max(4))
                        );
                    }
                }
                Class::Int => {
                    let _ = writeln!(out, "\tmov{}\t({}), {}", suffix(*bytes), one, held);
                }
            }
            stored(out, b, def, &held, back);
        }

        MIRInstKind::Store { to, value, bytes } => {
            let one = into(out, b, *to, sc1(Class::Int));
            let held = read_at(out, b, *value, sc0(b.class(*value)), *bytes);
            let what = match b.class(*value) {
                Class::Float => if *bytes <= 4 { "movss".into() } else { "movsd".into() },
                Class::Int => format!("mov{}", suffix(*bytes)),
            };
            let _ = writeln!(out, "\t{}\t{}, ({})", what, held, one);
        }

        // The string instruction, with the three registers it insists on put
        // out of the way first. It is one instruction whatever the size, which
        // is what makes it the right answer for a structure of any width.
        MIRInstKind::Copy { to, from, bytes } => {
            // Both addresses into the scratch registers *first*, and
            // unconditionally.
            //
            // The three registers the string instruction insists on are three
            // the allocator hands out, so either address may already be
            // sitting in one of them -- and `movq %r12, %rdi` to set the
            // destination is how the source is lost when the source was
            // `%rdi`. Reading both somewhere the instruction does not want is
            // what makes the order safe whatever the allocator did.
            let held = named(sc0(Class::Int), 8);
            let a = read_at(out, b, *from, sc0(Class::Int), 8);
            if a != held {
                let _ = writeln!(out, "\tmovq\t{}, {}", a, held);
            }
            let one = named(sc1(Class::Int), 8);
            let c = read_at(out, b, *to, sc1(Class::Int), 8);
            if c != one {
                let _ = writeln!(out, "\tmovq\t{}, {}", c, one);
            }
            let (a, c) = (held, one);
            let _ = writeln!(out, "\tpushq\t%rdi");
            let _ = writeln!(out, "\tpushq\t%rsi");
            let _ = writeln!(out, "\tpushq\t%rcx");
            let _ = writeln!(out, "\tmovq\t{}, %rdi", c);
            let _ = writeln!(out, "\tmovq\t{}, %rsi", a);
            let _ = writeln!(out, "\tmovq\t${}, %rcx", bytes);
            let _ = writeln!(out, "\trep movsb");
            let _ = writeln!(out, "\tpopq\t%rcx");
            let _ = writeln!(out, "\tpopq\t%rsi");
            let _ = writeln!(out, "\tpopq\t%rdi");
        }

        MIRInstKind::Call { to, args } => return call(out, b, inst, to, args),

        MIRInstKind::Undef => {}

        // The vector four, which `refuses` has already named.
        _ => {}
    }
    None
}

// The pool, in the section a constant belongs in. `.rodata` and not `.data`:
// nothing writes a string literal or a type descriptor, and saying so is what
// lets a linker put one copy of it in a page nothing may write to.
pub fn pool(held: &[MIRConstant]) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "\t.section\t.rodata");
    for one in held {
        let _ = writeln!(out, "\t.align\t8");
        let held = symbol(&one.symbol);
        let _ = writeln!(out, "\t.type\t{}, @object", held);
        out.push_str(&super::bytes_of(one));
        let _ = writeln!(out, "\t.size\t{}, .-{}", held, held);
    }
    out
}

// ---- Arithmetic ------------------------------------------------------------

fn binary(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    op: MIRBinOp,
    lhs: MIRRegId,
    rhs: MIRRegId,
) -> Option<String> {
    use MIRBinOp::*;
    let def = inst.def?;
    let bytes = b.bytes(def);
    let (sc0, sc1) = (scratch(b, 0, Class::Int), scratch(b, 1, Class::Int));

    match op {
        // The straight ones: put the left side where the answer goes and let
        // the right side be a memory operand, which this machine allows.
        // One width for the instruction and for both of its operands.
        //
        // The MIR does not promise the three agree: a temporary the lowering
        // made is a whole word and a value it was written beside may be one
        // byte, and `addb %r9, %bl` is not an instruction. So the widest of the
        // three is taken, anything narrower is extended into it, and the
        // answer is stored at whatever width the destination really is -- the
        // low bytes of a sum, a product or a bitwise operation depending on
        // nothing above them.
        Add | Sub | And | Or | Xor | Mul => {
            let float = matches!(b.class(def), Class::Float);
            let sc = scratch(b, 0, b.class(def));
            let back = match b.site(def) {
                Site::At(off) => Some(off),
                _ => None,
            };
            // A one-byte multiply has no two-operand form, so it is done four
            // bytes wide like everything else that will not fit.
            let wide = if float {
                bytes
            } else {
                bytes.max(b.bytes(lhs)).max(b.bytes(rhs)).max(usize::from(matches!(op, Mul)) * 4)
            };
            let held = named(reg_of(b, def, sc), wide);
            let a = if float {
                into(out, b, lhs, scratch(b, 1, Class::Float))
            } else {
                widened(out, b, lhs, sc1, wide, false)
            };
            if a != held {
                let what = if float { mov(b, def) } else { format!("mov{}", suffix(wide)) };
                let _ = writeln!(out, "\t{}\t{}, {}", what, a, held);
            }
            let one = if float {
                place(b, rhs)
            } else {
                widened(out, b, rhs, sc1, wide, false)
            };
            let _ = writeln!(out, "\t{}\t{}, {}", mnemonic(op, wide, float), one, held);
            let back_name = named(reg_of(b, def, sc), bytes);
            stored(out, b, def, &back_name, back);
        }

        // The count has to be in `cl`, which is a register the allocator may
        // have given to something. So the left side is read first -- before
        // anything is in the way -- and `rcx` is put back afterwards.
        Shl | LShr | AShr => {
            let a = into(out, b, lhs, sc0);
            let held = named(sc0, bytes);
            if a != held {
                let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(bytes), a, held);
            }
            let _ = writeln!(out, "\tpushq\t%rcx");
            let one = read_at(out, b, rhs, sc1, 8);
            if one != "%rcx" {
                let _ = writeln!(out, "\tmovq\t{}, %rcx", one);
            }
            let what = match op {
                Shl => "shl",
                LShr => "shr",
                _ => "sar",
            };
            let _ = writeln!(out, "\t{}{}\t%cl, {}", what, suffix(bytes), held);
            let _ = writeln!(out, "\tpopq\t%rcx");
            let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), held, place(b, def));
        }

        // The dividend goes in `rdx:rax` and both come back written, so both
        // are put out of the way. The divisor is read before either is touched
        // -- it may be sitting in one of them.
        SDiv | UDiv | SRem | URem => divide(out, b, def, op, lhs, rhs),

        FAdd | FSub | FMul | FDiv => {
            let sc = scratch(b, 0, Class::Float);
            let (held, back) = writing(b, def, sc);
            let a = into(out, b, lhs, scratch(b, 1, Class::Float));
            if a != held {
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), a, held);
            }
            let one = into(out, b, rhs, scratch(b, 1, Class::Float));
            let _ = writeln!(out, "\t{}\t{}, {}", mnemonic(op, bytes, true), one, held);
            stored(out, b, def, &held, back);
        }
    }
    let _ = (sc0, sc1);
    None
}

// Which register a destination is in, or the scratch it is being computed in.
fn reg_of(b: &Body, def: MIRRegId, sc: Reg) -> Reg {
    match b.site(def) {
        Site::In(held) => held,
        _ => sc,
    }
}

fn mnemonic(op: MIRBinOp, bytes: usize, float: bool) -> String {
    use MIRBinOp::*;
    if float {
        let at = if bytes <= 4 { "ss" } else { "sd" };
        return match op {
            FAdd | Add => format!("add{}", at),
            FSub | Sub => format!("sub{}", at),
            FMul | Mul => format!("mul{}", at),
            _ => format!("div{}", at),
        };
    }
    let held = match op {
        Add => "add",
        Sub => "sub",
        And => "and",
        Or => "or",
        Xor => "xor",
        _ => "imul",
    };
    format!("{}{}", held, suffix(bytes))
}

fn divide(
    out: &mut String,
    b: &Body,
    def: MIRRegId,
    op: MIRBinOp,
    lhs: MIRRegId,
    rhs: MIRRegId,
) {
    use MIRBinOp::*;
    let bytes = b.bytes(def);
    // There is no one-byte divide that answers where the others do, so
    // anything narrow is widened first -- which is a real extension and not a
    // reinterpretation, because the top bits of a quotient depend on them.
    let wide = bytes.max(4);
    let signed = matches!(op, SDiv | SRem);
    let (sc0, sc1) = (scratch(b, 0, Class::Int), scratch(b, 1, Class::Int));

    let _ = writeln!(out, "\tpushq\t%rax");
    let _ = writeln!(out, "\tpushq\t%rdx");
    let one = widened(out, b, rhs, sc1, wide, signed);

    // **The divisor may not be in `%rax` or `%rdx`, and the allocator does not
    // know that.** This instruction is the one place on this machine where two
    // registers are named by the opcode rather than by the operands: the
    // dividend is read from `%rdx:%rax`, so the two lines below this one write
    // both of them -- `cqto` fills `%rdx` with the sign of `%rax`, and the
    // unsigned path clears it outright -- and the `mov` into `%rax` writes the
    // other. A divisor that happened to be allocated to either is destroyed
    // before the divide reads it.
    //
    // The `push`es above do not help. They are what puts the caller's `%rax`
    // and `%rdx` back afterwards; the divisor is *read* in between, after the
    // clobber, so what it wants is somewhere else to live rather than somewhere
    // to be restored from.
    //
    // What that was worth in practice: `100 / i` compiled to `idivq %rdx` with
    // `cqto` immediately above it, so the program divided by the sign bit of
    // 100 -- nought -- and took SIGFPE. It only showed up at all because which
    // register `i` landed in varied per run, this compiler having been
    // nondeterministic (see `sir::promote`); the same source crashed or did
    // not depending on nothing.
    //
    // A scratch register is never one of the two, so this always has somewhere
    // to go, and a divisor in memory is left where it is -- `idiv` takes a
    // memory operand and nothing has clobbered it.
    let taken = [
        named(Reg { name: "rax", class: Class::Int }, wide),
        named(Reg { name: "rdx", class: Class::Int }, wide),
    ];
    let one = if taken.contains(&one) {
        let held = named(sc1, wide);
        let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(wide), one, held);
        held
    } else {
        one
    };

    let a = widened(out, b, lhs, sc0, wide, signed);
    if a != named(Reg { name: "rax", class: Class::Int }, wide) {
        let _ = writeln!(out, "\tmov{}\t{}, %{}", suffix(wide), a,
            if wide == 8 { "rax" } else { "eax" });
    }
    if signed {
        let _ = writeln!(out, "\t{}", if wide == 8 { "cqto" } else { "cltd" });
        let _ = writeln!(out, "\tidiv{}\t{}", suffix(wide), one);
    } else {
        let _ = writeln!(out, "\txorl\t%edx, %edx");
        let _ = writeln!(out, "\tdiv{}\t{}", suffix(wide), one);
    }
    let from = match op {
        SDiv | UDiv => if wide == 8 { "%rax" } else { "%eax" },
        _ => if wide == 8 { "%rdx" } else { "%edx" },
    };
    let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(wide), from, named(sc0, wide));
    let _ = writeln!(out, "\tpopq\t%rdx");
    let _ = writeln!(out, "\tpopq\t%rax");
    let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), named(sc0, bytes), place(b, def));
}

// A value read at `wide` bytes, extended from its own width where it is
// narrower. `movsbl` and its family are one instruction that reads a byte and
// writes four; a plain move would leave the three above it as they were.
fn widened(
    out: &mut String,
    b: &Body,
    reg: MIRRegId,
    sc: Reg,
    wide: usize,
    signed: bool,
) -> String {
    let bytes = b.bytes(reg);
    if bytes >= wide {
        return read_at(out, b, reg, sc, wide);
    }
    let held = named(sc, wide);
    let what = if signed { "movs" } else { "movz" };
    let _ = writeln!(
        out,
        "\t{}{}{}\t{}, {}",
        what,
        suffix(bytes),
        suffix(wide),
        place(b, reg),
        held
    );
    held
}

// ---- Comparisons -----------------------------------------------------------

fn compare(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    op: MIRCmpOp,
    lhs: MIRRegId,
    rhs: MIRRegId,
) {
    use MIRCmpOp::*;
    let Some(def) = inst.def else { return };
    let bytes = b.bytes(lhs);
    let float = matches!(b.class(lhs), Class::Float);

    if float {
        let a = into(out, b, lhs, scratch(b, 0, Class::Float));
        let one = into(out, b, rhs, scratch(b, 1, Class::Float));
        let what = if bytes <= 4 { "ucomiss" } else { "ucomisd" };
        let _ = writeln!(out, "\t{}\t{}, {}", what, one, a);
        // Equality has to say what it means about a value that is not ordered
        // against anything, itself included. `setnp` is what asks whether the
        // comparison was ordered at all, and without it a NaN compares equal
        // to everything.
        let (sc0, sc1) = (scratch(b, 0, Class::Int), scratch(b, 1, Class::Int));
        match op {
            FEq => {
                let _ = writeln!(out, "\tsetnp\t{}", named(sc0, 1));
                let _ = writeln!(out, "\tsete\t{}", named(sc1, 1));
                let _ = writeln!(out, "\tandb\t{}, {}", named(sc1, 1), named(sc0, 1));
                widen_flag(out, b, def, sc0);
            }
            FNe => {
                let _ = writeln!(out, "\tsetp\t{}", named(sc0, 1));
                let _ = writeln!(out, "\tsetne\t{}", named(sc1, 1));
                let _ = writeln!(out, "\torb\t{}, {}", named(sc1, 1), named(sc0, 1));
                widen_flag(out, b, def, sc0);
            }
            _ => set_flag(out, b, def, condition(op)),
        }
        return;
    }

    let signed = matches!(op, SLt | SLe | SGt | SGe);
    let wide = bytes.max(b.bytes(rhs)).clamp(1, 8);
    let a = widened(out, b, lhs, scratch(b, 0, Class::Int), wide, signed);
    let one = widened(out, b, rhs, scratch(b, 1, Class::Int), wide, signed);
    let _ = writeln!(out, "\tcmp{}\t{}, {}", suffix(wide), one, a);
    set_flag(out, b, def, condition(op));
}

// A one-byte answer already in a register, put where the destination is at
// the width the destination is.
fn widen_flag(out: &mut String, b: &Body, def: MIRRegId, sc: Reg) {
    let want = b.bytes(def);
    if want > 1 {
        let _ = writeln!(
            out,
            "\tmovzb{}\t{}, {}",
            suffix(want.max(4)),
            named(sc, 1),
            named(sc, want.max(4))
        );
    }
    let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(want), named(sc, want), place(b, def));
}

// `setcc` writes one byte and only one byte, so a destination wider than that
// is filled the rest of the way rather than left with whatever it held.
fn set_flag(out: &mut String, b: &Body, def: MIRRegId, what: &str) {
    let want = b.bytes(def);
    if want == 1 {
        let _ = writeln!(out, "\t{}\t{}", what, place(b, def));
        return;
    }
    let sc = scratch(b, 0, Class::Int);
    let _ = writeln!(out, "\t{}\t{}", what, named(sc, 1));
    let _ = writeln!(out, "\tmovzb{}\t{}, {}", suffix(want.max(4)), named(sc, 1),
        named(reg_of(b, def, sc), want.max(4)));
    if let Site::At(off) = b.site(def) {
        let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(want), named(sc, want),
            frame_at(off));
    }
}

// The letters after `set`. Above and below are the unsigned pair, greater and
// less the signed one, and a float is compared as if unsigned -- which is what
// the flags this machine sets after `ucomisd` actually mean.
fn condition(op: MIRCmpOp) -> &'static str {
    use MIRCmpOp::*;
    match op {
        Eq | FEq => "sete",
        Ne | FNe => "setne",
        SLt => "setl",
        SLe => "setle",
        SGt => "setg",
        SGe => "setge",
        ULt | FLt => "setb",
        ULe | FLe => "setbe",
        UGt | FGt => "seta",
        UGe | FGe => "setae",
    }
}

// ---- Conversions -----------------------------------------------------------

fn convert(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    of: MIRRegId,
    from: MIRScalar,
    to: MIRScalar,
) {
    let Some(def) = inst.def else { return };
    match (from, to) {
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Int { bytes: tb, .. }) => {
            let sc = scratch(b, 0, Class::Int);
            let (held, back) = writing(b, def, sc);
            if tb > fb && fb < 8 {
                let what = if signed { "movs" } else { "movz" };
                // Widening to eight from four has no unsigned form: a
                // four-byte write zeroes the top half of the register on this
                // machine, so a plain move is the extension.
                //
                // From four and not from anything narrower. `movzbq` and
                // `movzwq` are both instructions and do the whole job, and it
                // is only `movzlq` that was never written -- so a byte widened
                // through this arm assembled as `movl %al, %ecx`, which names
                // two widths that do not go together and is not an
                // instruction at all.
                if !signed && tb == 8 && fb == 4 {
                    let _ = writeln!(out, "\tmovl\t{}, {}", place(b, of), named(reg_of(b, def, sc), 4));
                } else {
                    let _ = writeln!(
                        out,
                        "\t{}{}{}\t{}, {}",
                        what,
                        suffix(fb),
                        suffix(tb),
                        place(b, of),
                        named(reg_of(b, def, sc), tb)
                    );
                }
            } else {
                let one = read_at(out, b, of, scratch(b, 1, Class::Int), tb.min(fb));
                let _ = writeln!(out, "\tmov{}\t{}, {}", suffix(tb.min(fb)), one, held);
            }
            stored(out, b, def, &held, back);
        }
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Float { bytes: tb }) => {
            let wide = fb.max(4);
            let one = widened(out, b, of, scratch(b, 0, Class::Int), wide, signed);
            let sc = scratch(b, 0, Class::Float);
            let (held, back) = writing(b, def, sc);
            let what = if tb <= 4 { "cvtsi2ss" } else { "cvtsi2sd" };
            let _ = writeln!(out, "\t{}{}\t{}, {}", what, suffix(wide), one, held);
            stored(out, b, def, &held, back);
        }
        (MIRScalar::Float { bytes: fb }, MIRScalar::Int { bytes: tb, .. }) => {
            let one = into(out, b, of, scratch(b, 0, Class::Float));
            let wide = tb.max(4);
            let sc = scratch(b, 0, Class::Int);
            let what = if fb <= 4 { "cvttss2si" } else { "cvttsd2si" };
            let _ = writeln!(out, "\t{}{}\t{}, {}", what, suffix(wide), one, named(sc, wide));
            let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), named(sc, tb), place(b, def));
        }
        (MIRScalar::Float { bytes: fb }, MIRScalar::Float { bytes: tb }) => {
            let one = into(out, b, of, scratch(b, 1, Class::Float));
            let sc = scratch(b, 0, Class::Float);
            let (held, back) = writing(b, def, sc);
            if fb == tb {
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), one, held);
            } else {
                let what = if tb <= 4 { "cvtsd2ss" } else { "cvtss2sd" };
                let _ = writeln!(out, "\t{}\t{}, {}", what, one, held);
            }
            stored(out, b, def, &held, back);
        }
    }
}

// ---- Calls -----------------------------------------------------------------

fn call(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    to: &MIRCallee,
    args: &[MIRRegId],
) -> Option<String> {
    let classes: Vec<Class> = args.iter().map(|&arg| b.class(arg)).collect();
    let want = passing(b.m, &classes);

    // The ones that go on the stack, *before* anything else is touched.
    //
    // The order is not tidiness. An argument still sitting in a register that
    // the shuffle below is about to write over would be read after it had gone:
    // a call whose first argument moves into `rdi` and whose seventh is living
    // in `rdi` would store whatever the first argument turned out to be. A
    // store reads a register and writes a word of the frame that nothing else
    // here reads, so doing every one of them first is always safe.
    //
    // Load and store one at a time rather than loading them all and then
    // storing: this machine has two scratch registers, and the one used here is
    // wanted again below for an indirect callee.
    for (at, &arg) in args.iter().enumerate() {
        let Some(Passed::On(which)) = want.get(at).copied() else { continue };
        let bytes = b.bytes(arg);
        let held = match b.site(arg) {
            // Already in a register, so it goes straight out.
            Site::In(from) => named(from, bytes),
            // In the frame or nowhere, so it comes through a scratch: this
            // machine will not move memory to memory in one instruction. The
            // scratch is of the argument's own file -- a float goes through an
            // `xmm`, and `movsd` will not name an integer register.
            _ => {
                let sc = named(scratch(b, 0, b.class(arg)), bytes);
                let _ = writeln!(out, "\t{}\t{}, {}", mov(b, arg), place(b, arg), sc);
                sc
            }
        };
        let _ = writeln!(
            out,
            "\t{}\t{}, {}",
            mov(b, arg),
            held,
            frame_at(b.outgoing_at(which))
        );
    }

    // The ones already in registers first, ordered so that none writes over a
    // source another still wants. The ones in the frame after: a load reads no
    // register but the frame pointer, so once the moves are done nothing a
    // load writes is still wanted.
    let mut moves: Vec<(Reg, Reg)> = Vec::new();
    for (at, &arg) in args.iter().enumerate() {
        let Some(Passed::In(into_reg)) = want.get(at).copied() else { continue };
        if let Site::In(from) = b.site(arg) {
            moves.push((into_reg, from));
        }
    }
    shuffle(out, b, &moves);
    for (at, &arg) in args.iter().enumerate() {
        let Some(Passed::In(into_reg)) = want.get(at).copied() else { continue };
        if !matches!(b.site(arg), Site::In(_)) {
            let _ = writeln!(
                out,
                "\t{}\t{}, {}",
                mov(b, arg),
                place(b, arg),
                named(into_reg, b.bytes(arg))
            );
        }
    }

    match to {
        MIRCallee::Symbol(name) => {
            let _ = writeln!(out, "\tcall\t{}", symbol(name));
        }
        // Through a register, which has to be one nothing is about to read --
        // the arguments are already where they go, so a scratch is the only
        // one left that is certainly free.
        MIRCallee::Reg(reg) => {
            let held = read_at(out, b, *reg, scratch(b, 0, Class::Int), 8);
            let _ = writeln!(out, "\tcall\t*{}", held);
        }
    }

    if let Some(def) = inst.def {
        let from = b.m.answering(b.class(def));
        let held = named(from, b.bytes(def));
        if place(b, def) != held {
            let _ = writeln!(out, "\t{}\t{}, {}", mov(b, def), held, place(b, def));
        }
    }
    None
}

#[cfg(test)]
mod tests;
