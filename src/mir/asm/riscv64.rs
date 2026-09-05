// RV64GC under the LP64D convention, in the syntax both GNU `as` and LLVM's
// assembler take.
//
// The destination comes first, as on aarch64, and like that machine nothing
// but a load or a store touches memory. What is different is narrower and more
// interesting: **this machine has no flags and no narrow arithmetic.**
//
// No flags means a comparison is a value. `slt` writes a one or a nought into
// a register, which is exactly what `MIRInstKind::Cmp` already means -- so the
// three-instruction dance the other two do (compare, set from the flags,
// branch on the flags) is one instruction here, and a branch is `bnez` on the
// value. Of the three machines this is the one whose comparison is the same
// shape as the MIR's.
//
// No narrow arithmetic is the other side of that coin. There is no one-byte
// add and no two-byte anything: the register file is sixty-four bits wide and
// the only other width is thirty-two, in the instructions that end in `w`. So
// **a value narrower than a word has to be extended before anything can be
// concluded about its sign**, and this file does that where it matters --
// before a comparison, before a division, before a shift that brings the sign
// down, and on the way into the float file. That is `extend`, and it is called
// in exactly the places where being wrong would be a wrong answer rather than
// a wasted instruction.
//
// **`li`, `la` and `call` are the assembler's**, not the machine's. Each
// expands into two or three real instructions and each covers a case that
// would otherwise be a page of shifts and adds here. Using them is what this
// file does instead of teaching itself to build a sixty-four bit constant, and
// the cost is that the output is a little further from what runs than the
// other two files' is.

use std::fmt::Write;

use super::super::linear::Line;
use super::super::machine::{Class, Reg};
use super::super::mir_nodes::*;
use super::{label, ordered, passing, refuses, symbol, Body, Site, Step};

// ---- Naming ----------------------------------------------------------------

// One name, whatever the width -- the whole point of the ABI names is that
// there is nothing else to say about a register.
fn named(reg: Reg, _bytes: usize) -> String {
    reg.name.to_string()
}

fn scratch(b: &Body, which: usize, class: Class) -> Reg {
    let held = match class {
        Class::Int => b.m.scratch,
        Class::Float => b.m.fscratch,
    };
    held[which.min(held.len() - 1)]
}

// How far the offsets of a block copy may run before the two addresses have to
// step instead. Two kilobytes is the twelve bits signed that a load or a store
// here has, and the window is under it with room for the widest step.
const WINDOW: usize = 2016;

// ---- Addresses -------------------------------------------------------------

// The offset on a load or a store is twelve bits with a sign, so a frame under
// two kilobytes is reached as it stands and a bigger one is worked out first.
fn frame_op(out: &mut String, off: usize, sc: Reg) -> String {
    if off <= 2048 {
        return format!("-{}(s0)", off);
    }
    let held = named(sc, 8);
    let _ = writeln!(out, "\tli\t{}, {}", held, off);
    let _ = writeln!(out, "\tsub\t{}, s0, {}", held, held);
    format!("0({})", held)
}

fn load_of(class: Class, bytes: usize) -> &'static str {
    match (class, bytes) {
        (Class::Float, b) if b <= 4 => "flw",
        (Class::Float, _) => "fld",
        // Unsigned for the two narrow ones. Nothing in the MIR says whether a
        // load is signed -- a cast is a `Convert` and says so itself -- so the
        // extension that adds no information is the one to make.
        (_, 1) => "lbu",
        (_, 2) => "lhu",
        (_, 4) => "lw",
        _ => "ld",
    }
}

fn store_of(class: Class, bytes: usize) -> &'static str {
    match (class, bytes) {
        (Class::Float, b) if b <= 4 => "fsw",
        (Class::Float, _) => "fsd",
        (_, 1) => "sb",
        (_, 2) => "sh",
        (_, 4) => "sw",
        _ => "sd",
    }
}

fn mov_of(class: Class, bytes: usize) -> &'static str {
    match class {
        Class::Float if bytes <= 4 => "fmv.s",
        Class::Float => "fmv.d",
        Class::Int => "mv",
    }
}

// ---- Reading and writing ---------------------------------------------------

fn read(out: &mut String, b: &Body, reg: MIRRegId, sc: Reg) -> String {
    let bytes = b.bytes(reg);
    match b.site(reg) {
        Site::In(held) => named(held, bytes),
        Site::Nowhere => named(sc, bytes),
        Site::At(off) => {
            let held = named(sc, bytes);
            let at = frame_op(out, off, scratch(b, 2, Class::Int));
            let _ = writeln!(out, "\t{}\t{}, {}", load_of(b.class(reg), bytes), held, at);
            held
        }
    }
}

// A value with every bit above its own width made to say the same thing.
//
// This is the one thing this machine needs that the other two do not. A
// four-byte value in a register here has whatever is above it, and `slt` reads
// all sixty-four bits -- so a signed comparison of two `i8`s that were loaded
// without an extension compares nought to two hundred and fifty-five rather
// than minus one to one. Sign for the signed questions, zero for the rest.
// The register it is written into is the caller's to name, because two
// operands of one instruction may both want extending and a single scratch
// would have the second write over the first.
fn extend(
    out: &mut String,
    b: &Body,
    reg: MIRRegId,
    held: &str,
    signed: bool,
    into: Reg,
) -> String {
    let bytes = b.bytes(reg);
    if bytes >= 8 {
        return held.to_string();
    }
    let sc = named(into, 8);
    let bits = 64 - bytes * 8;
    if signed {
        if bytes == 4 {
            let _ = writeln!(out, "\tsext.w\t{}, {}", sc, held);
        } else {
            let _ = writeln!(out, "\tslli\t{}, {}, {}", sc, held, bits);
            let _ = writeln!(out, "\tsrai\t{}, {}, {}", sc, sc, bits);
        }
    } else {
        let _ = writeln!(out, "\tslli\t{}, {}, {}", sc, held, bits);
        let _ = writeln!(out, "\tsrli\t{}, {}, {}", sc, sc, bits);
    }
    sc
}

fn writing(b: &Body, def: MIRRegId, sc: Reg) -> (String, Option<usize>) {
    match b.site(def) {
        Site::In(held) => (named(held, b.bytes(def)), None),
        Site::At(off) => (named(sc, b.bytes(def)), Some(off)),
        Site::Nowhere => (named(sc, b.bytes(def)), None),
    }
}

fn stored(out: &mut String, b: &Body, def: MIRRegId, held: &str, back: Option<usize>) {
    let Some(off) = back else { return };
    let at = frame_op(out, off, scratch(b, 2, Class::Int));
    let _ = writeln!(out, "\t{}\t{}, {}", store_of(b.class(def), b.bytes(def)), held, at);
}

// ---- One body --------------------------------------------------------------

pub fn body(b: &Body) -> (String, Vec<String>) {
    let mut said = refuses(b.held);
    let mut out = String::new();
    let name = symbol(&b.held.symbol);

    let _ = writeln!(out, "\t.text");
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
                if let Some(complaint) = inst_of(&mut out, b, inst) {
                    said.push(complaint);
                }
            }
            Line::Term(held) => term(&mut out, b, held),
        }
    }
    let _ = writeln!(out, "\t.size\t{}, .-{}", name, name);
    (out, said)
}

// The return address and the old frame pointer go down first, and the frame
// pointer is left pointing at the pair -- so every slot below it is at a
// negative offset and nothing in the frame overlaps what was saved.
fn prologue(out: &mut String, b: &Body) {
    let _ = writeln!(out, "\taddi\tsp, sp, -16");
    let _ = writeln!(out, "\tsd\tra, 8(sp)");
    let _ = writeln!(out, "\tsd\ts0, 0(sp)");
    let _ = writeln!(out, "\taddi\ts0, sp, 0");
    if b.frame > 0 {
        if b.frame <= 2048 {
            let _ = writeln!(out, "\taddi\tsp, sp, -{}", b.frame);
        } else {
            let _ = writeln!(out, "\tli\tt0, {}", b.frame);
            let _ = writeln!(out, "\tsub\tsp, sp, t0");
        }
    }
    for (which, held) in b.saved.iter().enumerate() {
        let at = frame_op(out, b.saved_at(which), scratch(b, 2, Class::Int));
        let what = if held.class == Class::Float { "fsd" } else { "sd" };
        let _ = writeln!(out, "\t{}\t{}, {}", what, named(*held, 8), at);
    }
    params(out, b);
}

fn params(out: &mut String, b: &Body) {
    let classes: Vec<Class> = b.held.params.iter().map(|&reg| b.class(reg)).collect();
    let held = passing(b.m, &classes);
    let mut moves: Vec<(Reg, Reg)> = Vec::new();

    for (at, &reg) in b.held.params.iter().enumerate() {
        let Some(Some(from)) = held.get(at).copied() else { continue };
        match b.site(reg) {
            Site::At(off) => {
                let one = frame_op(out, off, scratch(b, 2, Class::Int));
                let _ = writeln!(
                    out,
                    "\t{}\t{}, {}",
                    store_of(b.class(reg), b.bytes(reg)),
                    named(from, b.bytes(reg)),
                    one
                );
            }
            Site::In(to) => moves.push((to, from)),
            Site::Nowhere => {}
        }
    }
    shuffle(out, b, &moves);
}

fn shuffle(out: &mut String, b: &Body, moves: &[(Reg, Reg)]) {
    for step in ordered(moves) {
        let (what, a, c) = match step {
            Step::Move { to, from } => (mov_of(to.class, 8), named(to, 8), named(from, 8)),
            Step::Save(from) => {
                let sc = scratch(b, 1, from.class);
                (mov_of(from.class, 8), named(sc, 8), named(from, 8))
            }
            Step::Restore(to) => {
                let sc = scratch(b, 1, to.class);
                (mov_of(to.class, 8), named(to, 8), named(sc, 8))
            }
        };
        let _ = writeln!(out, "\t{}\t{}, {}", what, a, c);
    }
}

fn epilogue(out: &mut String, b: &Body) {
    for (which, held) in b.saved.iter().enumerate() {
        let at = frame_op(out, b.saved_at(which), scratch(b, 2, Class::Int));
        let what = if held.class == Class::Float { "fld" } else { "ld" };
        let _ = writeln!(out, "\t{}\t{}, {}", what, named(*held, 8), at);
    }
    let _ = writeln!(out, "\taddi\tsp, s0, 0");
    let _ = writeln!(out, "\tld\ts0, 0(sp)");
    let _ = writeln!(out, "\tld\tra, 8(sp)");
    let _ = writeln!(out, "\taddi\tsp, sp, 16");
    let _ = writeln!(out, "\tret");
}

fn term(out: &mut String, b: &Body, held: &MIRTerm) {
    match held {
        MIRTerm::Goto(to) => {
            let _ = writeln!(out, "\tj\t{}", label(b, *to));
        }
        // No flags, so nothing has to be compared first: the value the
        // comparison made is the thing to branch on.
        MIRTerm::Branch { cond, then, els } => {
            let one = read(out, b, *cond, scratch(b, 0, Class::Int));
            let _ = writeln!(out, "\tbnez\t{}, {}", one, label(b, *then));
            let _ = writeln!(out, "\tj\t{}", label(b, *els));
        }
        MIRTerm::Return(value) => {
            if let Some(reg) = value {
                let want = b.m.answering(b.class(*reg));
                let held = named(want, b.bytes(*reg));
                let one = read(out, b, *reg, scratch(b, 0, b.class(*reg)));
                if one != held {
                    let _ = writeln!(
                        out,
                        "\t{}\t{}, {}",
                        mov_of(b.class(*reg), b.bytes(*reg)),
                        held,
                        one
                    );
                }
            }
            epilogue(out, b);
        }
        MIRTerm::Unreachable => {
            let _ = writeln!(out, "\tunimp");
        }
    }
}

// ---- The instructions ------------------------------------------------------

fn inst_of(out: &mut String, b: &Body, inst: &MIRInst) -> Option<String> {
    match &inst.kind {
        MIRInstKind::Const(held) => {
            let def = inst.def?;
            let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
            match held {
                MIRConst::Int(n) => {
                    let _ = writeln!(out, "\tli\t{}, {}", one, n);
                }
                // Through an integer register, this machine having no way to
                // put a constant into a float one. `fmv.d.x` is a move of the
                // bits and not a conversion.
                MIRConst::Float(n) => {
                    let sc = named(scratch(b, 0, Class::Int), 8);
                    if b.bytes(def) <= 4 {
                        let _ = writeln!(out, "\tli\t{}, {}", sc, (*n as f32).to_bits());
                        let _ = writeln!(out, "\tfmv.w.x\t{}, {}", one, sc);
                    } else {
                        let _ = writeln!(out, "\tli\t{}, {}", sc, n.to_bits() as i64);
                        let _ = writeln!(out, "\tfmv.d.x\t{}, {}", one, sc);
                    }
                }
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Move(of) => {
            let def = inst.def?;
            let a = read(out, b, *of, scratch(b, 1, b.class(*of)));
            let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
            if a != one {
                let _ = writeln!(
                    out,
                    "\t{}\t{}, {}",
                    mov_of(b.class(def), b.bytes(def)),
                    one,
                    a
                );
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Un { op, operand } => {
            let def = inst.def?;
            let a = read(out, b, *operand, scratch(b, 1, b.class(*operand)));
            let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
            match op {
                // Nought less it, which is what `neg` is a name for.
                MIRUnOp::Neg => {
                    let what = if b.bytes(def) <= 4 { "negw" } else { "neg" };
                    let _ = writeln!(out, "\t{}\t{}, {}", what, one, a);
                }
                MIRUnOp::Not => {
                    let _ = writeln!(out, "\tnot\t{}, {}", one, a);
                }
                MIRUnOp::FNeg => {
                    let what = if b.bytes(def) <= 4 { "fneg.s" } else { "fneg.d" };
                    let _ = writeln!(out, "\t{}\t{}, {}", what, one, a);
                }
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Bin { op, lhs, rhs } => return binary(out, b, inst, *op, *lhs, *rhs),

        MIRInstKind::Cmp { op, lhs, rhs } => compare(out, b, inst, *op, *lhs, *rhs),

        MIRInstKind::Convert { of, from, to } => return convert(out, b, inst, *of, *from, *to),

        MIRInstKind::Frame(slot) => {
            let def = inst.def?;
            let off = b.offsets.get(*slot).copied().unwrap_or(b.m.word);
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            if off <= 2048 {
                let _ = writeln!(out, "\taddi\t{}, s0, -{}", one, off);
            } else {
                let _ = writeln!(out, "\tli\t{}, {}", one, off);
                let _ = writeln!(out, "\tsub\t{}, s0, {}", one, one);
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Symbol(name) => {
            let def = inst.def?;
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            let _ = writeln!(out, "\tla\t{}, {}", one, symbol(name));
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Offset { base, bytes } => {
            let def = inst.def?;
            let a = read(out, b, *base, scratch(b, 1, Class::Int));
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            if *bytes >= -2048 && *bytes <= 2047 {
                let _ = writeln!(out, "\taddi\t{}, {}, {}", one, a, bytes);
            } else {
                let sc = named(scratch(b, 2, Class::Int), 8);
                let _ = writeln!(out, "\tli\t{}, {}", sc, bytes);
                let _ = writeln!(out, "\tadd\t{}, {}, {}", one, a, sc);
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Scaled { base, index, scale } => {
            let def = inst.def?;
            let a = read(out, b, *base, scratch(b, 0, Class::Int));
            let c = read(out, b, *index, scratch(b, 1, Class::Int));
            // An index is often four bytes and an address is always eight, so
            // what is above the index has to be made to say nothing first.
            let c = extend(out, b, *index, &c, true, scratch(b, 1, Class::Int));
            let sc = named(scratch(b, 1, Class::Int), 8);
            let (one, back) = writing(b, def, scratch(b, 2, Class::Int));
            if scale.is_power_of_two() && *scale > 1 {
                let _ = writeln!(out, "\tslli\t{}, {}, {}", sc, c, scale.trailing_zeros());
                let _ = writeln!(out, "\tadd\t{}, {}, {}", one, a, sc);
            } else if *scale == 1 {
                let _ = writeln!(out, "\tadd\t{}, {}, {}", one, a, c);
            } else {
                let _ = writeln!(out, "\tli\t{}, {}", sc, scale);
                let _ = writeln!(out, "\tmul\t{}, {}, {}", sc, c, sc);
                let _ = writeln!(out, "\tadd\t{}, {}, {}", one, a, sc);
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Load { from, bytes } => {
            let def = inst.def?;
            let a = read(out, b, *from, scratch(b, 1, Class::Int));
            let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
            let _ = writeln!(
                out,
                "\t{}\t{}, 0({})",
                load_of(b.class(def), *bytes),
                one,
                a
            );
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Store { to, value, bytes } => {
            let a = read(out, b, *to, scratch(b, 1, Class::Int));
            let c = read(out, b, *value, scratch(b, 0, b.class(*value)));
            let _ = writeln!(
                out,
                "\t{}\t{}, 0({})",
                store_of(b.class(*value), *bytes),
                c,
                a
            );
        }

        // Unrolled, for the reason aarch64's is: a loop wants a register to
        // count in and there is not a fourth one held back.
        MIRInstKind::Copy { to, from, bytes } => {
            let a = read(out, b, *from, scratch(b, 1, Class::Int));
            let c = read(out, b, *to, scratch(b, 0, Class::Int));
            let held = named(scratch(b, 2, Class::Int), 8);
            // The offset on a load or a store is a small field -- twelve bits
            // signed here, and scaled-unsigned on aarch64 -- so a copy of more
            // than a couple of kilobytes cannot be written as one run of
            // offsets off the two addresses. Past that the addresses themselves
            // step, which keeps every offset inside the window. The two step
            // into the scratch registers, which is where `read` would have put
            // them had they not already been somewhere: an allocated register
            // is never a scratch, so neither can be the other's.
            let (a, c) = match *bytes > WINDOW {
                false => (a, c),
                true => {
                    let one = named(scratch(b, 1, Class::Int), 8);
                    let two = named(scratch(b, 0, Class::Int), 8);
                    if a != one {
                        let _ = writeln!(out, "\tmv\t{}, {}", one, a);
                    }
                    if c != two {
                        let _ = writeln!(out, "\tmv\t{}, {}", two, c);
                    }
                    (one, two)
                }
            };
            let (mut at, mut base) = (0usize, 0usize);
            for step in [8usize, 4, 2, 1] {
                while at + step <= *bytes {
                    if at - base >= WINDOW {
                        let by = at - base;
                        let _ = writeln!(out, "\taddi\t{}, {}, {}", a, a, by);
                        let _ = writeln!(out, "\taddi\t{}, {}, {}", c, c, by);
                        base = at;
                    }
                    let (one, keep) = match step {
                        8 => ("ld", "sd"),
                        4 => ("lw", "sw"),
                        2 => ("lhu", "sh"),
                        _ => ("lbu", "sb"),
                    };
                    let _ = writeln!(out, "\t{}\t{}, {}({})", one, held, at - base, a);
                    let _ = writeln!(out, "\t{}\t{}, {}({})", keep, held, at - base, c);
                    at += step;
                }
            }
        }

        MIRInstKind::Call { to, args } => return call(out, b, inst, to, args),

        MIRInstKind::Undef => {}

        _ => {}
    }
    None
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
    let a = read(out, b, lhs, scratch(b, 0, b.class(lhs)));
    let c = read(out, b, rhs, scratch(b, 1, b.class(rhs)));

    // The ones that read the sign of a narrow operand. Everything else is
    // right on the low bits whatever is above them: the low bits of a sum, a
    // product or a bitwise operation depend on nothing higher -- unless the
    // answer is wider than the operand, in which case what is above it is the
    // answer too.
    let signed = matches!(op, SDiv | SRem | AShr);
    let unsigned = matches!(op, UDiv | URem | LShr)
        || b.bytes(lhs) < bytes
        || b.bytes(rhs) < bytes;
    let (a, c) = if signed || unsigned {
        let one = extend(out, b, lhs, &a, signed, scratch(b, 0, Class::Int));
        // The right side of a shift is a count and needs nothing; of a
        // division it is a divisor and needs the same as the left.
        let held = if matches!(op, AShr | LShr) {
            c
        } else {
            extend(out, b, rhs, &c, signed, scratch(b, 1, Class::Int))
        };
        (one, held)
    } else {
        (a, c)
    };

    let (one, back) = writing(b, def, scratch(b, 2, b.class(def)));
    let narrow = bytes <= 4 && b.class(def) == Class::Int;
    match op {
        // The remainder has an instruction of its own here, unlike aarch64
        // where it is a divide and a multiply-subtract.
        SRem | URem | SDiv | UDiv | Add | Sub | Mul | And | Or | Xor | Shl | LShr
        | AShr => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", mnemonic(op, narrow), one, a, c);
        }
        FAdd | FSub | FMul | FDiv => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", mnemonic(op, bytes <= 4), one, a, c);
        }
    }
    stored(out, b, def, &one, back);
    None
}

// The `w` forms work on thirty-two bits and leave the answer sign-extended
// through the register, which is what makes them the right ones for a value
// the MIR called four bytes wide.
fn mnemonic(op: MIRBinOp, narrow: bool) -> String {
    use MIRBinOp::*;
    let held = match op {
        Add => "add",
        Sub => "sub",
        Mul => "mul",
        SDiv => "div",
        UDiv => "divu",
        SRem => "rem",
        URem => "remu",
        And => "and",
        Or => "or",
        Xor => "xor",
        Shl => "sll",
        LShr => "srl",
        AShr => "sra",
        FAdd => return if narrow { "fadd.s".into() } else { "fadd.d".into() },
        FSub => return if narrow { "fsub.s".into() } else { "fsub.d".into() },
        FMul => return if narrow { "fmul.s".into() } else { "fmul.d".into() },
        FDiv => return if narrow { "fdiv.s".into() } else { "fdiv.d".into() },
    };
    // `and`, `or` and `xor` have no narrow form and want none: every bit of
    // the answer depends on the bit under it and nothing else.
    let wide = matches!(op, And | Or | Xor);
    if narrow && !wide { format!("{}w", held) } else { held.to_string() }
}

// ---- Comparisons -----------------------------------------------------------

// A comparison is a value here, so there is nothing to set from flags: `slt`
// writes the one or the nought straight out. Equality is the one that takes
// two instructions, there being no `seq`.
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
    let a = read(out, b, lhs, scratch(b, 0, b.class(lhs)));
    let c = read(out, b, rhs, scratch(b, 1, b.class(rhs)));

    if b.class(lhs) == Class::Float {
        let wide = b.bytes(lhs) > 4;
        let at = if wide { "d" } else { "s" };
        let (one, back) = writing(b, def, scratch(b, 2, Class::Int));
        match op {
            FEq => {
                let _ = writeln!(out, "\tfeq.{}\t{}, {}, {}", at, one, a, c);
            }
            FNe => {
                let _ = writeln!(out, "\tfeq.{}\t{}, {}, {}", at, one, a, c);
                let _ = writeln!(out, "\txori\t{}, {}, 1", one, one);
            }
            FLt => {
                let _ = writeln!(out, "\tflt.{}\t{}, {}, {}", at, one, a, c);
            }
            FLe => {
                let _ = writeln!(out, "\tfle.{}\t{}, {}, {}", at, one, a, c);
            }
            FGt => {
                let _ = writeln!(out, "\tflt.{}\t{}, {}, {}", at, one, c, a);
            }
            _ => {
                let _ = writeln!(out, "\tfle.{}\t{}, {}, {}", at, one, c, a);
            }
        }
        stored(out, b, def, &one, back);
        return;
    }

    // Both sides extended, each into a scratch of its own: `slt` reads the
    // whole register, so what is above a narrow value decides the answer.
    let signed = matches!(op, SLt | SLe | SGt | SGe);
    let left = extend(out, b, lhs, &a, signed, scratch(b, 0, Class::Int));
    let right = extend(out, b, rhs, &c, signed, scratch(b, 1, Class::Int));

    let (one, back) = writing(b, def, scratch(b, 2, Class::Int));
    let slt = if signed { "slt" } else { "sltu" };
    match op {
        Eq => {
            let _ = writeln!(out, "\txor\t{}, {}, {}", one, left, right);
            let _ = writeln!(out, "\tseqz\t{}, {}", one, one);
        }
        Ne => {
            let _ = writeln!(out, "\txor\t{}, {}, {}", one, left, right);
            let _ = writeln!(out, "\tsnez\t{}, {}", one, one);
        }
        SLt | ULt => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", slt, one, left, right);
        }
        SGt | UGt => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", slt, one, right, left);
        }
        SLe | ULe => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", slt, one, right, left);
            let _ = writeln!(out, "\txori\t{}, {}, 1", one, one);
        }
        _ => {
            let _ = writeln!(out, "\t{}\t{}, {}, {}", slt, one, left, right);
            let _ = writeln!(out, "\txori\t{}, {}, 1", one, one);
        }
    }
    stored(out, b, def, &one, back);
}

// ---- Conversions -----------------------------------------------------------

fn convert(
    out: &mut String,
    b: &Body,
    inst: &MIRInst,
    of: MIRRegId,
    from: MIRScalar,
    to: MIRScalar,
) -> Option<String> {
    let def = inst.def?;
    let a = read(out, b, of, scratch(b, 1, b.class(of)));
    match (from, to) {
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Int { bytes: tb, .. }) => {
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            if tb > fb && fb < 8 {
                let held = extend(out, b, of, &a, signed, scratch(b, 1, Class::Int));
                let _ = writeln!(out, "\tmv\t{}, {}", one, held);
            } else {
                let _ = writeln!(out, "\tmv\t{}, {}", one, a);
            }
            stored(out, b, def, &one, back);
        }
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Float { bytes: tb }) => {
            let held = extend(out, b, of, &a, signed, scratch(b, 1, Class::Int));
            let (one, back) = writing(b, def, scratch(b, 0, Class::Float));
            let at = if tb <= 4 { "s" } else { "d" };
            let what = if signed { "l" } else { "lu" };
            let _ = writeln!(out, "\tfcvt.{}.{}\t{}, {}", at, what, one, held);
            let _ = fb;
            stored(out, b, def, &one, back);
        }
        (MIRScalar::Float { bytes: fb }, MIRScalar::Int { bytes: tb, signed }) => {
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            let at = if fb <= 4 { "s" } else { "d" };
            let what = match (tb <= 4, signed) {
                (true, true) => "w",
                (true, false) => "wu",
                (false, true) => "l",
                (false, false) => "lu",
            };
            // Towards nought, which is what a cast means everywhere in this
            // language and is not this machine's default rounding.
            let _ = writeln!(out, "\tfcvt.{}.{}\t{}, {}, rtz", what, at, one, a);
            stored(out, b, def, &one, back);
        }
        (MIRScalar::Float { bytes: fb }, MIRScalar::Float { bytes: tb }) => {
            let (one, back) = writing(b, def, scratch(b, 0, Class::Float));
            if fb == tb {
                let what = if tb <= 4 { "fmv.s" } else { "fmv.d" };
                let _ = writeln!(out, "\t{}\t{}, {}", what, one, a);
            } else if tb <= 4 {
                let _ = writeln!(out, "\tfcvt.s.d\t{}, {}", one, a);
            } else {
                let _ = writeln!(out, "\tfcvt.d.s\t{}, {}", one, a);
            }
            stored(out, b, def, &one, back);
        }
    }
    None
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
    if want.iter().any(|held| held.is_none()) {
        return Some(format!(
            "{}: a call with {} arguments is not emitted -- nothing here puts one on the stack",
            b.held.symbol,
            args.len()
        ));
    }

    let mut moves: Vec<(Reg, Reg)> = Vec::new();
    for (at, &arg) in args.iter().enumerate() {
        let Some(Some(into_reg)) = want.get(at).copied() else { continue };
        if let Site::In(from) = b.site(arg) {
            moves.push((into_reg, from));
        }
    }
    shuffle(out, b, &moves);
    for (at, &arg) in args.iter().enumerate() {
        let Some(Some(into_reg)) = want.get(at).copied() else { continue };
        let Site::At(off) = b.site(arg) else { continue };
        let one = frame_op(out, off, scratch(b, 2, Class::Int));
        let _ = writeln!(
            out,
            "\t{}\t{}, {}",
            load_of(b.class(arg), b.bytes(arg)),
            named(into_reg, b.bytes(arg)),
            one
        );
    }

    match to {
        MIRCallee::Symbol(name) => {
            let _ = writeln!(out, "\tcall\t{}", symbol(name));
        }
        MIRCallee::Reg(reg) => {
            let held = read(out, b, *reg, scratch(b, 0, Class::Int));
            let _ = writeln!(out, "\tjalr\t{}", held);
        }
    }

    if let Some(def) = inst.def {
        let from = b.m.answering(b.class(def));
        let held = named(from, b.bytes(def));
        let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
        if one != held {
            let _ = writeln!(
                out,
                "\t{}\t{}, {}",
                mov_of(b.class(def), b.bytes(def)),
                one,
                held
            );
        }
        stored(out, b, def, &one, back);
    }
    None
}

// ---- The pool --------------------------------------------------------------

pub fn pool(held: &[MIRConstant]) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "\t.section\t.rodata");
    for one in held {
        let name = symbol(&one.symbol);
        let _ = writeln!(out, "\t.align\t3");
        let _ = writeln!(out, "\t.type\t{}, @object", name);
        out.push_str(&super::bytes_of(one));
        let _ = writeln!(out, "\t.size\t{}, .-{}", name, name);
    }
    out
}

#[cfg(test)]
mod tests;
