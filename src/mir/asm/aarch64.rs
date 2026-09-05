// aarch64, in the syntax both GNU `as` and LLVM's assembler take.
//
// The destination comes first and there is exactly one form for it: every
// arithmetic instruction takes three registers, or two and a small immediate,
// and none of them touches memory. That is the whole difference from x86-64 and
// it runs through this file: a spilled operand is not an addressing mode here,
// it is a load, and an addition of two spilled values into a third spilled
// place is three registers held at once. Which is why this machine keeps three
// scratch registers and x86-64 keeps two.
//
// **A register's width is a different letter, not a different name.** `w0` is
// the bottom half of `x0`, and writing `w0` zeroes the top half rather than
// leaving it -- which is the opposite of what the other two machines here do
// with a narrow write and is worth knowing when reading the output. It makes
// no difference to what is emitted, because every value is read at its own
// width and written at its own width.
//
// **An immediate is twelve bits**, and a constant that does not fit is built
// sixteen bits at a time with `movz` and `movk`. Four instructions at worst for
// a whole word, and no literal pool: a pool would want a `.ltorg` placed
// somewhere a long body cannot reach past, which is a thing to get wrong
// silently.
//
// **A remainder is two instructions and no fixed registers.** `sdiv` then
// `msub` -- the quotient times the divisor taken from the dividend. x86-64
// needs `rdx:rax` and a push and a pop around it; this needs neither, and that
// is the clearest single case of what a three-address machine buys.

use std::fmt::Write;

use super::super::linear::Line;
use super::super::machine::{Class, Reg};
use super::super::mir_nodes::*;
use super::{label, ordered, passing, refuses, symbol, Body, Site, Step};

// ---- Naming ----------------------------------------------------------------

// A register at a width. Anything four bytes or under is the `w` view; the two
// wider are the `x` one. A float is `s` for four bytes and `d` for eight, and
// the machine numbers those two files separately.
fn named(reg: Reg, bytes: usize) -> String {
    if reg.class == Class::Float {
        let held = reg.name.trim_start_matches(|c: char| c.is_alphabetic());
        return format!("{}{}", if bytes <= 4 { "s" } else { "d" }, held);
    }
    if reg.name == "sp" {
        return "sp".to_string();
    }
    let held = reg.name.trim_start_matches('x');
    if bytes <= 4 { format!("w{}", held) } else { format!("x{}", held) }
}

fn scratch(b: &Body, which: usize, class: Class) -> Reg {
    let held = match class {
        Class::Int => b.m.scratch,
        Class::Float => b.m.fscratch,
    };
    held[which.min(held.len() - 1)]
}

// How far the offsets of a block copy may run before the two addresses have to
// step instead. The word form of a load reaches 32760 and the byte form only
// 4095, so the window is under the smaller of the two with room for a step.
const WINDOW: usize = 4032;

// ---- Building an address ---------------------------------------------------

// `x29` less an offset, which is always a *negative* displacement -- and that
// is the whole of what is delicate here.
//
// A load or a store has two immediate forms and only one of them takes a
// negative number. The twelve-bit one is scaled by the width and is unsigned,
// so it reaches a long way up and nowhere at all down; the one that goes down
// is the unscaled form, and its immediate is nine bits signed -- `-256..255`
// and no further. This file used to test the offset against the twelve-bit
// form and then write the nine-bit one, so every frame over 256 bytes emitted
// `[x29, #-408]` and an assembler refused it. A struct of forty fields was
// enough.
//
// So: the short way down where it fits, and otherwise the address worked out
// first. `sub` takes twelve bits unsigned, which covers every frame under
// 4096 in one instruction; above that the constant is built a piece at a time.
fn frame_op(out: &mut String, off: usize, sc: Reg) -> String {
    if off <= 256 {
        return format!("[x29, #-{}]", off);
    }
    let held = named(sc, 8);
    if off < 4096 {
        let _ = writeln!(out, "\tsub\t{}, x29, #{}", held, off);
        return format!("[{}]", held);
    }
    immediate(out, &held, off as i64);
    let _ = writeln!(out, "\tsub\t{}, x29, {}", held, held);
    format!("[{}]", held)
}

// A constant into a register, sixteen bits at a time. `movz` puts the first
// piece down and clears the rest; each `movk` writes one more piece and leaves
// the others. Pieces that are nought are skipped, so a small number is one
// instruction and only a genuinely wide one is four.
fn immediate(out: &mut String, held: &str, n: i64) {
    // Always the `x` view. `movk` on a `w` one takes a shift of nought or
    // sixteen and no more, so a wide constant into a narrow name is not an
    // instruction -- and the bits above the value's own width are ignored by
    // everything that reads it.
    let held = &wide_name(held);
    let held64 = n as u64;
    let pieces: Vec<u64> = (0..4).map(|at| (held64 >> (at * 16)) & 0xffff).collect();
    let mut first = true;
    for (at, piece) in pieces.iter().enumerate() {
        if *piece == 0 && !first {
            continue;
        }
        if first {
            let _ = writeln!(out, "\tmovz\t{}, #{}, lsl #{}", held, piece, at * 16);
            first = false;
        } else {
            let _ = writeln!(out, "\tmovk\t{}, #{}, lsl #{}", held, piece, at * 16);
        }
    }
    if first {
        let _ = writeln!(out, "\tmovz\t{}, #0", held);
    }
}

// The `x` view of a register named as the `w` one.
fn wide_name(held: &str) -> String {
    match held.strip_prefix('w') {
        Some(one) => format!("x{}", one),
        None => held.to_string(),
    }
}

// An operand at a width the caller names, extended where the value is
// narrower than that. The MIR does not promise an instruction's operands and
// its answer are all one width -- a temporary the lowering made is a whole
// word and a value beside it may be one byte -- and `add w0, x1, x2` is not
// an instruction.
fn unify(
    out: &mut String,
    b: &Body,
    reg: MIRRegId,
    held: &str,
    wide: usize,
    signed: bool,
    into: Reg,
) -> String {
    let bytes = b.bytes(reg);
    if bytes >= wide || b.class(reg) == Class::Float {
        return if wide <= 4 { narrow(held) } else { wide_name(held) };
    }
    let one = named(into, wide);
    let what = match (signed, bytes) {
        (true, 1) => "sxtb",
        (true, 2) => "sxth",
        (true, _) => "sxtw",
        (false, 1) => "uxtb",
        (false, 2) => "uxth",
        (false, _) => "mov",
    };
    if what == "mov" {
        let _ = writeln!(out, "\tmov\t{}, {}", narrow(&one), narrow(held));
    } else {
        let _ = writeln!(out, "\t{}\t{}, {}", what, one, narrow(held));
    }
    one
}

// ---- Reading and writing ---------------------------------------------------

// The move that carries a value of this width and file.
fn mov_of(class: Class, bytes: usize) -> &'static str {
    match class {
        Class::Float => "fmov",
        Class::Int if bytes <= 4 => "mov",
        Class::Int => "mov",
    }
}

fn load_of(class: Class, bytes: usize) -> &'static str {
    match (class, bytes) {
        (Class::Float, _) => "ldr",
        (_, 1) => "ldrb",
        (_, 2) => "ldrh",
        _ => "ldr",
    }
}

fn store_of(class: Class, bytes: usize) -> &'static str {
    match (class, bytes) {
        (Class::Float, _) => "str",
        (_, 1) => "strb",
        (_, 2) => "strh",
        _ => "str",
    }
}

// A value in a register, loading it out of the frame where that is where it
// is. Everything on this machine goes through here: there is no instruction
// that would have taken it where it lay.
fn read(out: &mut String, b: &Body, reg: MIRRegId, sc: Reg) -> String {
    let bytes = b.bytes(reg);
    match b.site(reg) {
        Site::In(held) => named(held, bytes),
        Site::Nowhere => named(sc, bytes),
        Site::At(off) => {
            let held = named(sc, bytes);
            // A one- or two-byte load writes the `w` view whatever the value
            // is called, which is what `ldrb` and `ldrh` do.
            let name = if bytes <= 4 && b.class(reg) == Class::Int {
                named(sc, 4)
            } else {
                held.clone()
            };
            let at = frame_op(out, off, scratch(b, 2, Class::Int));
            let _ = writeln!(out, "\t{}\t{}, {}", load_of(b.class(reg), bytes), name, at);
            held
        }
    }
}

// Where to compute an answer, and what has to happen afterwards.
fn writing(b: &Body, def: MIRRegId, sc: Reg) -> (String, Option<usize>) {
    match b.site(def) {
        Site::In(held) => (named(held, b.bytes(def)), None),
        Site::At(off) => (named(sc, b.bytes(def)), Some(off)),
        Site::Nowhere => (named(sc, b.bytes(def)), None),
    }
}

fn stored(out: &mut String, b: &Body, def: MIRRegId, held: &str, back: Option<usize>) {
    let Some(off) = back else { return };
    let bytes = b.bytes(def);
    let at = frame_op(out, off, scratch(b, 2, Class::Int));
    let _ = writeln!(out, "\t{}\t{}, {}", store_of(b.class(def), bytes), held, at);
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

// The frame pointer and the link register go down together, which is what the
// pre-indexed form of `stp` is for: one instruction that moves the stack and
// writes both.
fn prologue(out: &mut String, b: &Body) {
    let _ = writeln!(out, "\tstp\tx29, x30, [sp, #-16]!");
    let _ = writeln!(out, "\tmov\tx29, sp");
    if b.frame > 0 {
        if b.frame < 4096 {
            let _ = writeln!(out, "\tsub\tsp, sp, #{}", b.frame);
        } else {
            immediate(out, "x16", b.frame as i64);
            let _ = writeln!(out, "\tsub\tsp, sp, x16");
        }
    }
    for (which, held) in b.saved.iter().enumerate() {
        let at = b.saved_at(which);
        let one = frame_op(out, at, scratch(b, 2, Class::Int));
        let _ = writeln!(out, "\tstr\t{}, {}", named(*held, 8), one);
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
                let bytes = b.bytes(reg);
                let one = frame_op(out, off, scratch(b, 2, Class::Int));
                let _ = writeln!(
                    out,
                    "\t{}\t{}, {}",
                    store_of(b.class(reg), bytes),
                    named(from, bytes),
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
        let at = b.saved_at(which);
        let one = frame_op(out, at, scratch(b, 2, Class::Int));
        let _ = writeln!(out, "\tldr\t{}, {}", named(*held, 8), one);
    }
    // The stack back to where the frame pointer says, and then the pair out of
    // it -- the post-indexed form, which is the other half of the `stp` above.
    let _ = writeln!(out, "\tmov\tsp, x29");
    let _ = writeln!(out, "\tldp\tx29, x30, [sp], #16");
    let _ = writeln!(out, "\tret");
}

fn term(out: &mut String, b: &Body, held: &MIRTerm) {
    match held {
        MIRTerm::Goto(to) => {
            let _ = writeln!(out, "\tb\t{}", label(b, *to));
        }
        MIRTerm::Branch { cond, then, els } => {
            let one = read(out, b, *cond, scratch(b, 0, Class::Int));
            let _ = writeln!(out, "\tcbnz\t{}, {}", one, label(b, *then));
            let _ = writeln!(out, "\tb\t{}", label(b, *els));
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
        // The permanently undefined instruction, which is what this machine
        // calls the one that is guaranteed to fault.
        MIRTerm::Unreachable => {
            let _ = writeln!(out, "\tudf\t#0");
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
                MIRConst::Int(n) => immediate(out, &one, *n),
                // A float goes in through an integer register: this machine
                // has no instruction that puts a constant in a float one, and
                // `fmov` between the two files is a move of the bits.
                MIRConst::Float(n) => {
                    let held = named(scratch(b, 0, Class::Int), 8);
                    let bits = if b.bytes(def) <= 4 {
                        (*n as f32).to_bits() as i64
                    } else {
                        n.to_bits() as i64
                    };
                    immediate(out, &held, bits);
                    let at = if b.bytes(def) <= 4 {
                        named(scratch(b, 0, Class::Int), 4)
                    } else {
                        held
                    };
                    let _ = writeln!(out, "\tfmov\t{}, {}", one, at);
                }
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Move(of) => {
            let def = inst.def?;
            let a = read(out, b, *of, scratch(b, 1, b.class(*of)));
            let a = unify(out, b, *of, &a, b.bytes(def), false, scratch(b, 1, Class::Int));
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
            let what = match op {
                MIRUnOp::Neg => "neg",
                MIRUnOp::Not => "mvn",
                MIRUnOp::FNeg => "fneg",
            };
            let _ = writeln!(out, "\t{}\t{}, {}", what, one, a);
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Bin { op, lhs, rhs } => {
            let def = inst.def?;
            let float = b.class(def) == Class::Float;
            let wide = if float {
                b.bytes(def)
            } else {
                b.bytes(def).max(b.bytes(*lhs)).max(b.bytes(*rhs)).clamp(1, 8)
            };
            let signed = matches!(op, MIRBinOp::SDiv | MIRBinOp::SRem | MIRBinOp::AShr);
            let a = read(out, b, *lhs, scratch(b, 0, b.class(*lhs)));
            let a = unify(out, b, *lhs, &a, wide, signed, scratch(b, 0, Class::Int));
            let c = read(out, b, *rhs, scratch(b, 1, b.class(*rhs)));
            let c = unify(out, b, *rhs, &c, wide, signed, scratch(b, 1, Class::Int));
            let sc = scratch(b, 2, b.class(def));
            let back = match b.site(def) {
                Site::At(off) => Some(off),
                _ => None,
            };
            let one = if float {
                named(reg_of(b, def, sc), b.bytes(def))
            } else {
                named(reg_of(b, def, sc), wide)
            };
            use MIRBinOp::*;
            match op {
                // The one that is two instructions: the quotient, and then the
                // dividend less the quotient times the divisor.
                SRem | URem => {
                    let held = named(scratch(b, 2, Class::Int), b.bytes(def));
                    let what = if matches!(op, SRem) { "sdiv" } else { "udiv" };
                    let _ = writeln!(out, "\t{}\t{}, {}, {}", what, held, a, c);
                    let _ = writeln!(out, "\tmsub\t{}, {}, {}, {}", one, held, c, a);
                }
                _ => {
                    let what = mnemonic(*op);
                    let _ = writeln!(out, "\t{}\t{}, {}, {}", what, one, a, c);
                }
            }
            let name = named(reg_of(b, def, sc), b.bytes(def));
            stored(out, b, def, &name, back);
        }

        MIRInstKind::Cmp { op, lhs, rhs } => {
            use MIRCmpOp::*;
            let def = inst.def?;
            let signed = matches!(op, SLt | SLe | SGt | SGe);
            let float = b.class(*lhs) == Class::Float;
            let wide = b.bytes(*lhs).max(b.bytes(*rhs)).clamp(1, 8);
            let a = read(out, b, *lhs, scratch(b, 0, b.class(*lhs)));
            let c = read(out, b, *rhs, scratch(b, 1, b.class(*rhs)));
            let (a, c) = if float {
                (a, c)
            } else {
                (
                    unify(out, b, *lhs, &a, wide, signed, scratch(b, 0, Class::Int)),
                    unify(out, b, *rhs, &c, wide, signed, scratch(b, 1, Class::Int)),
                )
            };
            let what = if float { "fcmp" } else { "cmp" };
            let _ = writeln!(out, "\t{}\t{}, {}", what, a, c);
            let (one, back) = writing(b, def, scratch(b, 2, Class::Int));
            // `cset` writes a whole register whatever the answer is called.
            let _ = writeln!(out, "\tcset\t{}, {}", narrow(&wide_name(&one)), condition(*op));
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Convert { of, from, to } => return convert(out, b, inst, *of, *from, *to),

        MIRInstKind::Frame(slot) => {
            let def = inst.def?;
            let off = b.offsets.get(*slot).copied().unwrap_or(b.m.word);
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            if off < 4096 {
                let _ = writeln!(out, "\tsub\t{}, x29, #{}", one, off);
            } else {
                immediate(out, &one, off as i64);
                let _ = writeln!(out, "\tsub\t{}, x29, {}", one, one);
            }
            stored(out, b, def, &one, back);
        }

        // A page, and then the rest of the address within it. This machine
        // cannot reach an arbitrary symbol in one instruction and does not
        // pretend to.
        MIRInstKind::Symbol(name) => {
            let def = inst.def?;
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            let held = symbol(name);
            let _ = writeln!(out, "\tadrp\t{}, {}", one, held);
            let _ = writeln!(out, "\tadd\t{}, {}, :lo12:{}", one, one, held);
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Offset { base, bytes } => {
            let def = inst.def?;
            let a = wide_name(&read(out, b, *base, scratch(b, 1, Class::Int)));
            let (one, back) = writing(b, def, scratch(b, 0, Class::Int));
            let one = wide_name(&one);
            let held = if *bytes < 0 { "sub" } else { "add" };
            let by = bytes.unsigned_abs();
            if by < 4096 {
                let _ = writeln!(out, "\t{}\t{}, {}, #{}", held, one, a, by);
            } else {
                let step = named(scratch(b, 2, Class::Int), 8);
                immediate(out, &step, by as i64);
                let _ = writeln!(out, "\t{}\t{}, {}, {}", held, one, a, step);
            }
            stored(out, b, def, &one, back);
        }

        // A shift where the stride is a power of two, which is what the
        // addressing forms of this machine understand, and a multiply and an
        // add where it is not.
        MIRInstKind::Scaled { base, index, scale } => {
            let def = inst.def?;
            let a = wide_name(&read(out, b, *base, scratch(b, 0, Class::Int)));
            let c = read(out, b, *index, scratch(b, 1, Class::Int));
            let c = widen(out, b, *index, &c);
            let (one, back) = writing(b, def, scratch(b, 2, Class::Int));
            let one = wide_name(&one);
            match shift_of(*scale) {
                Some(0) => {
                    let _ = writeln!(out, "\tadd\t{}, {}, {}", one, a, c);
                }
                Some(by) => {
                    let _ = writeln!(out, "\tadd\t{}, {}, {}, lsl #{}", one, a, c, by);
                }
                None => {
                    let step = named(scratch(b, 2, Class::Int), 8);
                    immediate(out, &step, *scale as i64);
                    let _ = writeln!(out, "\tmadd\t{}, {}, {}, {}", one, c, step, a);
                }
            }
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Load { from, bytes } => {
            let def = inst.def?;
            let a = wide_name(&read(out, b, *from, scratch(b, 1, Class::Int)));
            let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
            let name = if *bytes <= 4 && b.class(def) == Class::Int {
                narrow(&one)
            } else {
                one.clone()
            };
            let _ = writeln!(
                out,
                "\t{}\t{}, [{}]",
                load_of(b.class(def), *bytes),
                name,
                a
            );
            stored(out, b, def, &one, back);
        }

        MIRInstKind::Store { to, value, bytes } => {
            let a = wide_name(&read(out, b, *to, scratch(b, 1, Class::Int)));
            let c = read(out, b, *value, scratch(b, 0, b.class(*value)));
            let name = if *bytes <= 4 && b.class(*value) == Class::Int {
                narrow(&c)
            } else {
                c
            };
            let _ = writeln!(
                out,
                "\t{}\t{}, [{}]",
                store_of(b.class(*value), *bytes),
                name,
                a
            );
        }

        // Unrolled, a word at a time and then the tail. There is no string
        // instruction here and a loop would want a fourth register to count
        // in, which is one more than this machine keeps back -- so a very
        // large copy is a very large run of instructions, and that is said
        // rather than hidden.
        MIRInstKind::Copy { to, from, bytes } => {
            let a = wide_name(&read(out, b, *from, scratch(b, 1, Class::Int)));
            let c = wide_name(&read(out, b, *to, scratch(b, 0, Class::Int)));
            let held = named(scratch(b, 2, Class::Int), 8);
            // The offset on a load or a store is a small field, so a copy of
            // more than a few kilobytes cannot be written as one run of offsets
            // off the two addresses -- past the window the addresses step
            // instead. They step into the scratch registers, which is where
            // `read` would have put them had they not already been somewhere:
            // an allocated register is never a scratch, so neither of these can
            // be the other's.
            let (a, c) = match *bytes > WINDOW {
                false => (a, c),
                true => {
                    let one = named(scratch(b, 1, Class::Int), 8);
                    let two = named(scratch(b, 0, Class::Int), 8);
                    if a != one {
                        let _ = writeln!(out, "\tmov\t{}, {}", one, a);
                    }
                    if c != two {
                        let _ = writeln!(out, "\tmov\t{}, {}", two, c);
                    }
                    (one, two)
                }
            };
            let (mut at, mut base) = (0usize, 0usize);
            for step in [8usize, 4, 2, 1] {
                while at + step <= *bytes {
                    if at - base >= WINDOW {
                        let by = at - base;
                        let _ = writeln!(out, "\tadd\t{}, {}, #{}", a, a, by);
                        let _ = writeln!(out, "\tadd\t{}, {}, #{}", c, c, by);
                        base = at;
                    }
                    let (one, keep) = match step {
                        8 => ("ldr", "str"),
                        4 => ("ldr", "str"),
                        2 => ("ldrh", "strh"),
                        _ => ("ldrb", "strb"),
                    };
                    let name = if step >= 8 { held.clone() } else { narrow(&held) };
                    let _ = writeln!(out, "\t{}\t{}, [{}, #{}]", one, name, a, at - base);
                    let _ = writeln!(out, "\t{}\t{}, [{}, #{}]", keep, name, c, at - base);
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

// Which register a destination is in, or the scratch it is being computed in.
fn reg_of(b: &Body, def: MIRRegId, sc: Reg) -> Reg {
    match b.site(def) {
        Site::In(held) => held,
        _ => sc,
    }
}

// The `w` view of a register named as the `x` one, for the loads and stores
// that write a narrow value.
fn narrow(held: &str) -> String {
    match held.strip_prefix('x') {
        Some(one) => format!("w{}", one),
        None => held.to_string(),
    }
}

// An index read at its own width, widened to a whole register: an address is
// eight bytes and an index is often four, and adding a `w` to an `x` is not a
// thing this machine does without being told which extension to use.
fn widen(out: &mut String, b: &Body, reg: MIRRegId, held: &str) -> String {
    if b.bytes(reg) >= 8 {
        return held.to_string();
    }
    let one = format!("x{}", held.trim_start_matches(['w', 'x']));
    let _ = writeln!(out, "\tsxtw\t{}, {}", one, held);
    one
}

fn shift_of(scale: usize) -> Option<u32> {
    if scale.is_power_of_two() { Some(scale.trailing_zeros()) } else { None }
}

fn mnemonic(op: MIRBinOp) -> &'static str {
    use MIRBinOp::*;
    match op {
        Add => "add",
        Sub => "sub",
        Mul => "mul",
        SDiv => "sdiv",
        UDiv => "udiv",
        And => "and",
        Or => "orr",
        Xor => "eor",
        Shl => "lsl",
        LShr => "lsr",
        AShr => "asr",
        FAdd => "fadd",
        FSub => "fsub",
        FMul => "fmul",
        FDiv => "fdiv",
        // The two that are written out where they are met.
        SRem | URem => "sdiv",
    }
}

// What `cset` is given. The float cases are the ones where a value that is not
// ordered against anything has to come out false: `mi` and `ls` say no to an
// unordered comparison where `lt` and `le` would say yes.
fn condition(op: MIRCmpOp) -> &'static str {
    use MIRCmpOp::*;
    match op {
        Eq | FEq => "eq",
        Ne | FNe => "ne",
        SLt => "lt",
        SLe => "le",
        SGt => "gt",
        SGe => "ge",
        ULt => "lo",
        ULe => "ls",
        UGt => "hi",
        UGe => "hs",
        FLt => "mi",
        FLe => "ls",
        FGt => "gt",
        FGe => "ge",
    }
}

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
    let (one, back) = writing(b, def, scratch(b, 0, b.class(def)));
    match (from, to) {
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Int { bytes: tb, .. }) => {
            if tb > fb && fb < 8 {
                let what = match (signed, fb) {
                    (true, 1) => "sxtb",
                    (true, 2) => "sxth",
                    (true, _) => "sxtw",
                    (false, 1) => "uxtb",
                    (false, 2) => "uxth",
                    (false, _) => "mov",
                };
                // Widening without a sign is a write of the `w` view, which
                // clears the top half on its own.
                if what == "mov" {
                    let _ = writeln!(out, "\tmov\t{}, {}", narrow(&one), narrow(&a));
                } else {
                    let _ = writeln!(out, "\t{}\t{}, {}", what, one, narrow(&a));
                }
            } else if tb < fb {
                // Narrowing, so the `w` view of both. A write of a `w` clears
                // the top half on its own, which is the truncation the cast
                // asks for -- and the two have to be named at one width, since
                // `mov w3, x2` reads as this and is not an instruction.
                let _ = writeln!(out, "\tmov\t{}, {}", narrow(&one), narrow(&a));
            } else {
                let _ = writeln!(out, "\tmov\t{}, {}", one, a);
            }
        }
        (MIRScalar::Int { bytes: fb, signed }, MIRScalar::Float { .. }) => {
            let what = if signed { "scvtf" } else { "ucvtf" };
            let held = if fb <= 4 { narrow(&a) } else { a };
            let _ = writeln!(out, "\t{}\t{}, {}", what, one, held);
        }
        (MIRScalar::Float { .. }, MIRScalar::Int { bytes: tb, signed }) => {
            let what = if signed { "fcvtzs" } else { "fcvtzu" };
            let held = if tb <= 4 { narrow(&one) } else { one.clone() };
            let _ = writeln!(out, "\t{}\t{}, {}", what, held, a);
        }
        (MIRScalar::Float { bytes: fb }, MIRScalar::Float { bytes: tb }) => {
            if fb == tb {
                let _ = writeln!(out, "\tfmov\t{}, {}", one, a);
            } else {
                let _ = writeln!(out, "\tfcvt\t{}, {}", one, a);
            }
        }
    }
    stored(out, b, def, &one, back);
    None
}

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
        let bytes = b.bytes(arg);
        let one = frame_op(out, off, scratch(b, 2, Class::Int));
        let name = if bytes <= 4 && b.class(arg) == Class::Int {
            named(into_reg, 4)
        } else {
            named(into_reg, bytes)
        };
        let _ = writeln!(out, "\t{}\t{}, {}", load_of(b.class(arg), bytes), name, one);
    }

    match to {
        MIRCallee::Symbol(name) => {
            let _ = writeln!(out, "\tbl\t{}", symbol(name));
        }
        MIRCallee::Reg(reg) => {
            let held = read(out, b, *reg, scratch(b, 0, Class::Int));
            let _ = writeln!(out, "\tblr\t{}", held);
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
