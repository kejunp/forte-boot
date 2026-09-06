// The listing: the MIR as something to read.
//
//     MIR (linear) -> regalloc -> text
//                                 ^^^^
//
// This is where the compiler finally says something out loud. Everything before
// it hands the next pass a data structure; this hands a person a page.
//
// It is a listing and not an assembler's input, and the difference is the
// point. No instruction here is one a machine has -- `copy.24` moves
// twenty-four bytes and nothing does that in one go -- and no directive here is
// one an assembler knows. What it is instead is every decision the back end
// made, written where it can be checked by reading: which registers things went
// in, what spilled, how big the frame is, how many bytes into a structure a
// field turned out to be. Those are the things that are wrong silently, and a
// page is the cheapest place to catch them.
//
// `mir::asm` is the other reader of the same decisions, and what it writes an
// assembler takes. Neither is derived from the other: this one is shorter than
// assembly because it leaves out everything a machine needs and a person does
// not, and leaving those out is what it is for. Where the two disagree about a
// body one of them is wrong, and they are meant to be read side by side --
// which is why both number a block the same way.
//
// The registers are the allocated ones. A listing over `%0` and `%1` would be
// the graph again with the edges flattened, and the whole reason for the second
// stage is what happens when there are not enough registers -- so what it shows
// is what the allocator did. What it shows for something that did not get one
// is where in the frame it went.
//
// Nothing in this file is a `Display` impl, and there is not one anywhere else
// in the compiler either. Every IR before this one is read with `{:#?}`, which
// is right for a thing a test prints and wrong for a thing a person reads: a
// `Debug` of a body is the body's *shape*, and what is wanted here is the
// program.

use std::fmt::Write;

use super::linear::{linearise, Line, Linear};
use super::machine::Machine;
use super::mir_nodes::*;
use super::regalloc::{allocate, Allocation, Where};

// The whole program: every body, and the pool underneath.
pub fn render(p: &MIRProgram, m: Machine) -> String {
    let mut out = String::new();
    for body in &p.bodies {
        let mut held = linearise(body);
        let at = allocate(&mut held, m);
        out.push_str(&body_text(&held, &at, m));
        out.push('\n');
    }
    if !p.pool.is_empty() {
        out.push_str("pool:\n");
        for held in &p.pool {
            let shown = match &held.held {
                MIRConstBody::Bytes(bytes) => quoted(bytes),
                MIRConstBody::Words(names) => format!("[{}]", names.join(", ")),
            };
            let _ = writeln!(out, "    {} = {}", held.symbol, shown);
        }
    }
    out
}

// One body, with its frame written above it so that every `[fp-N]` below has
// something to be read against.
pub fn body_text(held: &Linear, at: &Allocation, m: Machine) -> String {
    let (offsets, size) = frame(&held.frame, m);
    let mut out = String::new();
    let _ = writeln!(out, "{}:", held.symbol);
    let _ = writeln!(out, "    frame {} bytes", size);
    for (i, slot) in held.frame.iter().enumerate() {
        let _ = writeln!(
            out,
            "        [fp-{}] {} {} bytes{}",
            offsets[i],
            slot.name,
            slot.bytes,
            if slot.spill { " (spill)" } else { "" }
        );
    }

    let place = |reg: MIRRegId| -> String {
        match at.of(reg) {
            Where::In(held) => held.name.to_string(),
            Where::Spilled(slot) => format!("[fp-{}]", offsets.get(slot).copied().unwrap_or(0)),
            // Nothing writes it and nothing reads it, so there is nothing to
            // name -- and saying so is better than naming a register it is not
            // in.
            Where::Nowhere => "_".to_string(),
        }
    };

    for line in &held.lines {
        match line {
            Line::Label(block) => {
                let _ = writeln!(out, "  .L{}:", block);
            }
            Line::Inst(inst) => {
                let body = inst_text(&inst.kind, &place);
                match inst.def {
                    Some(def) => {
                        let _ = writeln!(out, "      {} = {}", place(def), body);
                    }
                    None => {
                        let _ = writeln!(out, "      {}", body);
                    }
                }
            }
            Line::Term(term) => {
                let _ = writeln!(out, "      {}", term_text(term, &place));
            }
        }
    }
    out
}

fn inst_text(kind: &MIRInstKind, place: &impl Fn(MIRRegId) -> String) -> String {
    use MIRInstKind::*;
    match kind {
        Const(MIRConst::Int(n)) => format!("const {}", n),
        Const(MIRConst::Float(n)) => format!("const {}", n),
        Move(of) => format!("mov {}", place(*of)),
        Un { op, operand } => format!("{} {}", un(*op), place(*operand)),
        Bin { op, lhs, rhs } => format!("{} {}, {}", bin(*op), place(*lhs), place(*rhs)),
        Cmp { op, lhs, rhs } => format!("{} {}, {}", cmp(*op), place(*lhs), place(*rhs)),
        Convert { of, from, to } => {
            format!("conv.{}.{} {}", scalar(*from), scalar(*to), place(*of))
        }
        // The address of something rather than what is in it, which is what
        // `lea` means everywhere it is written.
        Frame(slot) => format!("lea ${}", slot),
        Symbol(name) => format!("lea {}", name),
        Offset { base, bytes } => format!("lea [{} + {}]", place(*base), bytes),
        Scaled { base, index, scale } => {
            format!("lea [{} + {}*{}]", place(*base), place(*index), scale)
        }
        Load { from, bytes } => format!("load.{} [{}]", bytes, place(*from)),
        Store { to, value, bytes } => {
            format!("store.{} [{}], {}", bytes, place(*to), place(*value))
        }
        Copy { to, from, bytes } => {
            format!("copy.{} [{}], [{}]", bytes, place(*to), place(*from))
        }
        Call { to, args } => {
            let held: Vec<String> = args.iter().map(|&arg| place(arg)).collect();
            let name = match to {
                MIRCallee::Symbol(name) => name.clone(),
                MIRCallee::Reg(reg) => place(*reg),
            };
            format!("call {}({})", name, held.join(", "))
        }
        Pack(of) => {
            let held: Vec<String> = of.iter().map(|&one| place(one)).collect();
            format!("pack {}", held.join(", "))
        }
        Lane { of, at } => format!("lane {}[{}]", place(*of), at),
        VecLoad { from, bytes, lanes } => {
            format!("vload.{}x{} [{}]", bytes, lanes, place(*from))
        }
        VecStore { to, value } => format!("vstore [{}], {}", place(*to), place(*value)),
        Undef => "undef".to_string(),
    }
}

fn term_text(term: &MIRTerm, place: &impl Fn(MIRRegId) -> String) -> String {
    match term {
        MIRTerm::Goto(to) => format!("jmp .L{}", to),
        MIRTerm::Branch { cond, then, els } => {
            format!("br {}, .L{}, .L{}", place(*cond), then, els)
        }
        MIRTerm::Return(Some(reg)) => format!("ret {}", place(*reg)),
        MIRTerm::Return(None) => "ret".to_string(),
        MIRTerm::Unreachable => "unreachable".to_string(),
    }
}

// ---- Where everything in the frame sits ------------------------------------

// The frame is written downwards from the frame pointer, so a slot is named by
// how far below it is: `[fp-8]` is the first word. Each one is put where its
// own alignment allows, and the whole is rounded up to what the machine keeps
// the stack aligned to.
//
// This is worked out here rather than in `regalloc` because it is a fact about
// writing the frame down and not about deciding what goes in it -- the
// allocator says a value is in slot three, and which byte slot three starts at
// changes nothing it decided.
pub fn frame(slots: &[MIRSlot], m: Machine) -> (Vec<usize>, usize) {
    let mut at = 0usize;
    let mut offsets = Vec::with_capacity(slots.len());
    for slot in slots {
        let align = slot.align.max(1);
        at = (at + slot.bytes).div_ceil(align) * align;
        offsets.push(at);
    }
    let stack = m.stack.max(1);
    (offsets, at.div_ceil(stack) * stack)
}

// ---- Spelling ---------------------------------------------------------------

fn un(op: MIRUnOp) -> &'static str {
    match op {
        MIRUnOp::Neg => "neg",
        MIRUnOp::FNeg => "fneg",
        MIRUnOp::Not => "not",
    }
}

fn bin(op: MIRBinOp) -> &'static str {
    use MIRBinOp::*;
    match op {
        Add => "add",
        Sub => "sub",
        Mul => "mul",
        SDiv => "sdiv",
        UDiv => "udiv",
        SRem => "srem",
        URem => "urem",
        And => "and",
        Or => "or",
        Xor => "xor",
        Shl => "shl",
        LShr => "lshr",
        AShr => "ashr",
        FAdd => "fadd",
        FSub => "fsub",
        FMul => "fmul",
        FDiv => "fdiv",
    }
}

fn cmp(op: MIRCmpOp) -> &'static str {
    use MIRCmpOp::*;
    match op {
        Eq => "eq",
        Ne => "ne",
        SLt => "slt",
        SLe => "sle",
        SGt => "sgt",
        SGe => "sge",
        ULt => "ult",
        ULe => "ule",
        UGt => "ugt",
        UGe => "uge",
        FEq => "feq",
        FNe => "fne",
        FLt => "flt",
        FLe => "fle",
        FGt => "fgt",
        FGe => "fge",
    }
}

// A width and whether the top bit means anything, which is what a conversion
// has to say at both ends: widening a signed four-byte value and widening an
// unsigned one are two different instructions.
fn scalar(held: MIRScalar) -> String {
    match held {
        MIRScalar::Int { bytes, signed: true } => format!("i{}", bytes * 8),
        MIRScalar::Int { bytes, signed: false } => format!("u{}", bytes * 8),
        MIRScalar::Float { bytes } => format!("f{}", bytes * 8),
    }
}

// The bytes of a literal, as something a reader can recognise. Printable ASCII
// is shown as itself and everything else by its number, because a pool entry
// holding a newline should not put one in the listing.
fn quoted(bytes: &[u8]) -> String {
    let mut out = String::from("\"");
    for &byte in bytes {
        match byte {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            0x20..=0x7e => out.push(byte as char),
            _ => {
                let _ = write!(out, "\\x{:02x}", byte);
            }
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests;
