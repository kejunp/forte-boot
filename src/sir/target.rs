// What the machine can do, as far as anything here needs to know.
//
// Every pass before this one is about the program. This is the first thing in
// the compiler that is about the *machine*, and it is here because one rewrite
// cannot be made without it: running the turns of a loop several at a time
// needs to know how many fit, which instructions exist over several at once,
// and whether doing it that way is quicker -- and not one of those three is a
// fact about the source.
//
// There is no back end, so nothing here emits anything. What this is instead
// is a description: a handful of numbers and flags that say what a machine
// would be able to do, so that `sir::opt` can decide rather than guess. That
// is a smaller thing than a back end and a much larger thing than a constant
// called four, which is what stood here before.
//
// The descriptions are deliberately coarse. A vector register is so many bytes
// wide; a multiply over the wider integers exists or it does not; putting one
// lane in by hand costs so much. Nothing here models a pipeline, and nothing
// should until something measures one -- the point is to have an answer that
// can be wrong in a way that is written down, rather than one that is wrong in
// a way that is not.
//
// `Target::none` is the honest default for a machine nobody named: no vectors
// at all, so nothing is widened. What is actually defaulted to is the machine
// this compiler is running on, because a compiler with no back end that is
// asked to widen has to widen for something, and that is the only machine it
// knows anything about.

use crate::tir::tir_nodes::{TIRBinOp, TIRPrim, TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRProgram, Ty, TyId};

use super::sir_nodes::SIRInstKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Target {
    pub name:   &'static str,
    // How many bytes a vector register holds. Nought for a machine with no
    // vectors, which is what makes "do not widen anything" a target rather
    // than a flag somewhere else.
    pub bytes:  usize,
    // Whether there is a multiply over the eight-byte integers. There is not
    // on most of what calls itself SIMD: the narrow ones have had one for
    // thirty years and the wide one arrived with AVX-512.
    pub mul8:   bool,
    // Whether a shift may be by a different amount in each lane. Uniform
    // shifts are older than variable ones by about a decade.
    pub shifts: bool,
    // What putting one lane in by hand costs, against one ordinary
    // instruction. This is the number that decides most of it: a group whose
    // operands have to be gathered one at a time is a group that mostly does
    // not pay.
    pub insert: usize,
}

// No vectors. Everything else here is measured against this one: a target that
// widens nothing leaves the program exactly as the rewrites before it left it.
pub const NONE: Target =
    Target { name: "none", bytes: 0, mul8: false, shifts: false, insert: 1 };

// The baseline sixteen bytes, which is SSE2 on x86-64 and NEON on aarch64 --
// both of them old enough that nothing this would be compiled for lacks them.
pub const X86_64: Target =
    Target { name: "x86-64", bytes: 16, mul8: false, shifts: false, insert: 1 };
pub const AARCH64: Target =
    Target { name: "aarch64", bytes: 16, mul8: false, shifts: true, insert: 1 };

// RV64GC, which is what a Linux userland is built for and has no vectors at
// all. The vector extension is a separate one, it is optional, and it is not
// the fixed-width kind either of the other two are -- so a target that assumed
// sixteen bytes here would be assuming something about an extension that may
// not be there and does not work that way when it is.
pub const RISCV64: Target =
    Target { name: "riscv64", bytes: 0, mul8: false, shifts: false, insert: 1 };

// Thirty-two, which is AVX2: twice as wide, and shifts that may differ by lane.
pub const X86_64_V3: Target =
    Target { name: "x86-64-v3", bytes: 32, mul8: false, shifts: true, insert: 2 };

// And sixty-four, which is AVX-512, where the wide multiply finally arrived.
pub const X86_64_V4: Target =
    Target { name: "x86-64-v4", bytes: 64, mul8: true, shifts: true, insert: 3 };

impl Default for Target {
    fn default() -> Target {
        host()
    }
}

// The machine this compiler is running on, at its baseline. Baseline and not
// whatever this build was told it could use: `cfg!(target_feature)` says what
// the compiler compiling *this* was allowed to emit, which is a fact about how
// the compiler was built and not about where its output will run.
pub fn host() -> Target {
    if cfg!(target_arch = "x86_64") {
        X86_64
    } else if cfg!(target_arch = "aarch64") {
        AARCH64
    } else {
        NONE
    }
}

pub fn of(name: &str) -> Option<Target> {
    match name {
        "none" | "generic" => Some(NONE),
        "host" | "native" => Some(host()),
        "x86-64" | "x86-64-v2" => Some(X86_64),
        "x86-64-v3" => Some(X86_64_V3),
        "x86-64-v4" => Some(X86_64_V4),
        "aarch64" => Some(AARCH64),
        "riscv64" | "riscv" => Some(RISCV64),
        _ => None,
    }
}

// Every name `of` answers to, for a message that has to list them.
pub const NAMES: &[&str] =
    &["none", "host", "x86-64", "x86-64-v3", "x86-64-v4", "aarch64", "riscv64"];

impl Target {
    // How many of a thing that size fit in one register. One -- meaning "no
    // more than it already was" -- where there are no vectors, or where one of
    // the things is as wide as the whole register.
    pub fn lanes(&self, bytes: usize) -> usize {
        if self.bytes == 0 || bytes == 0 {
            return 1;
        }
        (self.bytes / bytes).max(1)
    }

    // Whether the machine can do this to several at once.
    //
    // The list is short on purpose, and what is missing from it is as
    // deliberate as what is in it. There is no integer divide in any of these
    // machines -- not one of them has ever had one -- so four divisions stay
    // four divisions however neatly they line up. Nor is there a cast: what a
    // narrowing or widening conversion costs over a vector is a question with
    // a different answer per pair of types, and answering it wrongly is worse
    // than leaving the conversions where they are.
    pub fn does(&self, kind: &SIRInstKind, p: TIRPrim, lanes: usize) -> bool {
        if self.bytes == 0 || lanes < 2 {
            return false;
        }
        let width = match size_of(p) {
            Some(width) => width,
            None => return false,
        };
        match kind {
            SIRInstKind::Unary { op, .. } => match op {
                TIRUnaryOp::Not => integer(p) || p == TIRPrim::Bool,
                TIRUnaryOp::Neg => integer(p) || floating(p),
                // A reference is an address, and there is nothing to take the
                // address of several values at once -- nor to read through
                // several at once, which is a gather and is not this.
                TIRUnaryOp::Ref(_) | TIRUnaryOp::Addr | TIRUnaryOp::Deref => false,
            },
            SIRInstKind::Binary { op, .. } => match op {
                TIRBinOp::Add | TIRBinOp::Sub => integer(p) || floating(p),
                // The narrow multiplies are as old as the registers; the wide
                // one is not.
                TIRBinOp::Mul => {
                    (integer(p) && (width < 8 || self.mul8)) || floating(p)
                }
                TIRBinOp::Div => floating(p),
                TIRBinOp::Rem => false,
                TIRBinOp::Shl | TIRBinOp::Shr => integer(p) && self.shifts,
                TIRBinOp::BitAnd | TIRBinOp::BitOr | TIRBinOp::BitXor => {
                    integer(p) || p == TIRPrim::Bool
                }
                // A comparison over a vector answers with one bit per lane,
                // which is what every one of these machines gives back.
                TIRBinOp::Eq
                | TIRBinOp::Ne
                | TIRBinOp::Lt
                | TIRBinOp::Gt
                | TIRBinOp::Le
                | TIRBinOp::Ge => integer(p) || floating(p),
                // The logical three are branches by the time they are here,
                // barring `^^`, which is the bitwise one over booleans.
                TIRBinOp::And | TIRBinOp::Or | TIRBinOp::Xor => p == TIRPrim::Bool,
            },
            // Everything else is a shape rather than an operation: reading a
            // field, building a structure, calling something. None of them is
            // one instruction over several values on any machine here.
            _ => false,
        }
    }

    // What one wide instruction of this kind costs, against one ordinary
    // instruction as the unit.
    //
    // One, for all of them, and that is not laziness: a vector add is one
    // instruction and so is a scalar add, and the whole of what makes widening
    // worth doing is that the wide one did four adds. The costs that are not
    // one are the ones that put a vector *together* -- see `insert` -- which
    // is why a group is worth making only when its operands were already in
    // the right shape.
    pub fn cost(&self, _kind: &SIRInstKind) -> usize {
        1
    }
}

fn integer(p: TIRPrim) -> bool {
    use TIRPrim::*;
    matches!(p, I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128)
}

fn floating(p: TIRPrim) -> bool {
    matches!(p, TIRPrim::F32 | TIRPrim::F64)
}

// How many bytes one of them takes.
//
// A primitive's width is the language's and not the machine's -- an `i32` is
// four bytes wherever it is compiled, which is what naming it after its width
// says (§6). Everything else is `None`: what a structure or a run takes is a
// layout question nothing in this compiler has answered yet, and a vector of
// them is not a thing any of these machines has anyway.
pub fn size_of(p: TIRPrim) -> Option<usize> {
    use TIRPrim::*;
    Some(match p {
        I8 | U8 | Bool => 1,
        I16 | U16 => 2,
        I32 | U32 | F32 => 4,
        // A `char` is one Unicode scalar value, which is four bytes wide
        // however few of them are used.
        Char => 4,
        I64 | U64 | F64 => 8,
        I128 | U128 => 16,
        Str | Null | Never => return None,
    })
}

// The same, for a type rather than a primitive.
pub fn size(ttir: &TTIRProgram, ty: TyId) -> Option<usize> {
    match ttir.types.get(ty)? {
        Ty::Prim(p) => size_of(*p),
        _ => None,
    }
}

pub fn prim(ttir: &TTIRProgram, ty: TyId) -> Option<TIRPrim> {
    match ttir.types.get(ty)? {
        Ty::Prim(p) => Some(*p),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
