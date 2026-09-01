// What the machine is, as far as anything that has to emit for it needs to
// know.
//
// `sir::target` is about the machine too, and this is not a second copy of it.
// That one answers one question -- how wide a vector is and what may be done to
// one -- because one rewrite could not be made without it, and its header says
// plainly that it is a description and not a back end. What is here is the rest
// of the description, and it is wanted for the opposite reason: a pass that
// emits cannot leave a single one of these open. How wide a pointer is settles
// what an address costs to hold; which registers exist settles how many values
// may be in one at a time; which of them a call keeps settles what has to be
// put somewhere before one.
//
// So `Target` stays where it is and is carried along here rather than folded
// in. Widening it into an ABI would take a file that says what it is for and
// make it a file that says two things.
//
// The register lists are the allocatable ones and nothing else. A stack pointer
// and a frame pointer are not in them: they hold what they hold for the whole
// of a body, and an allocator handed one would eventually give it away. They
// are named separately, because the frame has to be written about.
//
// Two machines, and they are the two `sir::target` already knows. Every
// `--target` name maps onto one of them: the vector variants of x86-64 differ
// in what a vector register holds and not at all in what an integer one is, so
// they are one machine here carrying a different `Target`.

use crate::sir::target::{self, Target};

// One register, by the name a listing calls it and the kind of value it holds.
// A name and not a number: nothing here encodes anything, and the only reader
// is a person looking at a listing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reg {
    pub name:  &'static str,
    pub class: Class,
}

// Which file a register comes out of. The two are separate everywhere, and a
// value belongs to one of them by its type rather than by anything an
// allocator decides -- so this is settled at lowering and only read here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Class {
    Int,
    Float,
}

const fn int(name: &'static str) -> Reg {
    Reg { name, class: Class::Int }
}

const fn float(name: &'static str) -> Reg {
    Reg { name, class: Class::Float }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Machine {
    pub name:      &'static str,
    // A pointer, in bytes. Everything that holds an address is this wide, and
    // so is the length beside a pointer in a run or a string.
    pub word:      usize,
    // What the stack pointer stays a multiple of across a call. The frame is
    // rounded up to it.
    pub stack:     usize,
    // What holds the frame, for the listing to write an offset against.
    pub frame:     Reg,
    // Every register an allocator may hand out, in the order it prefers them.
    pub ints:      &'static [Reg],
    pub floats:    &'static [Reg],
    // Where a call's arguments go, in the order the signature declares them,
    // and where its answer comes back. Two lists because the two files are
    // counted separately: the third integer argument goes in the third
    // integer register however many floats came before it.
    pub args:      &'static [Reg],
    pub fargs:     &'static [Reg],
    pub ret:       Reg,
    pub fret:      Reg,
    // What survives a call and what does not. Every allocatable register is in
    // exactly one of the two, which is the invariant `tests.rs` checks: a
    // register in neither would be one nothing knows what to do with across a
    // call, and one in both is a contradiction.
    pub saved:     &'static [Reg],
    pub clobbered: &'static [Reg],
    // What a vector holds here, which is the one machine question that was
    // already answered.
    pub vectors:   Target,
}

// ---- x86-64 ----------------------------------------------------------------

// The System V order. `rsp` and `rbp` are missing on purpose -- see the header.
const X86_INTS: &[Reg] = &[
    int("rax"), int("rcx"), int("rdx"), int("rsi"), int("rdi"),
    int("r8"), int("r9"), int("r10"), int("r11"),
    int("rbx"), int("r12"), int("r13"), int("r14"), int("r15"),
];

const X86_FLOATS: &[Reg] = &[
    float("xmm0"), float("xmm1"), float("xmm2"), float("xmm3"),
    float("xmm4"), float("xmm5"), float("xmm6"), float("xmm7"),
    float("xmm8"), float("xmm9"), float("xmm10"), float("xmm11"),
    float("xmm12"), float("xmm13"), float("xmm14"), float("xmm15"),
];

const X86_ARGS: &[Reg] =
    &[int("rdi"), int("rsi"), int("rdx"), int("rcx"), int("r8"), int("r9")];

const X86_FARGS: &[Reg] = &[
    float("xmm0"), float("xmm1"), float("xmm2"), float("xmm3"),
    float("xmm4"), float("xmm5"), float("xmm6"), float("xmm7"),
];

const X86_SAVED: &[Reg] =
    &[int("rbx"), int("r12"), int("r13"), int("r14"), int("r15")];

// Every allocatable register that is not saved. The floats are all here: on
// this ABI not one of them survives a call.
const X86_CLOBBERED: &[Reg] = &[
    int("rax"), int("rcx"), int("rdx"), int("rsi"), int("rdi"),
    int("r8"), int("r9"), int("r10"), int("r11"),
    float("xmm0"), float("xmm1"), float("xmm2"), float("xmm3"),
    float("xmm4"), float("xmm5"), float("xmm6"), float("xmm7"),
    float("xmm8"), float("xmm9"), float("xmm10"), float("xmm11"),
    float("xmm12"), float("xmm13"), float("xmm14"), float("xmm15"),
];

// ---- aarch64 ---------------------------------------------------------------

// `x29` is the frame pointer and `x30` the link register, so neither is handed
// out. `x18` is left out as well: it is the platform's on more than one system
// and a compiler that does not know which cannot use it.
const ARM_INTS: &[Reg] = &[
    int("x0"), int("x1"), int("x2"), int("x3"), int("x4"), int("x5"),
    int("x6"), int("x7"), int("x9"), int("x10"), int("x11"), int("x12"),
    int("x13"), int("x14"), int("x15"), int("x19"), int("x20"), int("x21"),
    int("x22"), int("x23"), int("x24"), int("x25"), int("x26"), int("x27"),
    int("x28"),
];

const ARM_FLOATS: &[Reg] = &[
    float("d0"), float("d1"), float("d2"), float("d3"),
    float("d4"), float("d5"), float("d6"), float("d7"),
    float("d8"), float("d9"), float("d10"), float("d11"),
    float("d12"), float("d13"), float("d14"), float("d15"),
];

const ARM_ARGS: &[Reg] = &[
    int("x0"), int("x1"), int("x2"), int("x3"),
    int("x4"), int("x5"), int("x6"), int("x7"),
];

const ARM_FARGS: &[Reg] = &[
    float("d0"), float("d1"), float("d2"), float("d3"),
    float("d4"), float("d5"), float("d6"), float("d7"),
];

// `x19` through `x28`, and the bottom half of each of `d8` through `d15` --
// which this does not model, so they are counted as saved whole. That is the
// safe direction to be wrong in: a value kept across a call is kept.
const ARM_SAVED: &[Reg] = &[
    int("x19"), int("x20"), int("x21"), int("x22"), int("x23"),
    int("x24"), int("x25"), int("x26"), int("x27"), int("x28"),
    float("d8"), float("d9"), float("d10"), float("d11"),
    float("d12"), float("d13"), float("d14"), float("d15"),
];

const ARM_CLOBBERED: &[Reg] = &[
    int("x0"), int("x1"), int("x2"), int("x3"), int("x4"), int("x5"),
    int("x6"), int("x7"), int("x9"), int("x10"), int("x11"), int("x12"),
    int("x13"), int("x14"), int("x15"),
    float("d0"), float("d1"), float("d2"), float("d3"),
    float("d4"), float("d5"), float("d6"), float("d7"),
];

// ---- The machines ----------------------------------------------------------

pub const X86_64: Machine = Machine {
    name:      "x86-64",
    word:      8,
    stack:     16,
    frame:     int("rbp"),
    ints:      X86_INTS,
    floats:    X86_FLOATS,
    args:      X86_ARGS,
    fargs:     X86_FARGS,
    ret:       int("rax"),
    fret:      float("xmm0"),
    saved:     X86_SAVED,
    clobbered: X86_CLOBBERED,
    vectors:   target::X86_64,
};

pub const AARCH64: Machine = Machine {
    name:      "aarch64",
    word:      8,
    stack:     16,
    frame:     int("x29"),
    ints:      ARM_INTS,
    floats:    ARM_FLOATS,
    args:      ARM_ARGS,
    fargs:     ARM_FARGS,
    ret:       int("x0"),
    fret:      float("d0"),
    saved:     ARM_SAVED,
    clobbered: ARM_CLOBBERED,
    vectors:   target::AARCH64,
};

impl Machine {
    // The machine a `--target` names. The vector variants of x86-64 are one
    // machine with a different `Target` carried along, which is the whole of
    // why this takes a `Target` and not a name: `sir::target::of` has already
    // turned the name into the answer about vectors, and what is left is which
    // register file goes with it.
    //
    // A target that names no vectors at all names no architecture either, so
    // the machine this compiler is running on is what stands in -- the same
    // answer `sir::target::host` gives, and for the same reason.
    pub fn of(t: Target) -> Machine {
        let mut held = match t.name {
            "aarch64" => AARCH64,
            "none" => host(),
            _ => X86_64,
        };
        held.vectors = t;
        held
    }

    // Whether a call leaves this register alone.
    pub fn keeps(&self, reg: Reg) -> bool {
        self.saved.contains(&reg)
    }

    // The file a class is allocated out of.
    pub fn file(&self, class: Class) -> &'static [Reg] {
        match class {
            Class::Int => self.ints,
            Class::Float => self.floats,
        }
    }

    // Where the arguments of a class go, in order.
    pub fn passing(&self, class: Class) -> &'static [Reg] {
        match class {
            Class::Int => self.args,
            Class::Float => self.fargs,
        }
    }

    // Where an answer of a class comes back.
    pub fn answering(&self, class: Class) -> Reg {
        match class {
            Class::Int => self.ret,
            Class::Float => self.fret,
        }
    }
}

// The machine this compiler was built for, where a target names none.
pub fn host() -> Machine {
    if cfg!(target_arch = "aarch64") {
        AARCH64
    } else {
        X86_64
    }
}

impl Default for Machine {
    fn default() -> Machine {
        Machine::of(Target::default())
    }
}

#[cfg(test)]
mod tests;
