// What the MIR is made of, in the shape it has while it is still a graph.
//
// The SIR's vocabulary is the language's and this one is the machine's, and
// almost every difference between them is one of those two words. A `Field` in
// the SIR names a field; here there is an address and a number of bytes from
// it. A `Binary` there carries `TIRBinOp::Div`, which means whichever division
// the operands' type called for; here it is `SDiv` or `UDiv`, because those are
// two instructions and something has already decided which. A `Drop` there is a
// release; here it is a call, like any other call.
//
// What does *not* change is the shape. The blocks are the SIR's blocks, the
// edges are its edges, and a register is defined once exactly as a value was --
// so this is still SSA, and the phis are still here. Dropping either on the way
// in would mean throwing away the one property that makes the graph worth
// having and then rebuilding it to allocate against. `mir::linear` is where
// both go, because that is where an edge becomes an order and a move has
// somewhere to be put.
//
// Registers are as many as the body wants. Nothing here knows how many a
// machine has -- that is `mir::machine`'s, and it is asked in `mir::regalloc`
// and nowhere before. A register in this file is a name for one value, and the
// difference between that and a machine register is the whole of what the
// second stage is for.
//
// Two things are here that the SIR had no need of. A body carries its
// `symbol`, because the thing that reads a MIR is a linker and a linker knows
// nothing else about it. And the frame is a list of slots with sizes rather
// than of typed locals: by here a type has been turned into a number of bytes
// and an alignment, and nothing downstream may ask which type it was.

use super::machine::Class;

// Numbered within the body that holds them, as the SIR's are. Nothing outside a
// body names a register, a block or a slot of its frame.
pub type MIRRegId = usize;
pub type MIRBlockId = usize;
pub type MIRFrameId = usize;
// The one id that is the program's, and it is not the SIR's: monomorphising
// makes several bodies out of one, so the numbering starts again here.
pub type MIRBodyId = usize;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct MIRProgram {
    pub bodies: Vec<MIRBody>,
    // What a literal too big to stand in an instruction is kept in. A string is
    // the only one so far: `Const` holds a number, and the bytes of "hello" are
    // not a number.
    pub pool:   Vec<MIRConstant>,
    // The globals, which are the one thing here that is neither code nor a
    // constant. A global is a *place* (§8): it may be assigned to, so it cannot
    // go in the pool beside the strings -- that is `.rodata` and a write to it
    // faults -- and it has to exist even where nothing initialises it, because
    // a program that only ever writes one still needs somewhere to write.
    pub data:   Vec<MIRGlobal>,
}

// One global, and the bytes it starts as.
//
// The image is as wide as the type and no wider, which is what `.size` will
// say; a global nothing initialised is that many zeroes. Kept as bytes rather
// than as a value because by here a type is three numbers and not a type
// (`MIRReg`), and the one thing a data segment is is bytes.
#[derive(Debug, Clone, PartialEq)]
pub struct MIRGlobal {
    pub symbol: String,
    pub bytes:  Vec<u8>,
    pub align:  usize,
}

// One thing in the constant pool, under the symbol that reaches it.
#[derive(Debug, Clone, PartialEq)]
pub struct MIRConstant {
    pub symbol: String,
    pub held:   MIRConstBody,
}

// What is under a constant's name. Two kinds, and the second is the one this
// compiler cannot write the bytes of: an address is not known until the linker
// has run, so a table of them is a run of *names* and a relocation apiece.
//
// That is what a trait object's table is -- one address per member of the
// trait, in the order the trait declared them -- and it is the first thing here
// to want one. A `str` global wants the same and does not have it yet (§8).
#[derive(Debug, Clone, PartialEq)]
pub enum MIRConstBody {
    Bytes(Vec<u8>),
    Words(Vec<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MIRBody {
    // What the linker calls it: the mangling `sema::names::Mangler` works out,
    // or the exact name a `@symbol` gave instead.
    pub symbol: String,
    pub entry:  MIRBlockId,
    pub blocks: Vec<MIRBlock>,
    // Every register the body makes, by the id that names it. An instruction's
    // `def` indexes this and so does a phi's, which is what keeps "defined
    // once" a fact about the arena rather than only about the code.
    pub regs:   Vec<MIRReg>,
    pub frame:  Vec<MIRSlot>,
    // What the caller filled, in the order the signature declared them. Made
    // by no instruction, exactly as the SIR's parameters are.
    pub params: Vec<MIRRegId>,
}

// One value, and what a machine would need to hold it.
//
// A type is gone by here. What is left of it is three numbers: which file the
// value lives in, how wide it is, and how many of it there are. That is all an
// allocator asks and all a listing shows, and it is deliberately not enough to
// work out what was written -- a `i32`, a `char` and a four-byte structure in a
// register are the same thing to everything downstream.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MIRReg {
    pub class: Class,
    pub bytes: usize,
    // More than one where a rewrite in `sir::opt` widened it, carried through
    // unchanged. One for everything else.
    pub lanes: usize,
    pub line:  usize,
    pub col:   usize,
}

impl MIRReg {
    // One of its width, which is what all but the widened ones are.
    pub fn one(class: Class, bytes: usize, line: usize, col: usize) -> MIRReg {
        MIRReg { class, bytes, lanes: 1, line, col }
    }
}

// Somewhere in the frame. Every local the SIR still had in a slot is one, and
// so is every aggregate the lowering had to build somewhere, and so is every
// register the allocator could not find room for.
#[derive(Debug, Clone, PartialEq)]
pub struct MIRSlot {
    pub bytes: usize,
    pub align: usize,
    // For the listing to name it by. A slot the allocator made is named after
    // the register it stands in for.
    pub name:  String,
    // Whether the allocator made it rather than the program. The two are laid
    // out the same way and are worth telling apart in a listing: a frame that
    // is mostly spills says something a frame that is mostly locals does not.
    pub spill: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MIRBlock {
    // Read before the block begins, all at once, exactly as the SIR's are.
    pub phis:  Vec<MIRPhi>,
    pub insts: Vec<MIRInst>,
    pub term:  MIRTerm,
    pub line:  usize,
    pub col:   usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MIRPhi {
    pub def:   MIRRegId,
    pub edges: Vec<(MIRBlockId, MIRRegId)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MIRInst {
    // What it makes, where it makes something. A store makes nothing and a call
    // whose answer nobody wanted makes nothing either.
    pub def:  Option<MIRRegId>,
    pub kind: MIRInstKind,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MIRInstKind {
    // ---- Values ------------------------------------------------------------
    Const(MIRConst),
    // One register into another. The lowering makes few of these; `mir::linear`
    // makes one per phi edge, which is most of them.
    Move(MIRRegId),
    Un {
        op:      MIRUnOp,
        operand: MIRRegId,
    },
    Bin {
        op:  MIRBinOp,
        lhs: MIRRegId,
        rhs: MIRRegId,
    },
    // Answers with a one or a nought, which is why it is not a `Bin`: what it
    // makes has nothing to do with what it took.
    Cmp {
        op:  MIRCmpOp,
        lhs: MIRRegId,
        rhs: MIRRegId,
    },
    // Between widths and between the two files. Both ends are named because
    // widening a signed four-byte value and widening an unsigned one are two
    // different instructions, and by here nothing can look the type up again.
    Convert {
        of:   MIRRegId,
        from: MIRScalar,
        to:   MIRScalar,
    },

    // ---- Addresses ---------------------------------------------------------
    // Where a slot of this frame begins.
    Frame(MIRFrameId),
    // Where something the linker knows about begins: another body, a global, a
    // string a literal put in the constant pool.
    Symbol(String),
    // A fixed number of bytes along. This is what every field read comes to:
    // `layout` turned the field's number into this number.
    Offset {
        base:  MIRRegId,
        bytes: i64,
    },
    // A number of bytes along that is not known until it runs, which is what an
    // index is. `scale` is the stride of the element, so the address is
    // `base + index * scale`.
    Scaled {
        base:  MIRRegId,
        index: MIRRegId,
        scale: usize,
    },

    // ---- Memory ------------------------------------------------------------
    Load {
        from:  MIRRegId,
        bytes: usize,
    },
    Store {
        to:    MIRRegId,
        value: MIRRegId,
        bytes: usize,
    },
    // A whole aggregate from one address to another. Not a `Load` and a `Store`
    // because what it moves does not fit in a register, which is exactly the
    // case those two cannot express.
    Copy {
        to:    MIRRegId,
        from:  MIRRegId,
        bytes: usize,
    },

    // ---- Calls -------------------------------------------------------------
    // Every call, whatever it was in the SIR. A method, a release, a map being
    // built and a closure being made are all this by the time they are here --
    // which is the point of lowering them, and the reason there is no second
    // instruction for any of them.
    Call {
        to:   MIRCallee,
        args: Vec<MIRRegId>,
    },

    // ---- Several at once ---------------------------------------------------
    // The SIR's four, carried down. A widened value is still widened: nothing
    // between here and a machine would gain by taking one apart, and `lanes` on
    // a register says which ones they are.
    Pack(Vec<MIRRegId>),
    Lane {
        of: MIRRegId,
        at: usize,
    },
    VecLoad {
        from:  MIRRegId,
        bytes: usize,
        lanes: usize,
    },
    VecStore {
        to:    MIRRegId,
        value: MIRRegId,
    },

    // A register read on a path that never wrote it. `sema` is where a read of
    // an unset name is turned down, so what is left here is to say plainly that
    // there is nothing rather than to invent a nought.
    Undef,
}

// What a call names. A declaration is a symbol and is known before anything
// runs; a closure or a fn held in a variable is an address that is not.
#[derive(Debug, Clone, PartialEq)]
pub enum MIRCallee {
    Symbol(String),
    Reg(MIRRegId),
}

// What fits in an instruction rather than in memory. A string is not here: it
// does not fit, so it goes in the constant pool and what stands in the
// instruction is the `Symbol` naming it.
#[derive(Debug, Clone, PartialEq)]
pub enum MIRConst {
    Int(i64),
    Float(f64),
}

// The machine's idea of what a value is, which is a width and whether the top
// bit means anything. Two four-byte integers that differ only in sign are one
// `bytes` and two `signed`, and that difference is the whole of why this is not
// just a number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MIRScalar {
    Int { bytes: usize, signed: bool },
    Float { bytes: usize },
}

impl MIRScalar {
    pub fn bytes(&self) -> usize {
        match self {
            MIRScalar::Int { bytes, .. } | MIRScalar::Float { bytes } => *bytes,
        }
    }

    pub fn class(&self) -> Class {
        match self {
            MIRScalar::Int { .. } => Class::Int,
            MIRScalar::Float { .. } => Class::Float,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MIRUnOp {
    // Arithmetic, and the two files need different instructions for it.
    Neg,
    FNeg,
    // Every bit turned over. `!` over a boolean is this as well: a boolean is a
    // nought or a one, and the lowering compares rather than complements.
    Not,
}

// The operators the machine actually has, which is more of them than the source
// has. `/` is one thing to write and two to run, and which of the two was meant
// is settled by the operands' type -- once, in the lowering, rather than at
// every pass that looks at one afterwards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MIRBinOp {
    Add,
    Sub,
    Mul,
    SDiv,
    UDiv,
    SRem,
    URem,
    And,
    Or,
    Xor,
    Shl,
    // Shifting right brings in noughts or brings in the sign, and which is
    // wanted is the operand's signedness. Two instructions everywhere.
    LShr,
    AShr,
    FAdd,
    FSub,
    FMul,
    FDiv,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MIRCmpOp {
    Eq,
    Ne,
    // Signed and unsigned orderings are different instructions; equality is
    // not, which is why there are only two of those and eight of these.
    SLt,
    SLe,
    SGt,
    SGe,
    ULt,
    ULe,
    UGt,
    UGe,
    FEq,
    FNe,
    FLt,
    FLe,
    FGt,
    FGe,
}

// How a block ends. The SIR's four, unchanged: nothing lowering does adds a way
// out of a block, and the two the GIR had that the SIR wrote away are still
// written away.
#[derive(Debug, Clone, PartialEq)]
pub enum MIRTerm {
    Goto(MIRBlockId),
    Branch {
        cond: MIRRegId,
        then: MIRBlockId,
        els:  MIRBlockId,
    },
    Return(Option<MIRRegId>),
    Unreachable,
}

impl MIRTerm {
    pub fn targets(&self) -> Vec<MIRBlockId> {
        match self {
            MIRTerm::Goto(to) => vec![*to],
            MIRTerm::Branch { then, els, .. } => vec![*then, *els],
            MIRTerm::Return(_) | MIRTerm::Unreachable => Vec::new(),
        }
    }

    pub fn targets_mut(&mut self) -> Vec<&mut MIRBlockId> {
        match self {
            MIRTerm::Goto(to) => vec![to],
            MIRTerm::Branch { then, els, .. } => vec![then, els],
            MIRTerm::Return(_) | MIRTerm::Unreachable => Vec::new(),
        }
    }

    // What it reads, which is the condition or nothing.
    pub fn uses(&self) -> Vec<MIRRegId> {
        match self {
            MIRTerm::Branch { cond, .. } => vec![*cond],
            MIRTerm::Return(Some(reg)) => vec![*reg],
            _ => Vec::new(),
        }
    }

    pub fn uses_mut(&mut self) -> Vec<&mut MIRRegId> {
        match self {
            MIRTerm::Branch { cond, .. } => vec![cond],
            MIRTerm::Return(Some(reg)) => vec![reg],
            _ => Vec::new(),
        }
    }
}

impl MIRBody {
    // Which blocks reach which, by the block reached. One entry per block, and
    // a block nothing reaches has an empty one.
    pub fn preds(&self) -> Vec<Vec<MIRBlockId>> {
        let mut out = vec![Vec::new(); self.blocks.len()];
        for (at, block) in self.blocks.iter().enumerate() {
            for to in block.term.targets() {
                if let Some(held) = out.get_mut(to) {
                    if !held.contains(&at) {
                        held.push(at);
                    }
                }
            }
        }
        out
    }

    // Which blocks the entry reaches. Nothing here shrinks a block arena, so a
    // block a rewrite emptied is still in it, and every count that means
    // anything is over these rather than over all of them.
    pub fn live(&self) -> Vec<bool> {
        let mut on = vec![false; self.blocks.len()];
        let mut todo = vec![self.entry];
        while let Some(at) = todo.pop() {
            if at >= on.len() || on[at] {
                continue;
            }
            on[at] = true;
            todo.extend(self.blocks[at].term.targets());
        }
        on
    }
}

// What an instruction reads. Written directly beside `uses_mut` on purpose: the
// two have to agree, and a kind added to one and not the other is a mistake
// that is visible only if they can be read together. The SIR's pair says the
// same thing for the same reason.
pub fn uses(kind: &MIRInstKind) -> Vec<MIRRegId> {
    use MIRInstKind::*;
    match kind {
        Const(_) | Frame(_) | Symbol(_) | Undef => Vec::new(),
        Move(of) | Un { operand: of, .. } | Lane { of, .. } => vec![*of],
        Offset { base, .. } => vec![*base],
        Load { from, .. } | VecLoad { from, .. } => vec![*from],
        Bin { lhs, rhs, .. } | Cmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Convert { of, .. } => vec![*of],
        Scaled { base, index, .. } => vec![*base, *index],
        Store { to, value, .. } | VecStore { to, value } => vec![*to, *value],
        Copy { to, from, .. } => vec![*to, *from],
        Pack(of) => of.clone(),
        Call { to, args } => {
            let mut held = match to {
                MIRCallee::Reg(reg) => vec![*reg],
                MIRCallee::Symbol(_) => Vec::new(),
            };
            held.extend(args.iter().copied());
            held
        }
    }
}

pub fn uses_mut(kind: &mut MIRInstKind) -> Vec<&mut MIRRegId> {
    use MIRInstKind::*;
    match kind {
        Const(_) | Frame(_) | Symbol(_) | Undef => Vec::new(),
        Move(of) | Un { operand: of, .. } | Lane { of, .. } => vec![of],
        Offset { base, .. } => vec![base],
        Load { from, .. } | VecLoad { from, .. } => vec![from],
        Bin { lhs, rhs, .. } | Cmp { lhs, rhs, .. } => vec![lhs, rhs],
        Convert { of, .. } => vec![of],
        Scaled { base, index, .. } => vec![base, index],
        Store { to, value, .. } | VecStore { to, value } => vec![to, value],
        Copy { to, from, .. } => vec![to, from],
        Pack(of) => of.iter_mut().collect(),
        Call { to, args } => {
            let mut held = match to {
                MIRCallee::Reg(reg) => vec![reg],
                MIRCallee::Symbol(_) => Vec::new(),
            };
            held.extend(args.iter_mut());
            held
        }
    }
}
