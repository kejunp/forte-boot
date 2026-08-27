// The nodes of the SIR: the graph once more, with every value named once and
// named where it is made.
//
//     TTIR -> lower -> GIR -> lower -> SIR
//
// The GIR drew the control flow as edges and left everything else as it found
// it: a slot is written to as often as the source writes to it, and an
// expression is a tree hanging off a statement. Neither survives here. An
// instruction takes values and makes at most one, so a tree becomes the
// straight line that built it, and a name becomes the one instruction that
// made what the name held -- which is what "single static assignment" is.
//
// Two things follow from that, and they are what most of this file is for.
//
// The first is joins. `let x = if c { 1 } else { 2 }` has two instructions
// making what `x` holds and one place that reads it, and reading it cannot be
// either of them. A `phi` stands at the top of the block they meet in and says
// which value came along which edge. It is not an instruction that runs: by
// the time the block has begun the edge is behind it, and every phi in the
// block is read at once, before anything else in it.
//
// The second is the slots that are left. A name whose address was taken is a
// name something else may write through, and there is no one instruction that
// made what it holds. Those stay in memory -- a `Slot`, and the `Load`s and
// `Stores` that reach it -- which is the honest answer rather than a wrong
// one. `sir::lower` puts *every* name in a slot and `sir::promote` takes back
// out the ones it can, so this file has to hold both shapes at once.
//
// What is *not* left is the two terminators the GIR carried unlowered. A
// `Match` is a decision tree of tests and branches here, and a `for` is a
// cursor and a loop -- see `lower.rs` for what each becomes and why.
//
// Types and patterns stay the TTIR's, as they did in the GIR: a `TyId` indexes
// that program's arena, and one answer to what a type is beats two.

#![allow(dead_code)]

use crate::gir::gir_nodes::GIRLocalId;
use crate::tir::tir_nodes::{TIRBinOp, TIRBinding, TIRLit, TIRRangeOp, TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRCapture, TTIRItemId, TyId};

// Numbered within the body that holds them, as a block is: a value is a
// function's, and nothing outside it names one.
pub type SIRValueId = usize;
pub type SIRBlockId = usize;
pub type SIRSlotId = usize;
// The one id that is the program's. A body keeps the number the GIR gave it,
// so a `GIRBodyId` and the `SIRBodyId` it became are the same, and a closure
// found in one is found in the other.
pub type SIRBodyId = usize;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct SIRProgram {
    pub bodies: Vec<SIRBody>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SIRBody {
    pub entry:  SIRBlockId,
    pub blocks: Vec<SIRBlock>,
    // Every value the body makes, by the id that names it. An instruction's
    // `def` indexes this, and so does a phi's; nothing else does, which is what
    // makes "defined once" a fact about the arena and not only about the code.
    pub values: Vec<SIRValue>,
    pub slots:  Vec<SIRSlot>,
    // The values the caller filled, in the order the signature declared them.
    // They are defined by no instruction -- being handed one is not making it
    // -- so they are the one exception to "every value has a def site", and
    // saying so here is what keeps a reader from looking for the missing one.
    pub params: Vec<SIRValueId>,
}

// What a value is, apart from where it was made. A type because every pass
// after this one wants it without walking to the instruction, and a name
// because a promoted slot is worth saying the name of in a message.
#[derive(Debug, Clone, PartialEq)]
pub struct SIRValue {
    pub ty:    TyId,
    // How many of that type it holds. One for every value the lowering makes
    // and every value any pass made until `sir::opt` learned to run the turns
    // of a loop several at a time; more only for the values that rewrite
    // builds.
    //
    // Here rather than in the type arena, and that is a decision rather than
    // an accident. A `Ty` is the checker's, and there is no vector in the
    // language for the checker to have inferred -- so a `Ty::Vector` would be
    // a type no source can write, carried through every pass that matches on
    // one, for the sake of a machine the checker has never heard of. A count
    // beside the type says the same thing where it belongs: this is four of
    // those, and what "those" are is still the one answer the checker gave.
    pub lanes: usize,
    // The GIR slot it came out of, where it came out of one. `sir::promote`
    // sets this as it takes a name out of memory, so a message can still say
    // `x` rather than `%14`.
    pub of:    Option<GIRLocalId>,
    pub line:  usize,
    pub col:   usize,
}

impl SIRValue {
    // One of its type, which is what all but a handful of them are.
    pub fn one(ty: TyId, of: Option<GIRLocalId>, line: usize, col: usize) -> SIRValue {
        SIRValue { ty, lanes: 1, of, line, col }
    }
}

// Somewhere in the frame, for a name a value cannot stand in. `sir::lower`
// makes one for every local it meets and `sir::promote` keeps the ones whose
// address goes somewhere a load or a store is not.
#[derive(Debug, Clone, PartialEq)]
pub struct SIRSlot {
    pub name:      TIRBinding,
    pub ty:        TyId,
    // The GIR local it stands for, where it stands for one. The cursor and the
    // iterable a `for` walks are slots nothing in the source named.
    pub of:        Option<GIRLocalId>,
    pub drops:     bool,
    pub synthetic: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SIRBlock {
    // Read before the block begins, all at once. Order among them means
    // nothing -- two phis in a block cannot read each other, because what they
    // read arrived along an edge and both edges are already behind.
    pub phis:  Vec<SIRPhi>,
    pub insts: Vec<SIRInst>,
    pub term:  SIRTerm,
    pub line:  usize,
    pub col:   usize,
}

// Which value came in along which edge. One entry per predecessor, and every
// predecessor named: a phi missing an edge is a value with no answer on the
// path that takes it.
#[derive(Debug, Clone, PartialEq)]
pub struct SIRPhi {
    pub def:   SIRValueId,
    pub edges: Vec<(SIRBlockId, SIRValueId)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SIRInst {
    // What it makes, where it makes something. A store makes nothing, and a
    // call whose value nobody wanted makes nothing either -- the value is
    // dropped at the instruction rather than by a statement wrapped round it,
    // which is why the GIR's `Eval` has no counterpart here.
    pub def:       Option<SIRValueId>,
    pub kind:      SIRInstKind,
    pub is_unsafe: bool,
    pub line:      usize,
    pub col:       usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SIRInstKind {
    // ---- What the source wrote ------------------------------------------
    Literal(TIRLit),
    Item(TTIRItemId),
    SelfValue,

    Unary {
        op:      TIRUnaryOp,
        operand: SIRValueId,
    },
    // `&&` and `||` were branches by the GIR and are branches still. `^^` is
    // here, for the reason it was there: it settles nothing until both sides
    // are known.
    Binary {
        op:  TIRBinOp,
        lhs: SIRValueId,
        rhs: SIRValueId,
    },
    Cast(SIRValueId),
    Range {
        op:    TIRRangeOp,
        start: Option<SIRValueId>,
        end:   Option<SIRValueId>,
    },

    // Reading out of a value, which is not the same as reading out of a place
    // -- the `*Addr` instructions below are the place. These make a copy of
    // what they found; those say where it is.
    Field {
        base:  SIRValueId,
        index: usize,
    },
    TupleIndex {
        base:  SIRValueId,
        index: u64,
    },
    Index {
        base:  SIRValueId,
        index: SIRValueId,
    },

    Call {
        callee: SIRValueId,
        args:   Vec<SIRValueId>,
    },
    Method {
        recv: SIRValueId,
        item: TTIRItemId,
        args: Vec<SIRValueId>,
    },

    StructLit {
        item:   TTIRItemId,
        fields: Vec<SIRValueId>,
    },
    VariantLit {
        item:    TTIRItemId,
        variant: usize,
        fields:  Vec<SIRValueId>,
    },
    ArrayLit(Vec<SIRValueId>),
    TupleLit(Vec<SIRValueId>),
    Map {
        hashed:  bool,
        entries: Vec<(SIRValueId, SIRValueId)>,
    },
    Set {
        hashed: bool,
        elems:  Vec<SIRValueId>,
    },
    Closure {
        captures: Vec<TTIRCapture>,
        body:     SIRBodyId,
    },

    // ---- Memory ----------------------------------------------------------
    // A place is an address here. `Addr` is where one starts and the two
    // projections are how it is reached into, so `p.xs[i] = 1` is three
    // instructions and a store rather than a shape a store has to understand.
    Addr(SIRSlotId),
    // A global and `self` are places too, and neither is a slot of this frame.
    ItemAddr(TTIRItemId),
    SelfAddr,
    FieldAddr {
        base:  SIRValueId,
        index: usize,
    },
    TupleAddr {
        base:  SIRValueId,
        index: u64,
    },
    IndexAddr {
        base:  SIRValueId,
        index: SIRValueId,
    },
    Load {
        from: SIRValueId,
    },
    Store {
        to:    SIRValueId,
        value: SIRValueId,
    },
    // A slot read on a path that never wrote it: `let x: T;` and then a jump
    // over the line that fills it. Nothing here refuses that -- `sema` is
    // where a read of an unset name is turned down -- so what is left is to
    // say plainly that there is no value rather than to invent one.
    Undef,

    // ---- What a match asks -----------------------------------------------
    // Which variant an enum value is, as the number the checker gave it.
    Discriminant(SIRValueId),
    // One field of one variant's payload, read once the discriminant has
    // already said it is that variant. Reading it before the test would be
    // reading a field that is not there.
    Payload {
        of:      SIRValueId,
        variant: usize,
        index:   usize,
    },

    // ---- What a for walks --------------------------------------------------
    // The closed set of iterables -- an array, a run, a `Range`, a `Set`, a
    // `HashSet` (§5) -- walked by a cursor. Four instructions and not one
    // because a loop asks four separate questions, and each of them has to be
    // asked in a different block: whether there is another, what it is, and
    // how to get past it.
    //
    // The cursor `Start` gives back stands *before* the first, so that
    // advancing is the first thing every turn does. That is what lets the test
    // sit in one block that every edge into the loop reaches -- see
    // `lower.rs`, which would otherwise need to know which edge it came in on.
    //
    // This is a protocol, and the language deliberately has none (§5: "the
    // language has no iterator protocol, so what may be run through is a
    // closed set"). It is the compiler's and not the language's: nobody can
    // write a type that answers these, and the closed set is exactly the set
    // the checker already agreed to walk.
    // No operand: "before the first" is a position and not a thing found in
    // the iterable, and it is `IterStep` -- which does take it -- that goes
    // looking for where the first actually is.
    IterStart,
    IterValid {
        iter: SIRValueId,
        at:   SIRValueId,
    },
    IterElem {
        iter: SIRValueId,
        at:   SIRValueId,
    },
    IterStep {
        iter: SIRValueId,
        at:   SIRValueId,
    },

    // ---- Several at once ---------------------------------------------------
    // What `sir::opt` builds when it finds the same thing being done to
    // several places at once -- which, after a counted loop has been written
    // out as its turns, is what a great many loop bodies look like.
    //
    // A value with more than one of its type in it is a value whose `lanes` is
    // more than one, and these four are the only instructions that make or
    // take one apart. Everything else that may hold one -- `Unary`, `Binary`
    // -- does to all of them what it did to the one, which is what makes them
    // the same instruction and not a second set.

    // Several values side by side. Also how a scalar joins them: the same
    // value named as many times as there are lanes.
    Pack(Vec<SIRValueId>),
    // And one of them back out, for a use that was not part of the group.
    Lane {
        of: SIRValueId,
        at: usize,
    },
    // A run of adjacent elements of an aggregate, read at once: what several
    // `Index`es at consecutive numbers come to. `at` is the first of them and
    // `lanes` says how many, so the run is `at .. at + lanes`.
    Lanes {
        of:    SIRValueId,
        at:    u64,
        lanes: usize,
    },
    // The write, `to` being the address of the first of the elements written.
    // Not a `Store` with a wide value, because a store writes one place and
    // this writes a run of them -- which is exactly the difference every pass
    // that asks what it wrote has to see.
    VecStore {
        to:    SIRValueId,
        value: SIRValueId,
    },

    // ---- Releases ----------------------------------------------------------
    // Where the GIR put them, carried through unmoved: which releases run was
    // settled by `gir::drops` on the graph, and nothing here asks it again.
    //
    // Two and not one. A promoted name *is* the value and is released as one;
    // a name still in a slot is released where it stands, and loading it first
    // would release a copy and leave the original.
    Drop(SIRValueId),
    DropSlot(SIRSlotId),
}

// How a block ends. Two edges at most, and the GIR's other two terminators are
// gone: a `Match` became the tests that pick its arm and a `for` became the
// loop that walks it, both of them written out of these three.
#[derive(Debug, Clone, PartialEq)]
pub enum SIRTerm {
    Goto(SIRBlockId),
    Branch {
        cond: SIRValueId,
        then: SIRBlockId,
        els:  SIRBlockId,
    },
    Return(Option<SIRValueId>),
    Unreachable,
}

impl SIRTerm {
    pub fn targets(&self) -> Vec<SIRBlockId> {
        match self {
            SIRTerm::Goto(to) => vec![*to],
            SIRTerm::Branch { then, els, .. } => vec![*then, *els],
            SIRTerm::Return(_) | SIRTerm::Unreachable => Vec::new(),
        }
    }

    pub fn targets_mut(&mut self) -> Vec<&mut SIRBlockId> {
        match self {
            SIRTerm::Goto(to) => vec![to],
            SIRTerm::Branch { then, els, .. } => vec![then, els],
            SIRTerm::Return(_) | SIRTerm::Unreachable => Vec::new(),
        }
    }
}

impl SIRBody {
    // Which blocks reach each block. Every pass that joins paths wants this --
    // a phi has one entry per predecessor, and which predecessor is which is
    // the order this hands back.
    pub fn preds(&self) -> Vec<Vec<SIRBlockId>> {
        let mut out = vec![Vec::new(); self.blocks.len()];
        for (id, block) in self.blocks.iter().enumerate() {
            for to in block.term.targets() {
                if !out[to].contains(&id) {
                    out[to].push(id);
                }
            }
        }
        out
    }

    // The blocks the entry can get to. `gir::opt` already emptied what nothing
    // reaches, but this pass makes blocks of its own and a decision tree can
    // leave one standing that no test ever picks.
    pub fn live(&self) -> Vec<bool> {
        let mut seen = vec![false; self.blocks.len()];
        let mut stack = vec![self.entry];
        while let Some(at) = stack.pop() {
            if seen[at] {
                continue;
            }
            seen[at] = true;
            stack.extend(self.blocks[at].term.targets());
        }
        seen
    }

    // Every value an instruction reads, which is what a use-site walk needs and
    // what would otherwise be written out at each of them.
    pub fn uses(kind: &SIRInstKind) -> Vec<SIRValueId> {
        match kind {
            SIRInstKind::Literal(_)
            | SIRInstKind::Item(_)
            | SIRInstKind::SelfValue
            | SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::Undef
            | SIRInstKind::IterStart
            | SIRInstKind::DropSlot(_)
            | SIRInstKind::Closure { .. } => Vec::new(),

            SIRInstKind::Unary { operand, .. } => vec![*operand],
            SIRInstKind::Cast(v)
            | SIRInstKind::Discriminant(v)
            | SIRInstKind::Drop(v)
            | SIRInstKind::Load { from: v } => vec![*v],
            SIRInstKind::Field { base, .. }
            | SIRInstKind::TupleIndex { base, .. }
            | SIRInstKind::FieldAddr { base, .. }
            | SIRInstKind::TupleAddr { base, .. } => vec![*base],
            SIRInstKind::Payload { of, .. } => vec![*of],
            SIRInstKind::Lane { of, .. } | SIRInstKind::Lanes { of, .. } => vec![*of],

            SIRInstKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            SIRInstKind::Index { base, index } | SIRInstKind::IndexAddr { base, index } => {
                vec![*base, *index]
            }
            SIRInstKind::Store { to, value } | SIRInstKind::VecStore { to, value } => {
                vec![*to, *value]
            }
            SIRInstKind::IterValid { iter, at }
            | SIRInstKind::IterElem { iter, at }
            | SIRInstKind::IterStep { iter, at } => vec![*iter, *at],

            SIRInstKind::Range { start, end, .. } => {
                start.iter().chain(end.iter()).copied().collect()
            }
            SIRInstKind::Call { callee, args } => {
                let mut out = vec![*callee];
                out.extend(args.iter().copied());
                out
            }
            SIRInstKind::Method { recv, args, .. } => {
                let mut out = vec![*recv];
                out.extend(args.iter().copied());
                out
            }
            SIRInstKind::StructLit { fields, .. }
            | SIRInstKind::VariantLit { fields, .. }
            | SIRInstKind::ArrayLit(fields)
            | SIRInstKind::TupleLit(fields)
            | SIRInstKind::Set { elems: fields, .. }
            | SIRInstKind::Pack(fields) => fields.clone(),
            SIRInstKind::Map { entries, .. } => {
                entries.iter().flat_map(|(k, v)| [*k, *v]).collect()
            }
        }
    }

    // The same, in place, for a pass that rewrites what an instruction reads.
    // `uses` and this have to agree on which fields are operands; they are
    // written next to each other so that adding a kind to one and not the
    // other is visible.
    pub fn uses_mut(kind: &mut SIRInstKind) -> Vec<&mut SIRValueId> {
        match kind {
            SIRInstKind::Literal(_)
            | SIRInstKind::Item(_)
            | SIRInstKind::SelfValue
            | SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::Undef
            | SIRInstKind::IterStart
            | SIRInstKind::DropSlot(_)
            | SIRInstKind::Closure { .. } => Vec::new(),

            SIRInstKind::Unary { operand, .. } => vec![operand],
            SIRInstKind::Cast(v)
            | SIRInstKind::Discriminant(v)
            | SIRInstKind::Drop(v)
            | SIRInstKind::Load { from: v } => vec![v],
            SIRInstKind::Field { base, .. }
            | SIRInstKind::TupleIndex { base, .. }
            | SIRInstKind::FieldAddr { base, .. }
            | SIRInstKind::TupleAddr { base, .. } => vec![base],
            SIRInstKind::Payload { of, .. } => vec![of],
            SIRInstKind::Lane { of, .. } | SIRInstKind::Lanes { of, .. } => vec![of],

            SIRInstKind::Binary { lhs, rhs, .. } => vec![lhs, rhs],
            SIRInstKind::Index { base, index } | SIRInstKind::IndexAddr { base, index } => {
                vec![base, index]
            }
            SIRInstKind::Store { to, value } | SIRInstKind::VecStore { to, value } => {
                vec![to, value]
            }
            SIRInstKind::IterValid { iter, at }
            | SIRInstKind::IterElem { iter, at }
            | SIRInstKind::IterStep { iter, at } => vec![iter, at],

            SIRInstKind::Range { start, end, .. } => {
                start.iter_mut().chain(end.iter_mut()).collect()
            }
            SIRInstKind::Call { callee, args } => {
                let mut out = vec![callee];
                out.extend(args.iter_mut());
                out
            }
            SIRInstKind::Method { recv, args, .. } => {
                let mut out = vec![recv];
                out.extend(args.iter_mut());
                out
            }
            SIRInstKind::StructLit { fields, .. }
            | SIRInstKind::VariantLit { fields, .. }
            | SIRInstKind::ArrayLit(fields)
            | SIRInstKind::TupleLit(fields)
            | SIRInstKind::Set { elems: fields, .. }
            | SIRInstKind::Pack(fields) => fields.iter_mut().collect(),
            SIRInstKind::Map { entries, .. } => {
                entries.iter_mut().flat_map(|(k, v)| [k, v]).collect()
            }
        }
    }
}
