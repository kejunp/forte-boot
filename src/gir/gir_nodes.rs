// The nodes of the GIR: a function's body with its control flow drawn as
// edges rather than nesting.
//
//     AST -> lower -> TIR -> [ sema ] -> TTIR -> lower -> GIR
//
// It is built from the TTIR and not from the TIR, so everything here is already
// typed and already resolved -- see `tir/ttir_nodes.rs`. What this adds is the
// one thing that tree still had: `if`, `while`, `for`, `match`, the jumps and
// the two short-circuiting operators are not expressions here, they are edges.
//
// Types and patterns are the TTIR's and are not copied. A `TyId` and a
// `TTIRPatId` here index that program's arenas, which is what keeps one answer
// to what a type is rather than two that have to be kept in step.

#![allow(dead_code)]

use crate::tir::tir_nodes::{TIRAssignOp, TIRBinOp, TIRBinding, TIRIntro, TIRLit, TIRRangeOp,
                            TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRItemId, TTIRPatId, TyId, TTIRCapture};

pub type GIRExprId = usize;
pub type GIRBodyId = usize;
// Numbered within the body that holds them: a graph is a function's, and
// nothing outside it names a block.
pub type GIRBlockId = usize;
pub type GIRLocalId = usize;

// Every graph the program has, and the expressions they are made of. Items stay
// in the TTIR -- a GIR is a body and not a program's worth of declarations.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct GIRProgram {
    pub bodies: Vec<GIRBody>,
    pub exprs:  Vec<GIRExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GIRBody {
    pub entry:  GIRBlockId,
    pub blocks: Vec<GIRBlock>,
    pub locals: Vec<GIRLocal>,
    // Which slots the parameters were put in. Nothing fills them -- a caller
    // did -- so without this a pass over the graph reads them as slots holding
    // nothing, and a parameter's release is what it would leave out.
    pub params: Vec<GIRLocalId>,
    // What a closure's body took from the body around it, and the parameter
    // holding the run of addresses it finds them at. Empty and `None` for
    // every body that belongs to a declaration: a fn captures nothing.
    //
    // These are here rather than left on the `Closure` expression because the
    // two ends need different halves of the same fact. Where the closure is
    // *made* the captures say what to put in the run, and that is the
    // expression's; where its body *runs* they say which of its slots are not
    // slots at all but places in the frame outside, and that is this.
    pub captures: Vec<TTIRCapture>,
    pub env: Option<GIRLocalId>,
}

// A slot: a `let`, a `var`, a parameter, or a temporary the lowering made to
// carry the value of something that branched.
#[derive(Debug, Clone, PartialEq)]
pub struct GIRLocal {
    pub name:      TIRBinding,
    pub ty:        TyId,
    pub intro:     TIRIntro,
    // Made by the lowering rather than written, and named with a `$` -- which
    // no source can collide with, that being a macro parameter's sigil.
    pub synthetic: bool,
    // Whether its type has anything to release: an `impl Drop`, or something
    // holding one. A slot that has not is never dropped and needs no flag.
    pub drops:     bool,
}

// Straight-line statements and the one edge out. Every block ends in a
// terminator; there is no falling off the end of one.
#[derive(Debug, Clone, PartialEq)]
pub struct GIRBlock {
    pub stmts: Vec<GIRStmt>,
    pub term:  GIRTerm,
    pub line:  usize,
    pub col:   usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GIRStmt {
    pub kind:      GIRStmtKind,
    pub is_unsafe: bool,
    pub line:      usize,
    pub col:       usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GIRStmtKind {
    // A slot given a value, and every temporary the lowering fills.
    Set {
        local: GIRLocalId,
        value: GIRExprId,
    },
    // A store through a place the source wrote, which may be a field or an
    // index and so is an expression rather than a slot.
    Store {
        place: GIRExprId,
        op:    TIRAssignOp,
        value: GIRExprId,
    },
    // Evaluated for what it does, not for what it is.
    Eval(GIRExprId),
    // Releasing a slot, which is what a `Drop` is for:
    //
    //     A value that move has one owner at a time, so the end of that owner
    //     is the one place a release belongs: a local at the end of its block,
    //     a temporary at the end of its statement, a field when the value
    //     holding it goes, and nothing at all where the value was moved away
    //     first. Fields go in the order they were declared and locals in the
    //     reverse of it.                                 (docs/prose.txt, §2)
    //
    // A field is not here: what a struct's release comes to is its type's, and
    // the order its fields go in is a fact about the type and not about this
    // line. What is here is the other three -- where a local's release stands,
    // where a temporary's does, and which of them the source moved away.
    // Unconditional: it runs where it stands. A slot the source moved away
    // from on one path and not another does not get a conditional release --
    // it gets a flag beside it and a branch, drawn by `gir::drops`, because a
    // graph is where a question about a path is answered and a statement that
    // means "release this if" is that question left in the tree.
    Drop {
        local: GIRLocalId,
    },
}

// How a block ends, which is the whole of the control flow.
#[derive(Debug, Clone, PartialEq)]
pub enum GIRTerm {
    Goto(GIRBlockId),
    // The one two-way edge. `&&` and `||` are two of these and no operator at
    // all, which is what short-circuiting means once it is drawn.
    Branch {
        cond: GIRExprId,
        then: GIRBlockId,
        els:  GIRBlockId,
    },
    // Arms and not a decision tree: which patterns bind is settled, but how to
    // test them in what order is a later question than this one.
    Match {
        scrutinee: GIRExprId,
        arms:      Vec<GIRArm>,
        otherwise: Option<GIRBlockId>,
    },
    // `for x in it`. The one loop that stays an edge of its own: what it would
    // desugar into is an iterator protocol, and the language has none.
    ForEach {
        local: GIRLocalId,
        iter:  GIRExprId,
        body:  GIRBlockId,
        exit:  GIRBlockId,
    },
    Return(Option<GIRExprId>),
    Unreachable,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GIRArm {
    pub pats:  Vec<TTIRPatId>,
    pub block: GIRBlockId,
}

// ---- Expressions ----------------------------------------------------------
// Nothing here branches, and nothing here has a value that depends on which way
// something went.

#[derive(Debug, Clone, PartialEq)]
pub struct GIRExpr {
    pub kind: GIRExprKind,
    pub ty:   TyId,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GIRExprKind {
    Literal(TIRLit),
    Local(GIRLocalId),
    Item(TTIRItemId),
    SelfExpr,

    Field {
        base:  GIRExprId,
        index: usize,
    },
    TupleIndex {
        base:  GIRExprId,
        index: u64,
    },
    Call {
        callee: GIRExprId,
        args:   Vec<GIRExprId>,
    },
    Method {
        recv: GIRExprId,
        item: TTIRItemId,
        args: Vec<GIRExprId>,
    },
    Index {
        base:  GIRExprId,
        index: GIRExprId,
    },
    StructLit {
        item:   TTIRItemId,
        fields: Vec<GIRExprId>,
    },
    VariantLit {
        item:    TTIRItemId,
        variant: usize,
        fields:  Vec<GIRExprId>,
    },

    ArrayLit(Vec<GIRExprId>),
    TupleLit(Vec<GIRExprId>),
    Map {
        hashed:  bool,
        entries: Vec<(GIRExprId, GIRExprId)>,
    },
    Set {
        hashed: bool,
        elems:  Vec<GIRExprId>,
    },

    Unary {
        op:      TIRUnaryOp,
        operand: GIRExprId,
    },
    // `&&` and `||` are not here: they are branches. `^^` is, since it settles
    // nothing until both sides are known and so evaluates both anyway.
    Binary {
        op:  TIRBinOp,
        lhs: GIRExprId,
        rhs: GIRExprId,
    },
    Range {
        op:    TIRRangeOp,
        start: Option<GIRExprId>,
        end:   Option<GIRExprId>,
    },
    Cast(GIRExprId),
    // A closure's body is a graph of its own.
    // As the TTIR has it: what it captured, and the graph its body became.
    Closure {
        captures: Vec<TTIRCapture>,
        body:     GIRBodyId,
    },
}
