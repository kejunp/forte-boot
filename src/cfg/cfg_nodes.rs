// The nodes of the control flow graph: a function's body with its control flow
// drawn as edges rather than nesting.
//
//     AST -> lower -> TIR -> [ sema ] -> TTIR -> lower -> CFG
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

pub type CFGExprId = usize;
pub type CFGBodyId = usize;
// Numbered within the body that holds them: a graph is a function's, and
// nothing outside it names a block.
pub type CFGBlockId = usize;
pub type CFGLocalId = usize;

// Every graph the program has, and the expressions they are made of. Items stay
// in the TTIR -- a CFG is a body and not a program's worth of declarations.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct CFGProgram {
    pub bodies: Vec<CFGBody>,
    pub exprs:  Vec<CFGExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CFGBody {
    pub entry:  CFGBlockId,
    pub blocks: Vec<CFGBlock>,
    pub locals: Vec<CFGLocal>,
    // Which slots the parameters were put in. Nothing fills them -- a caller
    // did -- so without this a pass over the graph reads them as slots holding
    // nothing, and a parameter's release is what it would leave out.
    pub params: Vec<CFGLocalId>,
}

// A slot: a `let`, a `var`, a parameter, or a temporary the lowering made to
// carry the value of something that branched.
#[derive(Debug, Clone, PartialEq)]
pub struct CFGLocal {
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
pub struct CFGBlock {
    pub stmts: Vec<CFGStmt>,
    pub term:  CFGTerm,
    pub line:  usize,
    pub col:   usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CFGStmt {
    pub kind:      CFGStmtKind,
    pub is_unsafe: bool,
    pub line:      usize,
    pub col:       usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CFGStmtKind {
    // A slot given a value, and every temporary the lowering fills.
    Set {
        local: CFGLocalId,
        value: CFGExprId,
    },
    // A store through a place the source wrote, which may be a field or an
    // index and so is an expression rather than a slot.
    Store {
        place: CFGExprId,
        op:    TIRAssignOp,
        value: CFGExprId,
    },
    // Evaluated for what it does, not for what it is.
    Eval(CFGExprId),
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
    Drop {
        local: CFGLocalId,
        // Whether the value may already have gone. Certain on one path and not
        // another is neither "release it" nor "leave it", and the prose does
        // not settle which -- a flag beside the slot, set where it is filled
        // and cleared where it is moved, is what a backend puts here.
        guarded: bool,
    },
}

// How a block ends, which is the whole of the control flow.
#[derive(Debug, Clone, PartialEq)]
pub enum CFGTerm {
    Goto(CFGBlockId),
    // The one two-way edge. `&&` and `||` are two of these and no operator at
    // all, which is what short-circuiting means once it is drawn.
    Branch {
        cond: CFGExprId,
        then: CFGBlockId,
        els:  CFGBlockId,
    },
    // Arms and not a decision tree: which patterns bind is settled, but how to
    // test them in what order is a later question than this one.
    Match {
        scrutinee: CFGExprId,
        arms:      Vec<CFGArm>,
        otherwise: Option<CFGBlockId>,
    },
    // `for x in it`. The one loop that stays an edge of its own: what it would
    // desugar into is an iterator protocol, and the language has none.
    ForEach {
        local: CFGLocalId,
        iter:  CFGExprId,
        body:  CFGBlockId,
        exit:  CFGBlockId,
    },
    Return(Option<CFGExprId>),
    Unreachable,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CFGArm {
    pub pats:  Vec<TTIRPatId>,
    pub block: CFGBlockId,
}

// ---- Expressions ----------------------------------------------------------
// Nothing here branches, and nothing here has a value that depends on which way
// something went.

#[derive(Debug, Clone, PartialEq)]
pub struct CFGExpr {
    pub kind: CFGExprKind,
    pub ty:   TyId,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CFGExprKind {
    Literal(TIRLit),
    Local(CFGLocalId),
    Item(TTIRItemId),
    SelfExpr,

    Field {
        base:  CFGExprId,
        index: usize,
    },
    TupleIndex {
        base:  CFGExprId,
        index: u64,
    },
    Call {
        callee: CFGExprId,
        args:   Vec<CFGExprId>,
    },
    Method {
        recv: CFGExprId,
        item: TTIRItemId,
        args: Vec<CFGExprId>,
    },
    Index {
        base:  CFGExprId,
        index: CFGExprId,
    },
    StructLit {
        item:   TTIRItemId,
        fields: Vec<CFGExprId>,
    },
    VariantLit {
        item:    TTIRItemId,
        variant: usize,
        fields:  Vec<CFGExprId>,
    },

    ArrayLit(Vec<CFGExprId>),
    TupleLit(Vec<CFGExprId>),
    Map {
        hashed:  bool,
        entries: Vec<(CFGExprId, CFGExprId)>,
    },
    Set {
        hashed: bool,
        elems:  Vec<CFGExprId>,
    },

    Unary {
        op:      TIRUnaryOp,
        operand: CFGExprId,
    },
    // `&&` and `||` are not here: they are branches. `^^` is, since it settles
    // nothing until both sides are known and so evaluates both anyway.
    Binary {
        op:  TIRBinOp,
        lhs: CFGExprId,
        rhs: CFGExprId,
    },
    Range {
        op:    TIRRangeOp,
        start: Option<CFGExprId>,
        end:   Option<CFGExprId>,
    },
    Cast(CFGExprId),
    // A closure's body is a graph of its own.
    // As the TTIR has it: what it captured, and the graph its body became.
    Closure {
        captures: Vec<TTIRCapture>,
        body:     CFGBodyId,
    },
}
