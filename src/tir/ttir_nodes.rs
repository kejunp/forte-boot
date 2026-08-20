// The TTIR -- the typed tree IR: the TIR beside it with every question `sema`
// answers already answered. Same tree, same control flow, same order of
// evaluation; what is added is that every name says what it refers to and every
// expression says what type it is.
//
//     AST -> lower -> TIR -> [ sema ] -> TTIR -> lower -> CFG
//                              ^ not written
//
// Nothing builds one of these yet. `sema` is the pass that would, and it is not
// written -- so what is here is the shape the checker has to produce and the
// shape `cfg::lower` reads, agreed on in advance so that neither has to guess
// at the other. A test builds one by hand; nothing else does.
//
// The vocabulary is the TIR's. An operator means the same thing in both trees
// and a second spelling of `+` would only be a second thing to keep in step, so
// the leaves are shared and only what `sema` adds is new here.

#![allow(dead_code)]

use super::tir_nodes::{
    TIRAssignOp, TIRAttrs, TIRBinOp, TIRBinding, TIRFnAttrs, TIRIntro, TIRLit, TIRPrim,
    TIRRangeOp, TIRRefOp, TIRUnaryOp, TIRVis,
};

pub type TTIRItemId = usize;
pub type TTIRExprId = usize;
pub type TTIRPatId = usize;
pub type TTIRBodyId = usize;
// A slot of the body that holds it, not of the program.
pub type TTIRLocalId = usize;
// A type, worked out rather than written: `Vec<_>` has an answer by now.
pub type TyId = usize;
// How long a reference is good for, once the checker has settled it. A `'a` in
// the source and one it worked out for itself are the same thing here.
pub type RegionId = usize;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct TTIRProgram {
    pub roots:  Vec<TTIRItemId>,
    pub items:  Vec<TTIRItem>,
    pub exprs:  Vec<TTIRExpr>,
    pub pats:   Vec<TTIRPat>,
    pub bodies: Vec<TTIRBody>,
    // Every type the program mentions, deduplicated by the checker: two `i32`s
    // are one entry, which is what lets a comparison be a handle comparison.
    pub types:  Vec<Ty>,
}

// ---- Types ----------------------------------------------------------------
// What a type *is*, not how it was written. `<grouped_type>` is gone, `_` is
// gone, and a name has become the declaration it names.

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Prim(TIRPrim),
    // A struct, an enum or a trait, with the arguments it was given.
    Named {
        item: TTIRItemId,
        args: Vec<TyId>,
    },
    Ref {
        op:    TIRRefOp,
        // Always known here. A reference with no `'a` written got one anyway,
        // which is what the inference in section 3 is for.
        life:  RegionId,
        inner: TyId,
    },
    // `ptr T`. No region: a pointer is what the checker stopped answering for,
    // and there is nothing here for it to have worked out.
    Ptr(TyId),
    // `T[8]`. The length is a number by now: an <array_suffix> takes a
    // <const_expr>, and evaluating one is the checker's.
    Array {
        elem: TyId,
        len:  u64,
    },
    Run(TyId),
    Tuple(Vec<TyId>),
    Fn {
        params: Vec<TyId>,
        ret:    TyId,
    },
    // What an expression the checker could not type is given, so one mistake
    // costs one message and not every message after it.
    Error,
}

// ---- Items ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRItem {
    pub kind: TTIRItemKind,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRItemKind {
    Fn(TTIRFn),
    Struct {
        vis:    TIRVis,
        attrs:  TIRAttrs,
        name:   String,
        fields: Vec<TTIRFieldDecl>,
    },
    Enum {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        variants: Vec<TTIRVariant>,
    },
    Trait {
        vis:     TIRVis,
        attrs:   TIRAttrs,
        name:    String,
        members: Vec<TTIRItemId>,
    },
    Impl {
        vis:     TIRVis,
        attrs:   TIRAttrs,
        // The type the impl is written about, and the trait where there is one.
        ty:      TyId,
        of:      Option<TTIRItemId>,
        members: Vec<TTIRItemId>,
    },
    Namespace {
        vis:   TIRVis,
        attrs: TIRAttrs,
        name:  String,
        items: Vec<TTIRItemId>,
    },
    Const {
        vis:   TIRVis,
        attrs: TIRAttrs,
        name:  String,
        ty:    TyId,
        value: TTIRExprId,
    },
    Global {
        vis:   TIRVis,
        attrs: TIRAttrs,
        intro: TIRIntro,
        name:  TIRBinding,
        ty:    TyId,
        init:  Option<TTIRExprId>,
    },
}

// An import is gone by now: it was a way of reaching a declaration, and every
// name that used one has been resolved to what it reached.
#[derive(Debug, Clone, PartialEq)]
pub struct TTIRFn {
    pub vis:       TIRVis,
    pub attrs:     TIRFnAttrs,
    pub is_const:  bool,
    pub is_unsafe: bool,
    pub name:      String,
    // The mangled symbol, or what `%symbol` said instead. Worked out once here
    // rather than by everything downstream that wants to name the function.
    pub symbol:    String,
    pub ty:        TyId,
    pub params:    Vec<TTIRLocalId>,
    pub ret:       TyId,
    pub body:      Option<TTIRBodyId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRFieldDecl {
    pub vis:   TIRVis,
    pub attrs: TIRAttrs,
    pub name:  String,
    pub ty:    TyId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRVariant {
    pub attrs:   TIRAttrs,
    pub name:    String,
    pub payload: TTIRPayload,
    // Worked out by the checker whether it was written or not.
    pub value:   i64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRPayload {
    None,
    Tuple(Vec<TyId>),
    Named(Vec<TTIRFieldDecl>),
}

// ---- Bodies ---------------------------------------------------------------
// Still a tree. Turning this into a graph is `cfg::lower`'s, and it is the one
// thing left to do to it.

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRBody {
    pub locals: Vec<TTIRLocal>,
    pub value:  TTIRExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRLocal {
    pub name:  TIRBinding,
    pub ty:    TyId,
    pub intro: TIRIntro,
}

// ---- Statements -----------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRStmt {
    // The slot is already declared in the body; this is where it is filled.
    Let {
        is_unsafe: bool,
        local:     TTIRLocalId,
        init:      Option<TTIRExprId>,
    },
    Expr {
        is_unsafe: bool,
        expr:      TTIRExprId,
    },
    Item(TTIRItemId),
}

// ---- Expressions ----------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRExpr {
    pub kind: TTIRExprKind,
    // Every expression has one. That is the whole of what makes this the typed
    // tree, and what lets `cfg::lower` build a graph that knows its own types.
    pub ty:   TyId,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRExprKind {
    Literal(TIRLit),
    // A name, resolved. `Name` is gone: there is nothing left to look up.
    Local(TTIRLocalId),
    Item(TTIRItemId),
    SelfExpr,

    // Reached by index rather than by name: which field `x` is, is settled.
    Field {
        base:  TTIRExprId,
        index: usize,
    },
    TupleIndex {
        base:  TTIRExprId,
        index: u64,
    },
    Call {
        callee: TTIRExprId,
        args:   Vec<TTIRExprId>,
    },
    // A method, resolved to the one it calls. `.` and `::` are both gone: which
    // separator was written mattered to the resolver and to nobody after it.
    Method {
        recv: TTIRExprId,
        item: TTIRItemId,
        args: Vec<TTIRExprId>,
    },
    Index {
        base:  TTIRExprId,
        index: TTIRExprId,
    },
    StructLit {
        item:   TTIRItemId,
        // In declaration order, whatever order they were written in.
        fields: Vec<TTIRExprId>,
    },
    VariantLit {
        item:    TTIRItemId,
        variant: usize,
        fields:  Vec<TTIRExprId>,
    },

    ArrayLit(Vec<TTIRExprId>),
    TupleLit(Vec<TTIRExprId>),
    Map {
        hashed:  bool,
        entries: Vec<(TTIRExprId, TTIRExprId)>,
    },
    Set {
        hashed: bool,
        elems:  Vec<TTIRExprId>,
    },

    Unary {
        op:      TIRUnaryOp,
        operand: TTIRExprId,
    },
    // `&&` and `||` are still here: this is a tree, and taking them apart into
    // branches is what the CFG is for.
    Binary {
        op:  TIRBinOp,
        lhs: TTIRExprId,
        rhs: TTIRExprId,
    },
    Assign {
        op:    TIRAssignOp,
        place: TTIRExprId,
        value: TTIRExprId,
    },
    Range {
        op:    TIRRangeOp,
        start: Option<TTIRExprId>,
        end:   Option<TTIRExprId>,
    },
    // The type is on the expression, so what it is cast *to* needs no field.
    Cast(TTIRExprId),
    Closure {
        is_move: bool,
        body:    TTIRBodyId,
    },

    Block {
        stmts: Vec<TTIRStmt>,
        tail:  Option<TTIRExprId>,
    },
    If {
        cond: TTIRExprId,
        then: TTIRExprId,
        els:  Option<TTIRExprId>,
    },
    While {
        cond: TTIRExprId,
        body: TTIRExprId,
    },
    For {
        local: TTIRLocalId,
        iter:  TTIRExprId,
        body:  TTIRExprId,
    },
    Match {
        scrutinee: TTIRExprId,
        arms:      Vec<TTIRArm>,
    },

    Return(Option<TTIRExprId>),
    Break(Option<TTIRExprId>),
    Continue,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRArm {
    pub pats: Vec<TTIRPatId>,
    pub body: TTIRExprId,
}

// ---- Patterns -------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct TTIRPat {
    pub kind: TTIRPatKind,
    pub ty:   TyId,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRPatKind {
    Wildcard,
    // A bare name that bound rather than tested, and the slot it binds.
    Bind(TTIRLocalId),
    // One that tested: the constant it stands for.
    Const(TTIRItemId),
    Lit {
        negated: bool,
        value:   TIRLit,
    },
    Range {
        op: TIRRangeOp,
        lo: TTIRPatId,
        hi: TTIRPatId,
    },
    Variant {
        item:    TTIRItemId,
        variant: usize,
        elems:   Vec<TTIRPatId>,
    },
    Tuple(Vec<TTIRPatId>),
    // Fields in declaration order, `None` where the pattern named none.
    Struct {
        item:   TTIRItemId,
        fields: Vec<Option<TTIRPatId>>,
    },
}
