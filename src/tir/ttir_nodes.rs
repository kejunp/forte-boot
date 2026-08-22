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
// A hole in a type while the checker is filling it. See `Ty::Var`.
pub type VarId = usize;

// One program is one *suite* and not one file, which is forced rather than
// chosen: `Ty::Named` names an item of this same program, and an import reaches
// a declaration in another file (section 1) -- so two files that share a type
// have to share the arena, and therefore the items it points into. That is also
// why `types` is deduplicated across the whole of it.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TTIRProgram {
    // The files it was compiled from, each with what it declared, in the order
    // they were read. Not one flat `roots`: a file is a module (section 1) and
    // its name stands in front of everything it declares, so which file a root
    // came from is part of what the program is.
    pub modules: Vec<TTIRModule>,
    pub items:   Vec<TTIRItem>,
    pub exprs:   Vec<TTIRExpr>,
    pub pats:    Vec<TTIRPat>,
    pub bodies:  Vec<TTIRBody>,
    // Every type the program mentions, deduplicated by the checker: two `i32`s
    // are one entry, which is what lets a comparison be a handle comparison.
    pub types:   Vec<Ty>,
}

// One file, and what it declared.
#[derive(Debug, Clone, PartialEq)]
pub struct TTIRModule {
    // Its path from the suite root: `a/b/deep.fc` is `["a", "b", "deep"]`.
    // What `ImportResolver::module_of` works out, and what stands in front of
    // every symbol the file compiles to.
    pub path:  Vec<String>,
    pub roots: Vec<TTIRItemId>,
}

// ---- Generics ---------------------------------------------------------------
// A parameter as declared, and what it is held to. The two kinds share one list
// because the grammar's does: `<'a, T: Show + 'a>` interleaves them, and whether
// that is allowed is a rule about a declaration rather than a shape one has.
//
// A parameter's place in this list is its index, which is what `Ty::Param` names
// it by and what an argument at a call is put in. There is no `index` field: the
// position is the index, and writing it down twice is what would let the two
// come apart.
//
// A `where` clause is gone by here. `fn f<T: Ord>` and `fn f<T> where T: Ord`
// say the same thing, and this is what a declaration *is* rather than how it was
// written, so a predicate about a parameter is folded into that parameter's
// bounds. What is not folded is a predicate about anything else -- `where
// Vec<T>: Show` has no parameter to belong to, and nothing here holds one yet.

#[derive(Debug, Clone, PartialEq)]
pub enum TTIRGeneric {
    Type {
        name:   String,
        // What it is held to. One list and not two, because one colon is what
        // writes both: `<T: Show + 'a>` is a trait and a region at once.
        bounds: Vec<TTIRBound>,
    },
    Life {
        name:   String,
        // The region it declares, which a `&'a T` in the signature points at.
        region: RegionId,
        // What it has to outlive: the `'b` of a `'a: 'b`. Regions only -- a
        // lifetime implements nothing, and by here that has been settled.
        bounds: Vec<RegionId>,
    },
}

// One thing something is held to. The TIR has a `TIRBound` of the same two
// shapes; what is different here is that both sides have been resolved -- a
// trait is the type it names, and a lifetime is the region it stands for.
#[derive(Debug, Clone, PartialEq)]
pub enum TTIRBound {
    // `T: Show<i32>`, which is a `Ty::Named` like any other by now.
    Trait(TyId),
    // `T: 'a`.
    Life(RegionId),
}

// One predicate of a `where` clause.
//
// A predicate about a parameter is not here: it is folded into that parameter's
// bounds, since `fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing and
// this tree is what a declaration *is*. What is left is every predicate with no
// parameter to fold into -- `where Vec<T>: Show` is about a type that was built
// rather than declared, and `where 'a: 'b` about two regions.
#[derive(Debug, Clone, PartialEq)]
pub struct TTIRWherePred {
    pub subject: TTIRSubject,
    pub bounds:  Vec<TTIRBound>,
}

// What a predicate is about. Not a `TTIRBound`: the two read alike and mean
// opposite things, and the one place the TIR spells them with one type is the
// one place a reader has to stop and work out which side they are on.
#[derive(Debug, Clone, PartialEq)]
pub enum TTIRSubject {
    Type(TyId),
    Region(RegionId),
}

// ---- Types ----------------------------------------------------------------
// What a type *is*, not how it was written. `<grouped_type>` is gone, `_` is
// gone, and a name has become the declaration it names.

// `Eq` and `Hash` because the arena interns these: an equal type has to be an
// equal handle, and that wants them as a key. Nothing here holds a float, so
// `Eq` is honest.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Prim(TIRPrim),
    // A struct, an enum or a trait, with the arguments it was given.
    Named {
        item:    TTIRItemId,
        args:    Vec<TyId>,
        // The regions it was handed, one per lifetime its declaration takes.
        // "Every reference in a signature with no lifetime of its own gets one"
        // (§3) reaches here too: a `Held` written bare gets as many fresh
        // regions as a `Held<'a>` names, so the two carry the same promise and
        // only one of them says which region it is.
        //
        // Kept beside `args` and not among them because they are not types: a
        // `Ty` is what unification works on, and a region is what it skips.
        regions: Vec<RegionId>,
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
    // A fn as a value, which is what a closure is and what a fn handed to one
    // is. `is_unsafe` rides along because calling through the value needs the
    // same guard calling the declaration does (section 2); `const` does not,
    // being a fact about whether the declaration folds rather than about the
    // value.
    Fn {
        params:    Vec<TyId>,
        ret:       TyId,
        is_unsafe: bool,
    },
    // `let gc x = ...`: the binding owns its value through the collector. It
    // is a type and not a flag on the binding, which is the question section 8
    // leaves open answered one way -- so a `gc` value handed to a function is
    // still one, and the signature can say so.
    GC(TyId),
    // A generic parameter: the `T` of `fn f<T>(x: T)`. `index` is its place in
    // the declaration's own list, which is what an argument at a call is put
    // in; `name` is for saying which one in a message.
    //
    // It is here because nothing monomorphises on the way to the TTIR: a
    // generic fn arrives with one body and its parameters still standing, and
    // `x` above has to have a type like anything else.
    Param {
        name:  String,
        index: usize,
    },
    // A type the checker has not worked out yet: the `_` of `Vec<_>` while it is
    // still being settled, and the type of every expression before it is.
    //
    // None survives into a finished program -- that is what makes this the
    // *typed* tree, and `sema::types::Types::finish` is where any that did
    // becomes an `Error` with a message against it. It is here rather than in a
    // table of the checker's own because inference builds partial types, and a
    // partial type is a `Ty` with a hole in it.
    Var(VarId),
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
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TTIRGeneric>,
        // No `wheres`: `<struct_decl>` takes a `<generic_params_opt>` and no
        // `<where_clause_opt>`, so a struct's parameters are held to what is
        // written between the angles and to nothing else. The same for an
        // enum. A fn and an impl are the two that take one.
        fields:   Vec<TTIRFieldDecl>,
    },
    Enum {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TTIRGeneric>,
        variants: Vec<TTIRVariant>,
    },
    Trait {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TTIRGeneric>,
        wheres:   Vec<TTIRWherePred>,
        members:  Vec<TTIRItemId>,
    },
    Impl {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        generics: Vec<TTIRGeneric>,
        wheres:   Vec<TTIRWherePred>,
        // The type the impl is written about, and the trait where there is one.
        ty:       TyId,
        of:       Option<TTIRItemId>,
        members:  Vec<TTIRItemId>,
    },
    // `type Pair<T> = (T, T)`. It survives as a *name* and not as a type: no
    // `Ty` mentions it, the alias having been followed and what it named left
    // in its place. What is left here is what a reader wrote -- the name is in
    // scope, `Pair<i32>` is what they typed, and a message about it has to be
    // able to say so.
    //
    // So there is nothing to compile and no symbol: an alias makes no new type
    // and no code, and `prefix_of` in `sema::names` gives it no letter.
    TypeAlias {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TTIRGeneric>,
        wheres:   Vec<TTIRWherePred>,
        // What it names, followed: `type Raw = ptr u8` holds the `ptr u8`.
        ty:       TyId,
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
    pub generics:  Vec<TTIRGeneric>,
    pub wheres:    Vec<TTIRWherePred>,
    // Which of this signature's regions outlive which, as `(longer, shorter)`.
    //
    // "Every reference in a signature with no lifetime of its own gets one, and
    // a reference in the return type gets the shortest-lived of the ones the
    // parameters brought in" (§3) -- which is this: every parameter's region
    // outlives the return's, and "the shortest of them outlives nothing the
    // others do not" is why that answer is always sound.
    //
    // A written `'a` sharpens it by naming one region in two places instead,
    // and then only what was written stands here.
    pub outlives:  Vec<(RegionId, RegionId)>,
    pub ty:        TyId,
    pub params:    Vec<TTIRParam>,
    pub ret:       TyId,
    pub body:      Option<TTIRBodyId>,
}

// One parameter as declared. The *type* is not here: it is in the fn's own
// `Ty::Fn`, and a second spelling of it would only be a second thing to keep
// in step. What is here is what that cannot say -- the name it was given, and
// which slot of the body it fills.
#[derive(Debug, Clone, PartialEq)]
pub struct TTIRParam {
    // `_` and a receiver are both bindings and neither is a name a caller may
    // use, which is why this is a `TIRBinding` and not a `String`.
    pub name: TIRBinding,
    // `None` in a signature, which has no body to fill: its parameters are
    // named and typed and there is nothing to put them in.
    pub slot: Option<TTIRLocalId>,
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
    // Where it was bound. A slot is not an expression and had none until the
    // checker wanted one: "the value was moved here, and it was bound there"
    // is two places, and only one of them is a line anybody wrote an
    // expression on.
    pub line:  usize,
    pub col:   usize,
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
    // What it captured, and its body. No `is_move`: the word is the TIR's,
    // which keeps what was written, and what it came to is a mode on each name
    // -- "the keyword names the capture mode and not the transfer" (§5). A
    // `move` closure is one whose captures are every one `Value`.
    Closure {
        captures: Vec<TTIRCapture>,
        body:     TTIRBodyId,
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

// One name a closure's body used but did not declare.
//
// This is the only way a body reaches out of itself: a `TTIRLocalId` is a slot
// of the body that holds it, so a closure's body cannot name a local of the
// frame it was written in. `outer` is that name where it lives and `slot` is
// the closure's own for it, and the two are the whole of the connection.
//
// It is also the one place a reference is taken without being written (§5), and
// so the one place the aliasing rule reaches something nobody spelled out --
// which is why the position is here. A capture has no expression of its own to
// take one from.
#[derive(Debug, Clone, PartialEq)]
pub struct TTIRCapture {
    pub outer: TTIRLocalId,
    pub slot:  TTIRLocalId,
    pub mode:  TTIRCaptureMode,
    pub line:  usize,
    pub col:   usize,
}

// How the body took it: "worked out per name, each taking the least the body
// asks of it. Reading one takes a `&` of it and assigning to one takes a `*`"
// (§5), and `move` overrules both at once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TTIRCaptureMode {
    // `&n` where the body reads it, `*n` where it assigns to one.
    Ref(TIRRefOp),
    // By value, which "is a copy where the name's type copies and a move where
    // it does not" -- the same rule every other handing-over follows.
    Value,
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
