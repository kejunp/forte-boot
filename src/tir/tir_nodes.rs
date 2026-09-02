// The nodes of the tree IR. See `tir.rs` for where this sits in the pipeline;
// what follows is what the shape is, and why it is not the AST's.
//
// `lower` builds these; `sema` is what still has to be written. Semantic
// analysis reads the TIR rather than producing it, so the order is lower first
// and check second.
//
// Five kinds instead of one. The AST is a single `ASTNodeKind` because that is
// what an LR parse wants -- every stack entry has to hold the same thing -- and
// the price is that a rule asking a child for a name it does not have finds out
// by panicking. Lowering is ordinary recursive code and owes that nothing, so an
// item, a statement, an expression, a type and a pattern are five types here,
// and handing one where another belongs stops compiling rather than stops the
// compiler.
//
// What is not here is as much of the point. Nothing is resolved and nothing is
// typed: `sema` runs after this, so a name is still the segments it was written
// as, and a bare name in a pattern is still a name -- whether it tests against a
// constant or binds is the resolver's, and guessing here would be guessing. What
// `sema` works out goes in tables of its own, kept beside these and keyed by the
// handles below; it does not rewrite the tree, or there would have to be another
// one after it.
//
// `lower` builds these and nothing reads them yet, `sema` being the pass that
// would. Until it exists most of what is here is constructed and never
// inspected, and the warning about it would be on every build rather than about
// anything. The allow is the nodes' own and not the module's, so that dead code
// in `lower` -- which does have a caller -- is still reported.
#![allow(dead_code)]

// A handle into one of the arenas in `TIRProgram`. Four types and not one, so a
// table `sema` keys by expression cannot be reached with a pattern's handle.
pub type TIRItemId = usize;
pub type TIRExprId = usize;
pub type TIRTypeId = usize;
pub type TIRPatId = usize;

// Everything a lowered file holds. The arenas are what the handles index, and
// the roots are the items the file was written as, in order.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TIRProgram {
    pub roots: Vec<TIRItemId>,
    pub items: Vec<TIRItem>,
    pub exprs: Vec<TIRExpr>,
    pub types: Vec<TIRType>,
    pub pats:  Vec<TIRPat>,
}

// ---- Positions ------------------------------------------------------------
// Every node keeps where it was written, since a diagnostic from `sema` points
// at source the same way one from the parser does. Line and column and no
// length: the AST has none to give, and a `Span` wants one -- see the note in
// `error/span.rs`.

#[derive(Debug, Clone, PartialEq)]
pub struct TIRItem {
    pub kind: TIRItemKind,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRExpr {
    pub kind: TIRExprKind,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRType {
    pub kind: TIRTypeKind,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRPat {
    pub kind: TIRPatKind,
    pub line: usize,
    pub col:  usize,
}

// ---- Items ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum TIRItemKind {
    // Every name one `import` reached, the tree it was written as already
    // flattened. Where a path is looked up is the resolver's, and section 8
    // leaves it open; so is what a glob does to a name already in scope, and
    // whether a root may stand anywhere but the front of a path.
    Import {
        vis:    TIRVis,
        attrs:  TIRAttrs,
        leaves: Vec<TIRImportLeaf>,
    },

    Fn(TIRFn),

    Struct {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TIRGeneric>,
        fields:   Vec<TIRFieldDecl>,
    },

    Enum {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TIRGeneric>,
        variants: Vec<TIRVariant>,
    },

    Trait {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TIRGeneric>,
        // Handles and not the functions themselves: a trait's method is a
        // function like any other, and `sema` keys what it works out by the
        // handle. Owning them here would leave a method the one function in
        // the language with no id to be named by.
        members:  Vec<TIRItemId>,
    },

    // `for_ty` is `Some` where a `for` was written, and then `ty` is the trait.
    // Whether `ty` names `Copy` or `Drop` is the checker's to notice: those two
    // are names it knows, not syntax the lowering can act on.
    Impl {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        generics: Vec<TIRGeneric>,
        ty:       TIRTypeId,
        for_ty:   Option<TIRTypeId>,
        wheres:   Vec<TIRWherePred>,
        members:  Vec<TIRItemId>,
    },

    Namespace {
        vis:   TIRVis,
        attrs: TIRAttrs,
        name:  String,
        items: Vec<TIRItemId>,
    },

    Const {
        vis:   TIRVis,
        attrs: TIRAttrs,
        name:  String,
        ty:    TIRTypeId,
        value: TIRExprId,
    },

    // `type MyType = i32`. An alias is a name for a type and not a type, so
    // once the resolver has followed it there is nothing of it left in any
    // type -- no `Ty` names one. The declaration itself survives into the TTIR
    // even so, because the *name* does: it is in scope, it is what a reader
    // wrote, and a message about it has to be able to say so.
    TypeAlias {
        vis:      TIRVis,
        attrs:    TIRAttrs,
        name:     String,
        generics: Vec<TIRGeneric>,
        ty:       TIRTypeId,
    },

    // A `<var_decl>` at file scope. The same declaration inside a block is a
    // `TIRStmt::Let`: the AST holds one node for both because the grammar does,
    // and splitting them here is what lets each say only what it can hold.
    Global {
        vis:   TIRVis,
        attrs: TIRAttrs,
        intro: TIRIntro,
        // The `gc` the binding was written with, already held against the rule
        // that only a heap value or a pointer may be under one.
        is_gc: bool,
        name:  TIRBinding,
        ty:    Option<TIRTypeId>,
        init:  Option<TIRExprId>,
    },
}

// A function, wherever it was declared: a file, a trait, an impl. `body` is
// `None` for a signature, which is what a `;` in place of a block spells.
#[derive(Debug, Clone, PartialEq)]
pub struct TIRFn {
    pub vis:       TIRVis,
    pub attrs:     TIRFnAttrs,
    pub is_const:  bool,
    pub is_unsafe: bool,
    pub name:      String,
    pub generics:  Vec<TIRGeneric>,
    pub params:    Vec<TIRParam>,
    pub ret:       Option<TIRTypeId>,
    pub wheres:    Vec<TIRWherePred>,
    pub body:      Option<TIRExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRParam {
    pub name: TIRBinding,
    pub ty:   Option<TIRTypeId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRFieldDecl {
    pub vis:   TIRVis,
    pub attrs: TIRAttrs,
    pub name:  String,
    pub ty:    TIRTypeId,
}

// A variant and what it carries. The AST spells the three payloads as three
// nodes hanging off an option; one enum says the same thing and leaves no
// fourth state to handle.
#[derive(Debug, Clone, PartialEq)]
pub struct TIRVariant {
    pub attrs:   TIRAttrs,
    pub name:    String,
    pub payload: TIRPayload,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TIRPayload {
    // `A`
    None,
    // `B(i32, str)`
    Tuple(Vec<TIRTypeId>),
    // `C { x: i32 }`
    Named(Vec<TIRFieldDecl>),
    // `D = 4`
    Discriminant(TIRExprId),
}

// ---- Generics -------------------------------------------------------------
// One list holds both kinds, as the grammar's does. Whether they may be
// interleaved is the checker's rule, so the order they were written in is kept.

// What calling a closure does to what it captured: `fn` reads it, `var fn`
// writes to it and `once fn` takes it. Ordered, so a closure stands where a
// weaker one is wanted -- reading is less than writing and writing is less
// than taking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TIRFnUses {
    Reads,
    Writes,
    Takes,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TIRGeneric {
    Type {
        name:   String,
        bounds: Vec<TIRBound>,
    },
    // The `~` was the lexer's; the name is what is left.
    Life {
        name:   String,
        bounds: Vec<TIRBound>,
    },
}

// What stands on the right of a bound's colon. A lifetime bounding a type and a
// type bounding a lifetime are both written, and turning the second down is the
// checker's -- one shape here, and the rule about it elsewhere.
#[derive(Debug, Clone, PartialEq)]
pub enum TIRBound {
    Trait(TIRTypeId),
    Life(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRWherePred {
    pub subject: TIRBound,
    pub bounds:  Vec<TIRBound>,
}

// ---- Types ----------------------------------------------------------------
// As written, and no further: resolving what a `Named` names is `sema`'s.
// A `<grouped_type>`'s parentheses are already gone -- they said which suffix
// belonged to what, and the tree says that by its shape.

#[derive(Debug, Clone, PartialEq)]
pub enum TIRTypeKind {
    Prim(TIRPrim),
    Named {
        path: Vec<String>,
        args: Vec<TIRGenericArg>,
    },
    // `&T` reads and `*T` writes. `life` is the `'a` written in front of the
    // referent, and `None` is every reference the checker works out for itself
    // -- which is all of them but the sharpened few.
    Ref {
        op:    TIRRefOp,
        life:  Option<String>,
        inner: TIRTypeId,
    },
    // `ptr T`: an address, and nothing about what is at it. No lifetime and no
    // `TIRRefOp` -- a pointer draws neither distinction, which is why only an
    // unsafe statement may hold one.
    Ptr(TIRTypeId),
    // `T[8]`: owned, its length in its type.
    Array {
        elem: TIRTypeId,
        len:  TIRExprId,
    },
    // `T[]`: a run of unknown length, which only a reference can hold.
    Run(TIRTypeId),
    Tuple(Vec<TIRTypeId>),
    // `fn(i32, str): bool`. No names and no `is_unsafe`: what a caller hands
    // over is types, and there is no spelling for an unsafe fn type. `uses` is
    // what calling it does to what the closure captured.
    Fn {
        uses:   TIRFnUses,
        params: Vec<TIRTypeId>,
        ret:    Option<TIRTypeId>,
    },
    // `_`, a type argument left to be worked out.
    Infer,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TIRGenericArg {
    Type(TIRTypeId),
    Life(String),
}

// ---- Statements -----------------------------------------------------------
// Owned by the block that holds them: nothing keys a table by a statement, so
// none of them needs a handle. `unsafe` is a flag rather than a node wrapped
// around one, there being exactly two statements it can prefix.

#[derive(Debug, Clone, PartialEq)]
pub enum TIRStmt {
    Let {
        is_unsafe: bool,
        // As on a `Global`: the word is spent and what is left is the flag.
        // `gc` and `unsafe` are unrelated -- `unsafe let gc p = addr x` is
        // both, since `addr` answers to the one and the pointer to the other.
        is_gc:     bool,
        intro:     TIRIntro,
        name:      TIRBinding,
        ty:        Option<TIRTypeId>,
        init:      Option<TIRExprId>,
    },
    Expr {
        is_unsafe: bool,
        expr:      TIRExprId,
    },
    // A declaration written inside a block.
    Item(TIRItemId),
}

// ---- Expressions ----------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum TIRExprKind {
    // `suffix` is the type a number named for itself, the `u8` of `5_u8`, and
    // only a numeric primitive can be there. It stands beside the value rather
    // than inside `TIRLit`, which the typed tree shares: there a literal has a
    // type over it, and a suffix would be the same answer written twice.
    Literal {
        value:  TIRLit,
        suffix: Option<TIRPrim>,
    },
    // A name as written. What it refers to is the resolver's, and it is a name
    // in a pattern too -- see `TIRPatKind::Name`.
    Name(Vec<String>),
    // `self` where a value is wanted: the receiver.
    SelfExpr,

    // `.x` reaches a value at run time; `::x` reaches what the compiler knows
    // the name of. The two look alike once resolved and are kept apart here for
    // exactly that reason: which separator was written is the resolver's input,
    // and folding them together would throw away what it is about to read.
    Field {
        base: TIRExprId,
        name: String,
    },
    Path {
        base: TIRExprId,
        name: String,
    },
    // `<T, U>` at a call: `foo<MyType>(x)`. Kept as its own node the way it is
    // written; whether the callee even takes them is the checker's to say.
    TypeArgs {
        base: TIRExprId,
        args: Vec<TIRGenericArg>,
    },
    // `.0`, counted rather than named.
    TupleIndex {
        base:  TIRExprId,
        index: u64,
    },

    Call {
        callee: TIRExprId,
        args:   Vec<TIRExprId>,
    },
    // A single value indexes, a range slices; both are this, and the type of
    // `index` says which.
    Index {
        base:  TIRExprId,
        index: TIRExprId,
    },
    StructLit {
        base:   TIRExprId,
        fields: Vec<TIRFieldInit>,
    },

    ArrayLit(Vec<TIRExprId>),
    TupleLit(Vec<TIRExprId>),
    // `hashed` is the glued `#`, which orders nothing and is the type's to keep.
    Map {
        hashed:  bool,
        entries: Vec<TIRMapEntry>,
    },
    Set {
        hashed: bool,
        elems:  Vec<TIRExprId>,
    },

    Unary {
        op:      TIRUnaryOp,
        operand: TIRExprId,
    },
    Binary {
        op:  TIRBinOp,
        lhs: TIRExprId,
        rhs: TIRExprId,
    },
    // `a += b` keeps its operator rather than becoming `a = a + b`: the place
    // would be written twice and evaluated twice, and saying it once needs a
    // temporary, which needs the types `sema` has not worked out yet.
    Assign {
        op:     TIRAssignOp,
        place:  TIRExprId,
        value:  TIRExprId,
    },
    // Either end may be missing: `0..10`, `0..`, `..10`, `..`.
    Range {
        op:    TIRRangeOp,
        start: Option<TIRExprId>,
        end:   Option<TIRExprId>,
    },
    Cast {
        value: TIRExprId,
        ty:    TIRTypeId,
    },
    // `is_move` is the capture mode: by value rather than by reference. What
    // by value comes to -- a copy or a move -- is the name's type, and so
    // `sema`'s.
    Closure {
        is_move: bool,
        params:  Vec<TIRParam>,
        body:    TIRExprId,
    },

    // A block is an expression, and `tail` is its value where no separator
    // ended the last thing in it.
    Block {
        stmts: Vec<TIRStmt>,
        tail:  Option<TIRExprId>,
    },
    // The `elif`s the AST keeps as written are folded here: one form, nested in
    // the `else`, and every pass below reads one shape instead of two.
    If {
        cond: TIRExprId,
        then: TIRExprId,
        els:  Option<TIRExprId>,
    },
    While {
        cond: TIRExprId,
        body: TIRExprId,
    },
    // Not folded into a `While`: what it would fold into is an iterator
    // protocol, and the language has no trait with code behind it to write one.
    For {
        name: TIRBinding,
        iter: TIRExprId,
        body: TIRExprId,
    },
    Match {
        scrutinee: TIRExprId,
        arms:      Vec<TIRArm>,
    },

    Return(Option<TIRExprId>),
    Break(Option<TIRExprId>),
    Continue,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRMapEntry {
    pub key:   TIRExprId,
    pub value: TIRExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TIRFieldInit {
    pub name:  String,
    pub value: TIRExprId,
}

// One arm, and the alternatives its pattern was written with: `Color::Red |
// Color::Blue` is two of them and one body.
#[derive(Debug, Clone, PartialEq)]
pub struct TIRArm {
    pub pats: Vec<TIRPatId>,
    pub body: TIRExprId,
}

// ---- Patterns -------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum TIRPatKind {
    // `_`
    Wildcard,
    // A bare name, still undecided. It tests against a constant where it names
    // one and binds where it does not, and which of those it is depends on what
    // is in scope -- so it stays a name until the resolver says.
    Name(Vec<String>),
    // The `-` a literal pattern may carry is folded into the value where it
    // can be, and kept as a flag where the literal has no sign of its own.
    // `suffix` is the number's own, as in `TIRExprKind::Literal`.
    Lit {
        negated: bool,
        value:   TIRLit,
        suffix:  Option<TIRPrim>,
    },
    Range {
        op: TIRRangeOp,
        lo: TIRPatId,
        hi: TIRPatId,
    },
    Variant {
        path:  Vec<String>,
        elems: Vec<TIRPatId>,
    },
    Tuple(Vec<TIRPatId>),
    Struct {
        path:   Vec<String>,
        fields: Vec<TIRFieldPat>,
    },
}

// `x: a`, and the shorthand `y` -- `pat: None`, the name binding itself.
#[derive(Debug, Clone, PartialEq)]
pub struct TIRFieldPat {
    pub name: String,
    pub pat:  Option<TIRPatId>,
}

// ---- Attributes -----------------------------------------------------------
// What a `@name` list lowered to. The set of attributes is closed, so a name is
// gone by the time a pass reads one of these: whichever was written is a field
// here, and one the compiler does not know was an error where it stood. That
// check belongs to the lowering and not to `sema` -- it needs the one
// declaration in hand and nothing else.

// `@deprecated` is the one that goes on any declaration, so every item carries
// this and only a fn carries the rest.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TIRAttrs {
    // The words the attribute was given, warned about wherever the thing it
    // marks is named.
    pub deprecated: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct TIRFnAttrs {
    pub common:   TIRAttrs,
    // `@symbol("malloc")`: the name this is compiled to, in place of the
    // mangled one. `None` is the mangling every other fn gets.
    pub symbol:   Option<String>,
    // `@must_use`: an expression statement that throws the result away is an
    // error, `let _ = f()` being how to say it was meant to go.
    pub must_use: bool,
    pub inline:   TIRInline,
    // `@test`: collected and run on its own rather than compiled into a build.
    pub is_test:  bool,
}

// `@inline` and `@noinline` are one question with three answers, so they are one
// field rather than two flags -- which is what leaves writing both a
// contradiction the lowering can turn down rather than a state to carry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TIRInline {
    // Neither was written, and the backend is left to decide.
    #[default]
    Unwritten,
    Always,
    Never,
}

// ---- Leaves ---------------------------------------------------------------
// Spelled again rather than borrowed from `parse`: a `+` means the same thing
// in both trees, but nothing below this module should have to reach into the
// syntax to name it, and `sema` importing from `parse` would be the layering
// undone for the sake of ten short enums.

#[derive(Debug, Clone, PartialEq)]
pub enum TIRLit {
    Int(i64),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
    Null,
}

// What a `<visibility_opt>` said. Unwritten is not `Private` but its own
// answer, and stays one until section 9 of docs/prose.txt settles which it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TIRVis {
    #[default]
    Unwritten,
    Pub,
    Priv,
    // `pub(suite)`: as far as the suite and no further.
    Suite,
}

// One name an import reached. A glob stands for whatever the path holds and so
// renames nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TIRImportLeaf {
    pub path:  Vec<String>,
    pub alias: Option<String>,
    pub glob:  bool,
    // Where the leaf was written. An item's own position is the `import`'s, and
    // a group holds a leaf the resolver has to be able to point at by itself.
    pub line:  usize,
    pub col:   usize,
}

// How a method takes its receiver: `self` by value, `&self` to read, `*self` to
// write through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRSelf {
    Value,
    Ref,
    Mut,
}

// `let` binds a name that is read and never written, `var` one that may be
// assigned again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRIntro {
    Let,
    Var,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TIRBinding {
    Name(String),
    // `_`, which binds nothing and so cannot be referred to.
    Discard,
    // How the receiver is held, and the region it named where it named one.
    // "the method that wants it says so" (§3): a `&'a self` is the only way to
    // tie a method's result to its receiver and not to its arguments.
    SelfRecv(TIRSelf, Option<String>),
}

// `&` reads and `*` writes; neither is a pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TIRRefOp {
    Imm,
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRUnaryOp {
    Not,
    Neg,
    // Taking a reference: `&x` and `*x`.
    Ref(TIRRefOp),
    // `addr x`: the address of a place, as a `ptr`.
    Addr,
    // `deref p`: what a `ptr` points at. A *place*, unlike the other four --
    // it may be assigned to and its address may be taken, which is what makes
    // a pointer worth having.
    Deref,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    // The logical three, over booleans rather than bits.
    And,
    Or,
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRAssignOp {
    Set,
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TIRRangeOp {
    Exclusive,
    Inclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TIRPrim {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F32,
    F64,
    Bool,
    Char,
    Str,
    // One value and no news; it belongs to every type.
    Null,
    // No values at all, so an expression of it agrees with anything beside it.
    Never,
}
