//! The syntax tree the grammar in docs/grammar.bnf describes.
//!
//! One node type for the whole tree, because that is what an LR parse wants.
//! What a node *is* lives in `ASTNodeKind`.
//!
//! A node names its children by `ASTNodeId` and owns none of them: the nodes
//! themselves sit side by side in the parser's arena, and a tree is that arena
//! together with the handle of its root. Reading one is a lookup rather than a
//! pointer to follow, and building one is an index rather than an allocation.
//!
//! The tree is of what was written, not of what it means: a name is segments
//! and no more, and parentheses are gone.

use crate::lex::tokens::Tok;

/// A node's place in the arena.
///
/// It is a `usize` like any other index, and named so that one cannot be read
/// as a length or a count -- the arena is the only thing it means anything to.
pub type ASTNodeId = usize;

/// A node, positioned at its first token — what a diagnostic points at.
#[derive(Debug, Clone, PartialEq)]
pub struct ASTNode {
    pub kind: ASTNodeKind,
    pub line: usize,
    pub col:  usize,
}

impl ASTNode {
    pub fn new(kind: ASTNodeKind, line: usize, col: usize) -> Self {
        ASTNode { kind, line, col }
    }

    /// A node beginning at a token — the reduction's leftmost, usually.
    pub fn at(kind: ASTNodeKind, tok: &Tok) -> Self {
        ASTNode { kind, line: tok.line, col: tok.col }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ASTNodeKind {
    // ---- The parser's own scaffolding ------------------------------------
    // BNF spells out optional and repetition as rules; neither reaches a tree.
    /// What an `<empty>` alternative reduces to, and what a spent arena slot
    /// holds.
    Empty,
    /// What a `<..._list>` accumulates into.
    List(Vec<ASTNodeId>),
    /// What a rule made of nothing but a word reduces to, until the rule above
    /// takes the word and drops the node. BNF spells `<additive_op> -> +` and
    /// `<visibility> -> public` as rules of their own; a tree has no such
    /// thing, and an `ASTMark` is how the word crosses the one reduction
    /// between where it was written and where it belongs.
    Mark(ASTMark),

    /// The file: its items, in the order they were written.
    Program(Vec<ASTNodeId>),

    // ---- Items -----------------------------------------------------------
    // A declaration carries its own attributes and visibility, wherever of the
    // grammar's four places it was written; in a statement they are empty.
    Import {
        /// `shapes::circle` as `["shapes", "circle"]`.
        path:  Vec<String>,
        alias: Option<String>,
    },

    Fn {
        attrs:     Vec<ASTNodeId>,
        vis:       ASTVisibility,
        is_const:  bool,
        is_unsafe: bool,
        name:      String,
        generics:  Vec<ASTNodeId>,
        params:    Vec<ASTNodeId>,
        ret:       Option<ASTNodeId>,
        wheres:    Vec<ASTNodeId>,
        /// `None` when the declaration ended in `;`: a signature, not a body.
        body:      Option<ASTNodeId>,
    },

    Struct {
        attrs:    Vec<ASTNodeId>,
        vis:      ASTVisibility,
        name:     String,
        generics: Vec<ASTNodeId>,
        fields:   Vec<ASTNodeId>,
    },

    Enum {
        attrs:    Vec<ASTNodeId>,
        vis:      ASTVisibility,
        name:     String,
        generics: Vec<ASTNodeId>,
        variants: Vec<ASTNodeId>,
    },

    Trait {
        attrs:    Vec<ASTNodeId>,
        vis:      ASTVisibility,
        name:     String,
        generics: Vec<ASTNodeId>,
        members:  Vec<ASTNodeId>,
    },

    Impl {
        attrs:    Vec<ASTNodeId>,
        vis:      ASTVisibility,
        generics: Vec<ASTNodeId>,
        /// The trait when there is a `for`, and the type itself when there is not.
        ty:       ASTNodeId,
        for_ty:   Option<ASTNodeId>,
        wheres:   Vec<ASTNodeId>,
        members:  Vec<ASTNodeId>,
    },

    Namespace {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        name:  String,
        items: Vec<ASTNodeId>,
    },

    /// `let` and `var`, which is a declaration and a statement both.
    Variable {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        intro: ASTVariableIntro,
        name:  ASTBinding,
        ty:    Option<ASTNodeId>,
        init:  Option<ASTNodeId>,
    },

    /// A `const` declaration, which spells its type and its value both.
    Const {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        name:  String,
        ty:    ASTNodeId,
        value: ASTNodeId,
    },

    // ---- The pieces items are made of ------------------------------------
    /// `@repr(C)`, and the `C` inside it — an argument is another of these.
    Attr {
        name: String,
        args: Vec<ASTNodeId>,
    },

    /// A parameter of a function or of a closure, which differ only in `this`.
    Param {
        name: ASTBinding,
        ty:   Option<ASTNodeId>,
    },

    FieldDecl {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        name:  String,
        ty:    ASTNodeId,
    },

    /// `body` is `None` for a bare `A`, else one of the three tails below.
    EnumVariant {
        attrs: Vec<ASTNodeId>,
        name:  String,
        body:  Option<ASTNodeId>,
    },
    /// `B(i32, str)`: the types, in order.
    TuplePayload(Vec<ASTNodeId>),
    /// `C { x: i32 }`: `FieldDecl`s, the same ones a struct holds.
    NamedPayload(Vec<ASTNodeId>),
    /// `D = 4`.
    Discriminant(ASTNodeId),

    /// One parameter of a `<T: Ord + Show>`; `bounds` may be empty.
    GenericParam {
        name:   String,
        bounds: Vec<ASTNodeId>,
    },

    /// One predicate of a `where`: `T: Ord + Show`.
    WherePred {
        ty:     ASTNodeId,
        bounds: Vec<ASTNodeId>,
    },

    // ---- Types -----------------------------------------------------------
    // A cast's type is one of these too, though it is a smaller language.
    /// `&T` reads and `*T` writes; see section 3 of docs/prose.txt.
    RefType {
        op:    ASTRefOp,
        inner: ASTNodeId,
    },
    /// `T[8]`: a fixed array, owned, its length in its type.
    Array {
        elem: ASTNodeId,
        len:  ASTNodeId,
    },
    /// `T[]`: a run of T with no size, so it exists only behind a reference.
    Run(ASTNodeId),
    Prim(ASTPrimType),
    /// `Map<str, List<i32>>`: a name, and the arguments it was given.
    Named {
        path: Vec<String>,
        args: Vec<ASTNodeId>,
    },
    /// `(i32, str)`: the members, in order, and two of them at least — a `(T)`
    /// is a T, the parentheses there having grouped and nothing more.
    TupleType(Vec<ASTNodeId>),
    /// `_`, where a type is wanted but left to be worked out.
    Infer,

    // ---- Statements ------------------------------------------------------
    /// An expression written for what it does, its value discarded.
    ExprStmt(ASTNodeId),
    /// `unsafe` in front of a statement; on a function it is `Fn::is_unsafe`.
    Unsafe(ASTNodeId),

    // ---- Expressions -----------------------------------------------------
    Literal(ASTLit),
    /// A name standing on its own, in an expression.
    Ident(String),
    This,

    /// A `::`-separated name, in a type, an import or a pattern.
    Name(Vec<String>),

    /// `[1, 2, 3]`, which is a fixed array.
    ArrayLit(Vec<ASTNodeId>),
    /// `(1, "a")`: the members of a tuple, in order. Two at least, for the
    /// reason `TupleType` gives.
    TupleLit(Vec<ASTNodeId>),
    /// `hashed` is the `#` of `#{1: 2}`; `{}` and `{:}` are both empty maps.
    Map {
        hashed:  bool,
        entries: Vec<ASTNodeId>,
    },
    /// `{1, 2, 3}` and `#{1, 2}`; `{,}` is the empty one — `{}` is a map.
    Set {
        hashed: bool,
        elems:  Vec<ASTNodeId>,
    },
    MapEntry {
        key:   ASTNodeId,
        value: ASTNodeId,
    },

    // A postfix takes the whole expression to its left, which is what lets
    // `shapes.Color::Red` and `shapes.Point { x: 1 }` be said at all.
    /// `.x`
    Field {
        base: ASTNodeId,
        name: String,
    },
    /// `.0`, which reaches into a tuple. A member there is counted rather than
    /// named, so what it holds is the number and not a `Field`'s spelling.
    TupleIndex {
        base:  ASTNodeId,
        index: u64,
    },
    /// `::x`, a suffix here because a name can want a `.` on either side of it.
    Path {
        base: ASTNodeId,
        name: String,
    },
    Call {
        callee: ASTNodeId,
        args:   Vec<ASTNodeId>,
    },
    /// `a[i]`, and `a[1..3]` — the index is any expression, a range included.
    Index {
        base:  ASTNodeId,
        index: ASTNodeId,
    },
    /// `Point { x: 1 }`, whose `base` is the expression naming the type.
    StructLit {
        base:   ASTNodeId,
        fields: Vec<ASTNodeId>,
    },
    FieldInit {
        name:  String,
        value: ASTNodeId,
    },

    Unary {
        op:      ASTUnaryOp,
        operand: ASTNodeId,
    },
    /// Precedence is spent: the grammar's ladder is now the tree's shape.
    Binary {
        op:  ASTBinOp,
        lhs: ASTNodeId,
        rhs: ASTNodeId,
    },
    Assign {
        op:     ASTAssignOp,
        target: ASTNodeId,
        value:  ASTNodeId,
    },
    /// Either end may be missing: `0..10`, `0..`, `..10`, `..`.
    Range {
        op:    ASTRangeOp,
        start: Option<ASTNodeId>,
        end:   Option<ASTNodeId>,
    },
    Cast {
        value: ASTNodeId,
        ty:    ASTNodeId,
    },

    Closure {
        is_move: bool,
        params:  Vec<ASTNodeId>,
        body:    ASTNodeId,
    },

    /// `tail` is the last thing in the body when no `;` ended it: its value.
    Block {
        stmts: Vec<ASTNodeId>,
        tail:  Option<ASTNodeId>,
    },

    /// The `elif`s are kept as written, not folded into nested `If`s.
    If {
        cond:       ASTNodeId,
        then:       ASTNodeId,
        elifs:      Vec<ASTNodeId>,
        else_block: Option<ASTNodeId>,
    },
    /// One `elif c { ... }` of the list above.
    Elif {
        cond:  ASTNodeId,
        block: ASTNodeId,
    },
    While {
        cond: ASTNodeId,
        body: ASTNodeId,
    },
    For {
        name: ASTBinding,
        iter: ASTNodeId,
        body: ASTNodeId,
    },
    Match {
        scrutinee: ASTNodeId,
        arms:      Vec<ASTNodeId>,
    },
    /// `pats` holds one arm's alternatives: `Color::Red | Color::Blue` is two.
    MatchArm {
        pats: Vec<ASTNodeId>,
        body: ASTNodeId,
    },

    Return(Option<ASTNodeId>),
    Break(Option<ASTNodeId>),
    Continue,

    // ---- Patterns --------------------------------------------------------
    // A bare name is a `Name`: whether it matches or binds is not ours to say.
    /// `_`
    Wildcard,
    /// A literal, and the `-` a literal pattern may carry.
    LitPat {
        negated: bool,
        value:   ASTLit,
    },
    /// `1..=9`, whose ends are `LitPat`s.
    RangePat {
        op: ASTRangeOp,
        lo: ASTNodeId,
        hi: ASTNodeId,
    },
    /// `Shape::Circle(r)`: a variant, and the payload it was written with.
    VariantPat {
        path:  Vec<String>,
        elems: Vec<ASTNodeId>,
    },
    /// `(a, b)`: the same payload with no name in front of it, which is a
    /// tuple being taken apart rather than a variant.
    TuplePat(Vec<ASTNodeId>),
    /// `Point { x: a, y }`
    StructPat {
        path:   Vec<String>,
        fields: Vec<ASTNodeId>,
    },
    /// `x: a`, and the shorthand `y` — `pat: None`, the name binding itself.
    FieldPat {
        name: String,
        pat:  Option<ASTNodeId>,
    },
}

/// A word a rule carried up to the rule that wanted it. Never in a finished
/// tree: whatever takes one puts it in a field of its own -- an operator, a
/// visibility, a `let` -- and the node it came in is spent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTMark {
    Bin(ASTBinOp),
    Assign(ASTAssignOp),
    Unary(ASTUnaryOp),
    Range(ASTRangeOp),
    Ref(ASTRefOp),
    Vis(ASTVisibility),
    Intro(ASTVariableIntro),
    /// `move`, which is a closure's and has nothing under it.
    Move,
}

/// The leaves that are not nodes: a spelling, and no position under it.
#[derive(Debug, Clone, PartialEq)]
pub enum ASTLit {
    Int(i64),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
    /// The one value of the type `null`, yielded when nothing else is.
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTVisibility {
    /// Neither word was written.
    Unwritten,
    Public,
    Private,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTVariableIntro {
    Let,
    Var,
}

/// A name being bound. `This` is a parameter's only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ASTBinding {
    Name(String),
    /// `_`: bound to nothing on purpose. `_foo` is an ordinary name.
    Discard,
    This,
}

/// `&` and `*`, which decide only whether writing through is allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTRefOp {
    /// `&`
    Imm,
    /// `*`
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTUnaryOp {
    /// `!`
    Not,
    /// `-`
    Neg,
    /// `&x` and `*x`, which take a reference; neither dereferences.
    Ref(ASTRefOp),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    /// `&` between two operands, which is `And` on their bits. The same `&`
    /// in front of one is a reference and reaches here as an `ASTUnaryOp`.
    BitAnd,
    /// `|` between two operands. The `|` of a closure's parameters and the one
    /// between a pattern's alternatives are neither, and neither reaches here.
    BitOr,
    /// `^`
    BitXor,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    /// `&&`
    And,
    /// `||`
    Or,
    /// `^^`. The one of the three that settles nothing until both sides are
    /// known, so there is no short-circuit to it.
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTAssignOp {
    /// `=`
    Set,
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    /// `^=`
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTRangeOp {
    /// `..`
    Exclusive,
    /// `..=`
    Inclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTPrimType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    Char,
    Str,
    /// One value, no information.
    Null,
    /// No values at all, so an expression of it argues with nothing beside it.
    Never,
}
