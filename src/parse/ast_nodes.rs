// The syntax tree docs/grammar.bnf describes. One node type for the whole tree,
// because that is what an LR parse wants; what a node *is* lives in
// `ASTNodeKind`.
//
// A node names its children by `ASTNodeId` and owns none of them: the nodes sit
// side by side in the parser's arena, and a tree is that arena plus the handle
// of its root.
//
// The tree is of what was written, not of what it means: a name is segments and
// no more, and parentheses are gone.

use crate::lex::tokens::Tok;

// A node's place in the arena. Named so it cannot be read as a length or a
// count -- the arena is the only thing it means anything to.
pub type ASTNodeId = usize;

// A node, positioned at its first token — what a diagnostic points at.
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

    // A node beginning at a token — the reduction's leftmost, usually.
    pub fn at(kind: ASTNodeKind, tok: &Tok) -> Self {
        ASTNode { kind, line: tok.line, col: tok.col }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ASTNodeKind {
    // ---- The parser's own scaffolding ------------------------------------
    // BNF spells out optional and repetition as rules; neither reaches a tree.
    // What an `<empty>` alternative reduces to, and what a spent slot holds.
    Empty,
    // What a `<..._list>` accumulates into.
    List(Vec<ASTNodeId>),
    // What a rule made of nothing but a word reduces to, until the rule above
    // takes the word and drops the node. BNF spells `<additive_op> -> +` as a
    // rule of its own; a tree has no such thing.
    Mark(ASTMark),

    // The file: its items, in the order they were written.
    Program(Vec<ASTNodeId>),

    // ---- Items -----------------------------------------------------------
    // A declaration carries its own attributes and visibility, wherever of the
    // grammar's four places it was written; in a statement they are empty.
    Import {
        attrs:  Vec<ASTNodeId>,
        vis:    ASTVisibility,
        // Every name the tree reached, flattened: `a::{b, c::*}` is two leaves.
        // The visibility is the import's and not a leaf's — `pub import`
        // re-exports everything it brought in.
        leaves: Vec<ASTImportLeaf>,
    },

    // What an import's tree has come to so far, on its way up to the `import`
    // that will hold it. Payload and no handles, so a group nests for free.
    ImportTree(Vec<ASTImportLeaf>),

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
        // `None` when the declaration ended in `;`: a signature, not a body.
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
        // The trait when there is a `for`, and the type itself when there is not.
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

    // `let` and `var`, which is a declaration and a statement both.
    Variable {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        intro: ASTVariableIntro,
        // The `gc` between the intro and the name: the binding owns its value
        // through the collector. A flag rather than a node, there being one
        // word and nothing under it -- as `is_unsafe` is on a `Fn`. What may
        // stand on the right of one is `tir::lower`'s rule, not the grammar's.
        gc:    bool,
        name:  ASTBinding,
        ty:    Option<ASTNodeId>,
        init:  Option<ASTNodeId>,
    },

    // `type MyType = i32`: a name for a type. It makes no new type -- what it
    // names is the type, and the alias is gone once anything has resolved it.
    TypeAlias {
        attrs:    Vec<ASTNodeId>,
        vis:      ASTVisibility,
        name:     String,
        generics: Vec<ASTNodeId>,
        ty:       ASTNodeId,
    },

    // A `const` declaration, which spells its type and its value both.
    Const {
        attrs: Vec<ASTNodeId>,
        vis:   ASTVisibility,
        name:  String,
        ty:    ASTNodeId,
        value: ASTNodeId,
    },

    // ---- The pieces items are made of ------------------------------------
    // A macro: `macro twice($x:expr) { .. }`. Its body is a block, and its
    // parameters are `MacroParam`s.
    MacroDecl {
        attrs:  Vec<ASTNodeId>,
        vis:    ASTVisibility,
        name:   String,
        params: Vec<ASTNodeId>,
        body:   ASTNodeId,
    },

    // One `$x:expr` of a macro's parameter list. `fragment` is the word after
    // the colon, unchecked here: the set of them is closed and the compiler
    // knows it, as it knows the attributes.
    MacroParam {
        name:     String,
        fragment: String,
    },

    // `$x` where the body spells it, the `$` having been the lexer's. It stands
    // in an expression, a type and a pattern, and which of those its fragment
    // allows is the checker's.
    MacroVar(String),

    // `@println(x)`: the name without its `@`, and the arguments as written.
    MacroCall {
        name: String,
        args: Vec<ASTNodeId>,
    },

    // `%repr(C)`, and the `C` inside it — an argument is another of these.
    Attr {
        name: String,
        args: Vec<ASTNodeId>,
    },

    // A parameter of a function or of a closure, which differ only in `this`.
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

    // `body` is `None` for a bare `A`, else one of the three tails below.
    EnumVariant {
        attrs: Vec<ASTNodeId>,
        name:  String,
        body:  Option<ASTNodeId>,
    },
    // `B(i32, str)`: the types, in order.
    TuplePayload(Vec<ASTNodeId>),
    // `C { x: i32 }`: `FieldDecl`s, the same ones a struct holds.
    NamedPayload(Vec<ASTNodeId>),
    // `D = 4`.
    Discriminant(ASTNodeId),

    // One parameter of a `<T: Ord + Show>`; `bounds` may be empty.
    GenericParam {
        name:   String,
        bounds: Vec<ASTNodeId>,
    },

    // A lifetime where it is named: `'a`, without the `~`. It stands as a
    // generic argument, as a bound, and in front of what a reference refers to.
    Lifetime(String),

    // One lifetime parameter of a `<'a, T>`; `bounds` may be empty. Its own
    // variant rather than a `GenericParam` with a flag, because the two are
    // different kinds of name and every pass that reads one has to know which.
    LifetimeParam {
        name:   String,
        bounds: Vec<ASTNodeId>,
    },

    // One predicate of a `where`: `T: Ord + Show`, or `'a: 'b`, whose `ty` is
    // a `Lifetime`.
    WherePred {
        ty:     ASTNodeId,
        bounds: Vec<ASTNodeId>,
    },

    // ---- Types -----------------------------------------------------------
    // A cast's type is one of these too, though it is a smaller language.
    // `&T` reads and `*T` writes; see section 3 of docs/prose.txt.
    RefType {
        op:    ASTRefOp,
        // The lifetime written in front of the referent, `&'a T`. `None` where
        // none was written, which is every reference the checker is left to
        // work out for itself -- and, so far, every reference in a cast.
        life:  Option<ASTNodeId>,
        inner: ASTNodeId,
    },
    // `ptr T`: an address and no more. No lifetime, because a pointer says
    // nothing about how long what it points at is good for -- which is what
    // keeps it inside an `unsafe`.
    PtrType(ASTNodeId),
    // `dyn Shape`: whatever type turned out to answer the trait. The child is
    // the <named_type> after the word, which is a name like any other here --
    // whether it names a trait at all is the checker's to say.
    DynType(ASTNodeId),
    // `T[8]`: a fixed array, owned, its length in its type.
    Array {
        elem: ASTNodeId,
        len:  ASTNodeId,
    },
    // `T[]`: a run of T with no size, so it exists only behind a reference.
    Run(ASTNodeId),
    Prim(ASTPrimType),
    // `Map<str, List<i32>>`: a name, and the arguments it was given.
    Named {
        path: Vec<String>,
        args: Vec<ASTNodeId>,
    },
    // `(i32, str)`: the members, in order, two at least — a `(T)` is a T, the
    // parentheses having grouped and nothing more.
    TupleType(Vec<ASTNodeId>),
    // `_`, where a type is wanted but left to be worked out.
    Infer,

    // ---- Statements ------------------------------------------------------
    // An expression written for what it does, its value discarded.
    ExprStmt(ASTNodeId),
    // `unsafe` in front of a statement; on a function it is `Fn::is_unsafe`.
    Unsafe(ASTNodeId),

    // ---- Expressions -----------------------------------------------------
    Literal(ASTLit),
    // A name standing on its own, in an expression.
    Ident(String),
    // `self`: the receiver where a value is wanted, and the module a path
    // starts in where a path is. Which one is the resolver's to say.
    SelfExpr,
    // `fn(i32, str): bool`, which is what a closure's type is written as. No
    // parameter names: a caller hands over types, and what they were called
    // where the closure was written is the closure's own business.
    FnType {
        uses:   ASTFnUses,
        params: Vec<ASTNodeId>,
        ret:    Option<ASTNodeId>,
    },

    // A receiver, as a parameter list holds it: `self`, `&self`, `*self`, and
    // the same two with a lifetime in front -- `&'a self`.
    SelfRecv(ASTSelf, Option<String>),

    // A `::`-separated name, in a type, an import or a pattern.
    Name(Vec<String>),

    // `[1, 2, 3]`, which is a fixed array.
    ArrayLit(Vec<ASTNodeId>),
    // `(1, "a")`: the members, in order. Two at least, as `TupleType` says.
    TupleLit(Vec<ASTNodeId>),
    // `hashed` is the `#` of `#{1: 2}`; `{}` and `{:}` are both empty maps.
    Map {
        hashed:  bool,
        entries: Vec<ASTNodeId>,
    },
    // `{1, 2, 3}` and `#{1, 2}`; `{,}` is the empty one — `{}` is a map.
    Set {
        hashed: bool,
        elems:  Vec<ASTNodeId>,
    },
    MapEntry {
        key:   ASTNodeId,
        value: ASTNodeId,
    },

    // A postfix takes the whole expression to its left, which is what lets
    // `shapes::Color::Red` and `shapes::Point { x: 1 }` be said at all.
    // `.x`
    Field {
        base: ASTNodeId,
        name: String,
    },
    // `.0`, which reaches into a tuple: counted rather than named, so it holds
    // the number and not a `Field`'s spelling.
    TupleIndex {
        base:  ASTNodeId,
        index: u64,
    },
    // `<T, U>` at a call: `foo<MyType>(x)`. A suffix like the rest, and built
    // before its base like the rest -- what it is the type arguments *of* is not
    // on the stack yet. Which `<` opens one is the lexer's to have decided.
    TypeArgs {
        base: ASTNodeId,
        args: Vec<ASTNodeId>,
    },

    // `::x`, a suffix here because a name can want a `.` on either side of it.
    Path {
        base: ASTNodeId,
        name: String,
    },
    Call {
        callee: ASTNodeId,
        args:   Vec<ASTNodeId>,
    },
    // `a[i]`, and `a[1..3]` — the index is any expression, a range included.
    Index {
        base:  ASTNodeId,
        index: ASTNodeId,
    },
    // `Point { x: 1 }`, whose `base` is the expression naming the type.
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
    // Precedence is spent: the grammar's ladder is now the tree's shape.
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
    // Either end may be missing: `0..10`, `0..`, `..10`, `..`.
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

    // `tail` is the last thing in the body when no `;` ended it: its value.
    Block {
        stmts: Vec<ASTNodeId>,
        tail:  Option<ASTNodeId>,
    },

    // The `elif`s are kept as written, not folded into nested `If`s.
    If {
        cond:       ASTNodeId,
        then:       ASTNodeId,
        elifs:      Vec<ASTNodeId>,
        else_block: Option<ASTNodeId>,
    },
    // One `elif c { ... }` of the list above.
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
    // `pats` holds one arm's alternatives: `Color::Red | Color::Blue` is two.
    MatchArm {
        pats: Vec<ASTNodeId>,
        body: ASTNodeId,
    },

    Return(Option<ASTNodeId>),
    Break(Option<ASTNodeId>),
    Continue,

    // ---- Patterns --------------------------------------------------------
    // A bare name is a `Name`: whether it matches or binds is not ours to say.
    // `_`
    Wildcard,
    // A literal, and the `-` a literal pattern may carry.
    LitPat {
        negated: bool,
        value:   ASTLit,
    },
    // `1..=9`, whose ends are `LitPat`s.
    RangePat {
        op: ASTRangeOp,
        lo: ASTNodeId,
        hi: ASTNodeId,
    },
    // `Shape::Circle(r)`: a variant, and the payload it was written with.
    VariantPat {
        path:  Vec<String>,
        elems: Vec<ASTNodeId>,
    },
    // `(a, b)`: the same payload unnamed — a tuple taken apart, not a variant.
    TuplePat(Vec<ASTNodeId>),
    // `Point { x: a, y }`
    StructPat {
        path:   Vec<String>,
        fields: Vec<ASTNodeId>,
    },
    // `x: a`, and the shorthand `y` — `pat: None`, the name binding itself.
    FieldPat {
        name: String,
        pat:  Option<ASTNodeId>,
    },
}

// A word a rule carried up to the rule that wanted it. Never in a finished
// tree: whatever takes one puts it in a field of its own, and the node is spent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTMark {
    Bin(ASTBinOp),
    Assign(ASTAssignOp),
    Unary(ASTUnaryOp),
    Range(ASTRangeOp),
    Ref(ASTRefOp),
    Vis(ASTVisibility),
    Intro(ASTVariableIntro),
    // What calling a closure does to what it captured: the word in front of a
    // `<fn_type>`, where one was written.
    Uses(ASTFnUses),
    // `move`, which is a closure's and has nothing under it.
    Move,
    // `gc`, which is a binding's and has nothing under it either.
    Gc,
}

// The leaves that are not nodes: a spelling, and no position under it.
//
// A number carries the type its own spelling named -- the `u8` of `5_u8` -- as
// the primitive it names. Only the twelve numeric ones can be there, the lexer
// spelling no other suffix, and holding it as an `ASTPrimType` is what lets the
// checker hold it against a type without translating first.
#[derive(Debug, Clone, PartialEq)]
pub enum ASTLit {
    Int(i64, Option<ASTPrimType>),
    Float(f64, Option<ASTPrimType>),
    Str(String),
    Char(char),
    Bool(bool),
    // The one value of the type `null`, yielded when nothing else is.
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTVisibility {
    // Neither word was written.
    Unwritten,
    Pub,
    Priv,
    // `pub(suite)`: exported to the rest of the suite and no further.
    Suite,
}

// One name an import reached. A glob names none of them and stands for whatever
// the path holds, which is why it carries no alias: there is nothing to rename.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ASTImportLeaf {
    // `shapes::circle` as `["shapes", "circle"]`, the roots spelled as the
    // words they were written with.
    pub path:  Vec<String>,
    pub alias: Option<String>,
    pub glob:  bool,
    // Where this leaf begins, which is not where the `import` does: a group
    // holds several and the resolver has something to say about each on its
    // own, so `a::{b, c}` has to be able to point at the `c`.
    pub line:  usize,
    pub col:   usize,
}

// How a method takes its receiver. `&self` reads it, `*self` writes through it,
// and a bare `self` takes the value whole.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTSelf {
    Value,
    Ref,
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTVariableIntro {
    Let,
    Var,
}

// A name being bound. `SelfRecv` is a parameter's only, and a method's at that:
// a closure shares `Param` and never has one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ASTBinding {
    Name(String),
    // `_`: bound to nothing on purpose. `_foo` is an ordinary name.
    Discard,
    // How it was taken, and the region it named where it named one.
    SelfRecv(ASTSelf, Option<String>),
}

// What calling a closure does to what it captured, which is the same
// distinction a binding draws with `let` and `var` plus a third for the one
// that takes. Ordered: reading is less than writing and writing is less than
// taking, so a closure stands where a weaker one is wanted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ASTFnUses {
    // `fn(..)`: reads what it captured.
    Reads,
    // `var fn(..)`: writes to what it captured, so one holder at a time.
    Writes,
    // `once fn(..)`: takes what it captured, so one call and no more.
    Takes,
}

// `&` and `*`, which decide only whether writing through is allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTRefOp {
    // `&`
    Imm,
    // `*`
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTUnaryOp {
    // `!`
    Not,
    // `-`
    Neg,
    // `&x` and `*x`, which take a reference; neither dereferences.
    Ref(ASTRefOp),
    // `addr x`, which takes the address of a place as a `ptr`. The one
    // operator no safe statement may write.
    Addr,
    // `deref p`, which reaches what a `ptr` points at. `addr` makes an address
    // and this is what an address is for, so the two are a pair and are
    // written as one -- and like `addr` it is not something a safe statement
    // may write.
    Deref,
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
    // `&` between two operands. In front of one it is a reference, and reaches
    // here as an `ASTUnaryOp`.
    BitAnd,
    // `|` between two operands. A closure's parameters and a pattern's
    // alternatives are neither, and neither reaches here.
    BitOr,
    // `^`
    BitXor,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    // `&&`
    And,
    // `||`
    Or,
    // `^^`, which settles nothing until both sides are known: no short-circuit.
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTAssignOp {
    // `=`
    Set,
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    // `^=`
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTRangeOp {
    // `..`
    Exclusive,
    // `..=`
    Inclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ASTPrimType {
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
    // One value, no information.
    Null,
    // No values at all, so an expression of it argues with nothing beside it.
    Never,
}
