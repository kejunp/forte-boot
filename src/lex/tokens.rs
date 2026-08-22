#[derive(Debug, Clone, PartialEq)]
pub enum TokType {
    // Types
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
    // The empty type: no values at all, so an expression of it argues with
    // nothing beside it. `null` is its opposite — one value, no information.
    Never,
    // `ptr T`: an address and nothing more. Not a reference — nothing is
    // checked about what it points at — so only an unsafe statement holds one.
    Ptr,

    // Declarations
    Fn,
    Let,
    Var,
    Const,
    Struct,
    Trait,
    // `type MyType = i32`: a name for a type, and nothing new to check.
    Type,
    Impl,
    Pub,
    Priv,
    Import,
    // The two roots a path may start from: the suite a file is compiled in, and
    // the module above the one the path is written in. `self` is the third and
    // is a literal below, being an expression as well.
    Suite,
    Super,
    Enum,
    Namespace,
    // Declares a macro: `macro foo($x:expr) { .. }`.
    Macro,
    // Marks a fn whose caller carries an obligation the checker cannot see,
    // and prefixes the statement — usually a block — that discharges one.
    Unsafe,
    // `let gc x = ...`: the binding owns its value through the collector rather
    // than through a scope. It stands between the intro and the name, so it
    // annotates the binding and not the value — see `ASTNodeKind::Variable`.
    Gc,

    // Control flow
    If,
    Elif,
    Else,
    While,
    For,
    In,
    Return,
    Break,
    Continue,
    Match,

    // Literals
    True,
    False,
    // A method's receiver, and the module a path starts in. Both are `self`,
    // and which one it is depends on where it stands.
    SelfKw,
    // Both a literal and a type name: `null` is the one value of the type
    // `null`, which is what a function, a block or a loop yields when it
    // yields nothing in particular. There is no `void`.
    Null,

    // The wildcard: a pattern that matches anything, and the name of a binding
    // whose value is deliberately unused. A lone `_` only — `_foo` and `__` are
    // ordinary identifiers.
    Underscore,

    // Literal values
    Identifier(String),
    // A number and the type its spelling named, `5_u8` being `IntLiteral(5,
    // Some(U8))`. The suffix is part of the token and not one of its own, for
    // the reason a lifetime is one token: no space may come between a number
    // and its suffix, and two tokens could not say so.
    IntLiteral(i64, Option<NumSuffix>),
    FloatLiteral(f64, Option<NumSuffix>),
    StringLiteral(String),
    CharLiteral(char),

    // A macro invocation's name, `@println`, without the `@`. One token for
    // the same reason a lifetime is: `@` spells nothing else now that the
    // attributes have moved to `%`, so a space could change no reading.
    MacroName(String),
    // An attribute's name, `%repr`, without the `%`. `%` is the remainder
    // operator as well, and where it stands is what tells the two apart: an
    // operand before it makes it the operator, and anything else makes it this.
    AttrName(String),
    // A macro's parameter where the body spells it, `$x`, without the `$`.
    MacroParam(String),

    // A lifetime, `'a`, carrying its name without the `'`. One token and not
    // two, so no space can come between the sigil and the name. The same `'`
    // opens a character literal, and which one it is depends on what follows
    // the name -- see `opens_lifetime`.
    Lifetime(String),

    // Takes the address of a place, `addr x`, and is the only thing that makes
    // a `ptr`. A word rather than a sigil because `&` and `*` are the two
    // references and neither had a spelling left over.
    Addr,

    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    LShift,
    RShift,

    // Comparison operators
    EqualsEquals,
    BangEquals,
    LessThan,
    // The `<` that opens a type argument list at a call: `foo<T>(x)`. A `<` is
    // a comparison everywhere else, and nothing in front of it says which --
    // the lexer looks ahead for the matching `>` and what follows it, and says
    // so here. The same decision `LCurlyValue` carries for a brace.
    LessGeneric,
    GreaterThan,
    LessOrEqual,
    GreaterOrEqual,

    // Logical operators
    And,
    Or,
    // `^^`. The one of the three with no short-circuit to it: both sides of an
    // exclusive or have to be known before the answer is.
    Xor,
    Bang,

    // A lone `|`: pattern alternation, and a closure's parameter list. Told
    // from `||` the way `&` is told from `&&` — by whether an operand ends in
    // front of it.
    Pipe,

    // Reference operators. `&` takes an immutable reference and `*` a mutable
    // one, in a type and in an expression alike; `Star` above is the same token
    // as the multiplication one, told apart by where it stands.
    Ampersand,

    // A lone `^`: exclusive or, on the bits. Unlike `&` and `|` it spells one
    // thing only -- nothing is prefixed with it and no pattern uses it -- so
    // `^^` needs no deciding and is always the logical one.
    Caret,

    // Type operators
    As,
    Where,

    // Forces a closure to capture by value. See `closure_expr` in the grammar.
    Move,
    // `once fn(..)`: a fn type that may be called once, because calling it
    // takes what the closure captured.
    Once,

    // Range operators
    DotDot,
    DotDotEquals,

    // Assignment
    Equals,
    PlusEquals,
    MinusEquals,
    StarEquals,
    SlashEquals,
    AndEquals,
    OrEquals,
    CaretEquals,
    LShiftEquals,
    RShiftEquals,

    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurlyBracket,
    // The `{` of a value: a struct literal's, a map's, a set's. A block's and a
    // body's is `LCurlyBracket`, and telling the two apart is the lexer's to do
    // — nothing in front of the brace says which it is, and the parser, reading
    // one token at a time, would have to guess. See `push_brace`.
    LCurlyValue,
    RCurlyBracket,
    Colon,
    ColonColon,
    // `::*`, the glob of an import, glued as one token the way `%name` and `#{`
    // are. A `*` on its own is the multiplication and the reference both, and
    // neither ends an operand; this does, so an import that globs may end its
    // line without a `;` like every other declaration. `a:: *` with a space in
    // it is two tokens and no glob, as a space likewise ends an attribute.
    Glob,
    Comma,
    Dot,
    Semicolon,
    FatArrow,
    // `#` has one use left: `#{` makes a map or set literal hashed. Attributes
    // are `%name` and macros `@name`, and neither leaves a sigil of its own.
    HashTag,

    // Special
    EOF,
    Error(String),
}

// The type a number literal named for itself: the `u8` of `5_u8`. Only the
// numeric primitives can be said this way -- `bool` and `str` have literals of
// their own and nothing to ascribe -- so this is its own short list rather than
// the whole of the primitives with ten spellings the lexer would have to refuse.
//
// Whether the value fits the type it named is not asked here. `-128_i8` is a
// negation of `128_i8`, and only a tree that has the `-` in it can tell that
// one from the overflow it looks like; the checker asks, once it exists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumSuffix {
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
}

impl NumSuffix {
    // The suffix a word spells, or `None` where it spells no suffix at all.
    pub fn of(word: &str) -> Option<NumSuffix> {
        Some(match word {
            "i8" => NumSuffix::I8,
            "i16" => NumSuffix::I16,
            "i32" => NumSuffix::I32,
            "i64" => NumSuffix::I64,
            "i128" => NumSuffix::I128,
            "u8" => NumSuffix::U8,
            "u16" => NumSuffix::U16,
            "u32" => NumSuffix::U32,
            "u64" => NumSuffix::U64,
            "u128" => NumSuffix::U128,
            "f32" => NumSuffix::F32,
            "f64" => NumSuffix::F64,
            _ => return None,
        })
    }

    // Whether the suffix names a float type, and so may follow a decimal point.
    pub fn is_float(self) -> bool {
        matches!(self, NumSuffix::F32 | NumSuffix::F64)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tok {
    pub line:    usize,
    pub col:     usize,
    // How many characters the token was written with, so a diagnostic can
    // underline the whole of it. Counted from the input and not the spelling:
    // `0x10` and `16` are the same `IntLiteral`. Zero where nothing was written
    // -- end of file, and inserted separators -- which is a place, not a span.
    pub len:     usize,
    pub toktype: TokType,
}

