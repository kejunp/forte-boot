#[derive(Debug, Clone, PartialEq)]
pub enum TokType {
    // Types
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
    // The empty type: no values at all, so an expression of it argues with
    // nothing beside it. `null` is its opposite — one value, no information.
    Never,

    // Declarations
    Fn,
    Let,
    Var,
    Const,
    Struct,
    Trait,
    Impl,
    Public,
    Private,
    Import,
    Enum,
    Namespace,
    // Marks a fn whose caller carries an obligation the checker cannot see,
    // and prefixes the statement — usually a block — that discharges one.
    Unsafe,

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
    This,
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
    IntLiteral(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    CharLiteral(char),

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
    GreaterThan,
    LessOrEqual,
    GreaterOrEqual,

    // Logical operators
    And,
    Or,
    Bang,

    // A lone `|`: pattern alternation, and a closure's parameter list. Told
    // from `||` the way `&` is told from `&&` — by whether an operand ends in
    // front of it.
    Pipe,

    // Reference operators. `&` takes an immutable reference and `*` a mutable
    // one, in a type and in an expression alike; `Star` above is the same token
    // as the multiplication one, told apart by where it stands.
    Ampersand,

    // Type operators
    As,
    Where,

    // Forces a closure to capture by value. See `closure_expr` in the grammar.
    Move,

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
    Comma,
    Dot,
    Semicolon,
    FatArrow,
    // `#` has one use left: `#{` makes a map or set literal hashed. Attributes
    // are `@`.
    HashTag,
    At,

    // Special
    EOF,
    Error(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tok {
    pub line:    usize,
    pub col:     usize,
    pub toktype: TokType,
}

