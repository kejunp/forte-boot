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
    Void,

    // Declarations
    Fn,
    Let,
    Var,
    Struct,
    Trait,
    Impl,
    Public,
    Private,
    Import,
    Enum,

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

    // Type operators
    As,

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
    RCurlyBracket,
    Colon,
    ColonColon,
    Comma,
    Dot,
    Semicolon,
    FatArrow,
    HashTag,

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

