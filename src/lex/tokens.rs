pub enum TokType {
    // Types
    Int,
    Float,
    Bool,
    String,
    Char,
    Void,
    List,
    Dict,

    // Declarations
    Func,
    Let,
    Var,
    Struct,
    Impl,
    Import,
    Asm,
    Print,
    Enum,

    // Control flow
    If,
    Elif,
    Else,
    While,
    For,
    Return,
    Break,
    Continue,
    Match,

    // Block delimiters
    Start,
    End,

    // Literals
    True,
    False,
    This,
    Null,

    // Literal values
    Identifier(String),
    Number(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    CharLiteral(char),

    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,

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

    // Assignment
    Equals,
    PlusEquals,
    MinusEquals,
    StarEquals,
    SlashEquals,

    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Comma,
    Dot,
    Arrow,
    Semicolon,
    FatArrow,

    // Special
    EOF,
    Error(String),
}

pub struct Tok {
    pub line:    usize,
    pub col:     usize,
    pub toktype: TokType,
}

