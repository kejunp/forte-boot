// Types as the lexer sees them: array suffixes, views, and the parentheses
// that group one so the other reading finally has a spelling.

use super::*;

// A fixed array and a view are ordinary types: they end a declaration at the
// `]` that closes them, and they stand in a type argument list like any other.
#[test]
fn lexes_array_and_view_types() {
    // `T[8]` owns its eight, and the `]` closes the statement.
    assert_eq!(
        lex_types("let a: i32[8]\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("a".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // A run is held only behind a reference, and the ref op says which kind.
    assert_eq!(
        lex_types("let s: &i32[] = &a\nlet w: *i32[] = *a[1..3]\n"),
        vec![
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::Equals,
            TokType::Ampersand,
            TokType::Identifier("a".to_string()),
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("w".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::Equals,
            TokType::Star,
            TokType::Identifier("a".to_string()),
            TokType::LBracket,
            TokType::IntLiteral(1, None),
            TokType::DotDot,
            TokType::IntLiteral(3, None),
            TokType::RBracket,
            TokType::Semicolon,
        ]
    );
    // Only the first suffix may be `[]`, so a view of rows stacks the two.
    assert_eq!(
        lex_types("fn rows(m: &i32[][3]);"),
        vec![
            TokType::Fn,
            TokType::Identifier("rows".to_string()),
            TokType::LParen,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::LBracket,
            TokType::IntLiteral(3, None),
            TokType::RBracket,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // A view in a type argument keeps the generic context open, so the `>`
    // closes it and ends the declaration.
    assert_eq!(
        lex_types("let m: Map<str, &i32[]>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
}

// Parentheses group a type, which is what gives an array of references a
// spelling. They may stand in a type argument without abandoning the context.
#[test]
fn lexes_grouped_types() {
    assert_eq!(
        lex_types("let xs: (&i32)[8]\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("xs".to_string()),
            TokType::Colon,
            TokType::LParen,
            TokType::Ampersand,
            TokType::I32,
            TokType::RParen,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("let v: Vec<(&i32)[8]>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::LParen,
            TokType::Ampersand,
            TokType::I32,
            TokType::RParen,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
}

// A reference is a type like any other: it heads a parameter, and the lexer
// keeps its generic context open across one.
#[test]
fn lexes_reference_types() {
    assert_eq!(
        lex_types("fn swap(a: &Point, b: *i32);"),
        vec![
            TokType::Fn,
            TokType::Identifier("swap".to_string()),
            TokType::LParen,
            TokType::Identifier("a".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::Identifier("Point".to_string()),
            TokType::Comma,
            TokType::Identifier("b".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::I32,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // The context survives both, so the `>>` is two closers and the `>` ends
    // the declaration.
    assert_eq!(
        lex_types("let m: Map<str, List<*Node>>\nlet v: Vec<&i32>\nlet w = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Identifier("List".to_string()),
            TokType::LessThan,
            TokType::Star,
            TokType::Identifier("Node".to_string()),
            TokType::GreaterThan,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Ampersand,
            TokType::I32,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("w".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // `&&` still cannot stand in a type argument, so a `<` in front of one was
    // a comparison and the `>>` after it is a real shift.
    assert_eq!(
        lex_types("a < b && c >> d"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::LessThan,
            TokType::Identifier("b".to_string()),
            TokType::And,
            TokType::Identifier("c".to_string()),
            TokType::RShift,
            TokType::Identifier("d".to_string()),
            TokType::Semicolon,
        ]
    );
}
