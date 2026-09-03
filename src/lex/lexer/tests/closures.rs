// Closures: the `|` that opens the parameters, and the `move` in front of it.
// `||` splits into two `|` where no operand precedes it.

use super::*;

// `move` marks a closure that captures by value, and the `||` after it still
// splits into two `|`, since a keyword ends no operand.
#[test]
fn lexes_move_closures() {
    assert_eq!(
        lex_types("let own = move || n + 1"),
        vec![
            TokType::Let,
            TokType::Identifier("own".to_string()),
            TokType::Equals,
            TokType::Move,
            TokType::Pipe,
            TokType::Pipe,
            TokType::Identifier("n".to_string()),
            TokType::Plus,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("let f = move |x: i32| x")[3],
        TokType::Move
    );
    // A whole word only.
    assert_eq!(
        lex_types("moves"),
        vec![TokType::Identifier("moves".to_string()), TokType::Semicolon]
    );
}

// `|` is a token of its own — pattern alternation, and a closure's parameter
// list — split from `||` by whether an operand ends in front of it.
#[test]
fn splits_a_prefix_pipe_pair() {
    assert_eq!(
        lex_types("match n {\n    1 | 2 => small,\n    _ => big,\n}"),
        vec![
            TokType::Match,
            TokType::Identifier("n".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1, None),
            TokType::Pipe,
            TokType::IntLiteral(2, None),
            TokType::FatArrow,
            TokType::Identifier("small".to_string()),
            TokType::Comma,
            TokType::Underscore,
            TokType::FatArrow,
            TokType::Identifier("big".to_string()),
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // An operand in front of it keeps the disjunction whole.
    assert_eq!(
        lex_types("a || b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::Or,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // None in front, so `||` is a closure that takes nothing.
    assert_eq!(
        lex_types("let f = || g()"),
        vec![
            TokType::Let,
            TokType::Identifier("f".to_string()),
            TokType::Equals,
            TokType::Pipe,
            TokType::Pipe,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("xs.map(|x| x * 2)"),
        vec![
            TokType::Identifier("xs".to_string()),
            TokType::Dot,
            TokType::Identifier("map".to_string()),
            TokType::LParen,
            TokType::Pipe,
            TokType::Identifier("x".to_string()),
            TokType::Pipe,
            TokType::Identifier("x".to_string()),
            TokType::Star,
            TokType::IntLiteral(2, None),
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // `|=` is untouched.
    assert_eq!(
        lex_types("a |= b")[1],
        TokType::OrEquals
    );
}
