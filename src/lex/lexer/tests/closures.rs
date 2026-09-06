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

// ---- What the `{` after the parameters opens ---------------------------------

// A closure's body written in braces is a block, and it is the one place where
// "in the middle of an expression" and "a statement could stand here" are both
// true. `{}` and `{ x }` are decided by where they stand (§7), and where they
// stand here is the body of a closure.
//
// This was the reading the other way round, and what it cost was the commonest
// way to write a closure: `|d: i64| { n = n + d }` is a block whose value is an
// assignment, and reading it as a set of one thing made it `no type is called
// Set` instead.
#[test]
fn a_brace_after_the_parameters_opens_a_block() {
    // The three shapes `scan_brace_body` cannot decide from the inside: empty,
    // one value, and one statement that is not a value.
    assert_eq!(lex_types("let f = |x: i32| { }")[8], TokType::LCurlyBracket);
    assert_eq!(lex_types("let f = |x: i32| { x }")[8], TokType::LCurlyBracket);
    assert_eq!(lex_types("let f = |d: i32| { n = n + d }")[8], TokType::LCurlyBracket);
    // With no parameters, where the two `|` are the split pair.
    assert_eq!(lex_types("let f = || { n }")[5], TokType::LCurlyBracket);
    assert_eq!(lex_types("let f = move || { n }")[6], TokType::LCurlyBracket);
}

// And what it does not reach: a literal that says so from the inside keeps its
// reading wherever it stands, so the other half of §8's promise -- "the other
// reading always has a spelling" -- is still kept in this position.
#[test]
fn a_literal_after_the_parameters_is_still_a_literal() {
    assert_eq!(lex_types("let f = |x: i32| {x, x}")[8], TokType::LCurlyValue);
    assert_eq!(lex_types("let f = |x: i32| {x: x}")[8], TokType::LCurlyValue);
    assert_eq!(lex_types("let f = |x: i32| {,}")[8], TokType::LCurlyValue);
    assert_eq!(lex_types("let f = |x: i32| {:}")[8], TokType::LCurlyValue);
    // Which is what leaves the set of one a spelling here: the comma it does
    // not need anywhere else.
    assert_eq!(lex_types("let f = |x: i32| {x,}")[8], TokType::LCurlyValue);
}

// The `|` of a disjunction is nobody's parameter list, so the brace after one
// is whatever it would have been. Two of them: one where no closure was ever
// open, and one inside a closure's own body, where the list is closed already.
#[test]
fn a_disjunction_does_not_open_a_parameter_list() {
    assert_eq!(lex_types("let s = a || b")[4], TokType::Or);
    assert_eq!(lex_types("let s = if a || b { x }")[7], TokType::LCurlyBracket);
    // Inside the body, past the closing `|`: the brace is decided as it would
    // be anywhere in the middle of an expression, and here that is a set.
    assert_eq!(lex_types("let f = |x: i32| g(x) + {y}")[13], TokType::LCurlyValue);
}
