// Numbers, the words stuck to the end of them, and the ranges glued to the
// front. `..` has to win over the number lexer's "junk after a literal" check,
// and a `.` before a digit is a tuple index rather than a decimal point.

use super::*;

// Ranges glue straight onto integer literals, so `..` has to win over the
// number lexer's "junk after a literal" check.
#[test]
fn lexes_range_operators() {
    assert_eq!(
        lex_types("0..10"),
        vec![
            TokType::IntLiteral(0, None),
            TokType::DotDot,
            TokType::IntLiteral(10, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("0..=10"),
        vec![
            TokType::IntLiteral(0, None),
            TokType::DotDotEquals,
            TokType::IntLiteral(10, None),
            TokType::Semicolon,
        ]
    );
    // Hex bounds: the base reader must stop at the dots too.
    assert_eq!(
        lex_types("0x10..0x20"),
        vec![
            TokType::IntLiteral(16, None),
            TokType::DotDot,
            TokType::IntLiteral(32, None),
            TokType::Semicolon,
        ]
    );
    // A single '.' is still member access, and a float still absorbs its point.
    assert_eq!(
        lex_types("a.b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::Dot,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("1.5..2.5"),
        vec![
            TokType::FloatLiteral(1.5, None),
            TokType::DotDot,
            TokType::FloatLiteral(2.5, None),
            TokType::Semicolon,
        ]
    );
}

#[test]
fn lexes_for_in_header() {
    assert_eq!(
        lex_types("for i in 0..10 {}"),
        vec![
            TokType::For,
            TokType::Identifier("i".to_string()),
            TokType::In,
            TokType::IntLiteral(0, None),
            TokType::DotDot,
            TokType::IntLiteral(10, None),
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // `in` is a keyword on its own only; it still prefixes identifiers.
    assert_eq!(
        lex_types("index"),
        vec![TokType::Identifier("index".to_string()), TokType::Semicolon]
    );
}

// An open range ends a statement; a bounded one ends at its upper bound.
#[test]
fn range_terminates_statement() {
    assert_eq!(
        lex_types("let x = 1..10\nlet y = 2\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::DotDot,
            TokType::IntLiteral(10, None),
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
    // `1..` is a complete expression, so the next line must not glue onto it.
    assert_eq!(
        lex_types("let x = 1..\nlet y = 2\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::DotDot,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
    // A newline inside brackets is still just formatting.
    assert_eq!(
        lex_types("f(a[1..],\n  2)"),
        vec![
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Identifier("a".to_string()),
            TokType::LBracket,
            TokType::IntLiteral(1, None),
            TokType::DotDot,
            TokType::RBracket,
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

// Every open form: from, to, to-inclusive, and full.
#[test]
fn lexes_open_ranges() {
    let range_only = |src| {
        let mut toks = lex_types(src);
        toks.pop(); // trailing inserted semicolon
        toks.drain(..3); // the `let ... =` in front
        toks
    };
    assert_eq!(range_only("let a = 1.."), vec![TokType::IntLiteral(1, None), TokType::DotDot]);
    assert_eq!(range_only("let b = ..10"), vec![TokType::DotDot, TokType::IntLiteral(10, None)]);
    assert_eq!(
        range_only("let c = ..=10"),
        vec![TokType::DotDotEquals, TokType::IntLiteral(10, None)]
    );
    assert_eq!(range_only("let d = .."), vec![TokType::DotDot]);

    // The full range as an index, where no bound is present at all.
    assert_eq!(
        lex_types("s[..]"),
        vec![
            TokType::Identifier("s".to_string()),
            TokType::LBracket,
            TokType::DotDot,
            TokType::RBracket,
            TokType::Semicolon,
        ]
    );
}

// Ranges must not cost the diagnostic for a genuinely doubled decimal point.
#[test]
fn still_rejects_doubled_decimal_point() {
    assert!(matches!(lex_types("1.2.3")[0], TokType::Error(_)));
}

// A number after a `.` is a tuple index, so it is whole however many dots
// follow: `t.0.1` reaches into the tuple in the first member.
#[test]
fn a_dot_before_a_number_makes_it_an_index() {
    assert_eq!(
        lex_types("t.0.1"),
        vec![
            TokType::Identifier("t".to_string()),
            TokType::Dot,
            TokType::IntLiteral(0, None),
            TokType::Dot,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // Anywhere else a float still absorbs its point, the dots of a range
    // being their own token.
    assert_eq!(
        lex_types("let f = 5.0"),
        vec![
            TokType::Let,
            TokType::Identifier("f".to_string()),
            TokType::Equals,
            TokType::FloatLiteral(5.0, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("0..0.5"),
        vec![
            TokType::IntLiteral(0, None),
            TokType::DotDot,
            TokType::FloatLiteral(0.5, None),
            TokType::Semicolon,
        ]
    );
}

// A `_` among digits separates them and is dropped from the value.
#[test]
fn wildcard_separates_digits() {
    assert_eq!(lex_types("1_000_000")[0], TokType::IntLiteral(1_000_000, None));
    assert_eq!(lex_types("0xFF_FF")[0], TokType::IntLiteral(0xFFFF, None));
    assert_eq!(lex_types("0b1010_1010")[0], TokType::IntLiteral(0b1010_1010, None));
    assert_eq!(lex_types("1_0.2_5")[0], TokType::FloatLiteral(10.25, None));
    // Junk that is not a separator is still the malformed literal it was.
    assert!(matches!(lex_types("12abc")[0], TokType::Error(_)));
    assert!(matches!(lex_types("0xFFZZ")[0], TokType::Error(_)));
    // A leading `_` is a word, so it never reaches the number reader.
    assert_eq!(
        lex_types("_1000")[0],
        TokType::Identifier("_1000".to_string())
    );
}

// A number may name its own type: `5_u8`, `2.6_f32`. The `_` is the digit
// separator doing what it always does, so `5u8` says the same thing.
#[test]
fn a_number_may_name_its_type() {
    use crate::lex::tokens::NumSuffix;

    assert_eq!(lex_types("5_u8")[0], TokType::IntLiteral(5, Some(NumSuffix::U8)));
    assert_eq!(lex_types("5u8")[0], TokType::IntLiteral(5, Some(NumSuffix::U8)));
    assert_eq!(lex_types("2.6_f32")[0], TokType::FloatLiteral(2.6, Some(NumSuffix::F32)));
    assert_eq!(
        lex_types("1_000_i128")[0],
        TokType::IntLiteral(1000, Some(NumSuffix::I128))
    );
    // A based literal takes one too, where the suffix is no digit of its base.
    assert_eq!(lex_types("0xFF_u8")[0], TokType::IntLiteral(255, Some(NumSuffix::U8)));
    assert_eq!(
        lex_types("0b1010_i32")[0],
        TokType::IntLiteral(10, Some(NumSuffix::I32))
    );
    // The digits of a based literal are read as greedily as ever, so a suffix
    // spelled in them is not one: `0x1_f32` is the number 0x1f32.
    assert_eq!(lex_types("0x1_f32")[0], TokType::IntLiteral(0x1f32, None));

    // A float suffix on a whole number makes a float of it.
    assert_eq!(lex_types("5_f32")[0], TokType::FloatLiteral(5.0, Some(NumSuffix::F32)));
    assert_eq!(
        lex_types("0b1010_f64")[0],
        TokType::FloatLiteral(10.0, Some(NumSuffix::F64))
    );

    // An integer suffix on a float names a type the value cannot have.
    assert!(matches!(lex_types("2.6_u8")[0], TokType::Error(_)));
    // A word that names no type at all.
    assert!(matches!(lex_types("5_u9")[0], TokType::Error(_)));
    assert!(matches!(lex_types("5_bool")[0], TokType::Error(_)));
    assert!(matches!(lex_types("0xFF_u9")[0], TokType::Error(_)));

    // The suffix ends the number, so what follows reads as it always did.
    assert_eq!(
        lex_types("1_u8..2_u8"),
        vec![
            TokType::IntLiteral(1, Some(NumSuffix::U8)),
            TokType::DotDot,
            TokType::IntLiteral(2, Some(NumSuffix::U8)),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("x + 1_i64"),
        vec![
            TokType::Identifier("x".to_string()),
            TokType::Plus,
            TokType::IntLiteral(1, Some(NumSuffix::I64)),
            TokType::Semicolon,
        ]
    );
    // A tuple index carries none: the number after a `.` is a member's place,
    // and `f32` there would be a field name if it were anything.
    assert_eq!(
        lex_types("t.0.1"),
        vec![
            TokType::Identifier("t".to_string()),
            TokType::Dot,
            TokType::IntLiteral(0, None),
            TokType::Dot,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
}

// The float types are keywords, and like the other primitives they can end a
// declaration — so a newline after one inserts a semicolon.
#[test]
fn lexes_float_types() {
    assert_eq!(
        lex_types("let x: f32\nlet y: f64\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::F32,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::F64,
            TokType::Semicolon,
        ]
    );
    // And they are legal type arguments, so a generic stays open across one.
    assert_eq!(
        lex_types("Vec<Pair<f32>>"),
        vec![
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Identifier("Pair".to_string()),
            TokType::LessThan,
            TokType::F32,
            TokType::GreaterThan,
            TokType::GreaterThan,
            TokType::Semicolon,
        ]
    );
}
