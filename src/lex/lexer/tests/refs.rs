// `&`, `*`, `^` and the pairs of them.
//
// Whether an operand stands in front decides every one of these: `&&` is one
// operator where something ends in front of it and two references where
// nothing does.

use super::*;

// A lone `&` is a token now — an immutable reference — and the longer
// operators still win over it.
#[test]
fn lexes_reference_operators() {
    assert_eq!(
        lex_types("let r = &x"),
        vec![
            TokType::Let,
            TokType::Identifier("r".to_string()),
            TokType::Equals,
            TokType::Ampersand,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("a && b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::And,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("a &= b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::AndEquals,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
}

// `&&` is the logical operator only where an operand ends in front of it.
// Where none does it is two prefix `&`, so a reference to a reference can be
// written as one expects.
#[test]
fn splits_a_prefix_ampersand_pair() {
    // Nothing at all in front of it.
    assert_eq!(
        lex_types("&&x"),
        vec![
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
    // A type, after the `:` that annotates one.
    assert_eq!(
        lex_types("fn f(p: &&i32);"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Identifier("p".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::I32,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // Every operator position: after `=`, `(`, `,`, `return`, another `&`.
    assert_eq!(
        lex_types("let r = &&x"),
        vec![
            TokType::Let,
            TokType::Identifier("r".to_string()),
            TokType::Equals,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("f(&&a, &&b)"),
        vec![
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Identifier("a".to_string()),
            TokType::Comma,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Identifier("b".to_string()),
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("return &&x;"),
        vec![
            TokType::Return,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
    // Taking the first `&` alone is what makes the third and later ones fall
    // out for free.
    assert_eq!(
        lex_types("let r = &&&*x"),
        vec![
            TokType::Let,
            TokType::Identifier("r".to_string()),
            TokType::Equals,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Ampersand,
            TokType::Star,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
}

// `^` needs none of that deciding: nothing is written with a prefix `^`, so a
// single one is always bitwise and a doubled one always logical.
#[test]
fn a_caret_is_never_split() {
    assert_eq!(
        lex_types("a ^ b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::Caret,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("a ^^ b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::Xor,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // Glued on either side, and with no operand in front of it -- the shape
    // that makes `&&` two references and `||` a closure's empty parameters.
    assert_eq!(lex_types("a^^b")[1], TokType::Xor);
    assert_eq!(lex_types("let x = ^^y")[3], TokType::Xor);
    // Three in a row is the doubled one and then a single, as `&&&` is.
    assert_eq!(
        lex_types("a ^^^ b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::Xor,
            TokType::Caret,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // `^=` is a third thing the character spells, and the doubled one still
    // wins: only a single `^` can take the `=`.
    assert_eq!(lex_types("a ^= b")[1], TokType::CaretEquals);
    assert_eq!(lex_types("a ^^= b")[1], TokType::Xor);

    // Neither ends a statement, so a newline after one continues the line...
    assert_eq!(
        lex_types("let m = a ^\n    b\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::Identifier("a".to_string()),
            TokType::Caret,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // ...and neither starts a statement, so a line beginning with one carries
    // the line above it on, as `&` and `|` already did.
    for source in ["let m = a\n    ^ b\n", "let m = a\n    ^^ b\n", "a\n    ^= b\n"] {
        assert_eq!(
            lex_types(source).iter().filter(|t| **t == TokType::Semicolon).count(),
            1,
            "{:?} is one statement",
            source
        );
    }
}

// The widths of the new pair, which is what a diagnostic underlines.
#[test]
fn the_carets_are_as_wide_as_they_are_written() {
    assert_eq!(lex_spans("a ^ b"), vec![(1, 1), (3, 1), (5, 1), (6, 0)]);
    assert_eq!(lex_spans("a ^^ b"), vec![(1, 1), (3, 2), (6, 1), (7, 0)]);
}

// ...and an operand in front of it keeps it whole, wherever that operand ends.
#[test]
fn an_operand_keeps_the_ampersand_pair_whole() {
    for (source, left) in [
        ("a && b", TokType::Identifier("a".to_string())),
        ("f() && b", TokType::RParen),
        ("xs[0] && b", TokType::RBracket),
        ("if c { x } && b", TokType::RCurlyBracket),
        ("1 && b", TokType::IntLiteral(1, None)),
        ("true && b", TokType::True),
        ("self && b", TokType::SelfKw),
    ] {
        let toks = lex_types(source);
        let at = toks.iter().position(|t| *t == left).unwrap();
        assert_eq!(
            toks[at + 1],
            TokType::And,
            "{:?} should keep its `&&` whole",
            source
        );
    }
    // A bound list is the one place a type ends in front of it, and the `>`
    // closing a type argument list ends one too.
    let bounds = lex_types("fn f<T: Show && Clone>(x: T);");
    let show = bounds
        .iter()
        .position(|t| *t == TokType::Identifier("Show".to_string()))
        .unwrap();
    assert_eq!(bounds[show + 1], TokType::And);
    assert_eq!(
        lex_types("let x: Vec<i32> && y"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::I32,
            TokType::GreaterThan,
            TokType::And,
            TokType::Identifier("y".to_string()),
            TokType::Semicolon,
        ]
    );
    // `&=` is untouched, and so is a `&&` inside a brace the lexer looks into.
    assert_eq!(
        lex_types("a &= b"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::AndEquals,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("let s = {a && b}"),
        vec![
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::Identifier("a".to_string()),
            TokType::And,
            TokType::Identifier("b".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// A glob is one token glued out of `::` and `*`, which is what lets it end a
// statement where neither half could.
#[test]
fn a_glob_is_one_token_and_a_space_undoes_it() {
    assert_eq!(
        lex_types("import a::*;"),
        vec![
            TokType::Import,
            TokType::Identifier("a".to_string()),
            TokType::Glob,
            TokType::Semicolon,
        ]
    );
    // A space ends the `::` at itself, as a space ends an attribute at its name.
    assert_eq!(
        lex_types("import a:: *;"),
        vec![
            TokType::Import,
            TokType::Identifier("a".to_string()),
            TokType::ColonColon,
            TokType::Star,
            TokType::Semicolon,
        ]
    );
    // The glob ends the statement, so the newline inserts the `;` nobody wrote.
    assert_eq!(
        lex_types("import a::*\nfn main() {}\n"),
        vec![
            TokType::Import,
            TokType::Identifier("a".to_string()),
            TokType::Glob,
            TokType::Semicolon,
            TokType::Fn,
            TokType::Identifier("main".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A bare `*` still ends nothing: an operand is owed after it.
    assert_eq!(
        lex_types("let x = a *\nb\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::Identifier("a".to_string()),
            TokType::Star,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
}

// `*` is prefix and infix both, and where it stands is the whole of what tells
// a mutable reference from a product.
#[test]
fn star_is_prefix_and_infix() {
    assert_eq!(
        lex_types("let p = a * *b"),
        vec![
            TokType::Let,
            TokType::Identifier("p".to_string()),
            TokType::Equals,
            TokType::Identifier("a".to_string()),
            TokType::Star,
            TokType::Star,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // A reference is transparent, so a write through one is an ordinary
    // assignment — and `*=` is still the one operator.
    assert_eq!(
        lex_types("let m = *x\nm *= 2\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::Star,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
            TokType::Identifier("m".to_string()),
            TokType::StarEquals,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
}
