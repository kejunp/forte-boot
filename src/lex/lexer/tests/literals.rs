// Collection literals: `[]` an array, `{}` with colons a map, without them a
// set, and `#` glued to either making it hashed. What makes these the lexer's
// problem is that the same braces hold statements where a statement could
// stand.

use super::*;

// `[...]` is an array, `{...}` with colons a map, `{...}` without a set, and a
// glued `#` makes either one hashed. All of them are values: their entries are
// separated by written commas, and their `}` closes a value rather than a
// statement.
#[test]
fn lexes_collection_literals() {
    assert_eq!(
        lex_types("let a = [1, 2]\nlet s = {1, 2}\nlet m = {1: 2}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("a".to_string()),
            TokType::Equals,
            TokType::LBracket,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Colon,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Entries, so a newline inside one inserts nothing — as in a struct literal
    // — and the `}` closes a value, so the chain below still continues the line.
    assert_eq!(
        lex_types("let m = {\n    \"a\": 1,\n    \"b\": 2,\n}\n.len()\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::StringLiteral("a".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::StringLiteral("b".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2, None),
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Dot,
            TokType::Identifier("len".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // A `#` glued to the brace says hashed, and settles the kind on its own —
    // `#{}` needs no lookahead to be a literal.
    assert_eq!(
        lex_types("let h = #{}\n.len()\n"),
        vec![
            TokType::Let,
            TokType::Identifier("h".to_string()),
            TokType::Equals,
            TokType::HashTag,
            TokType::LCurlyValue,
            TokType::RCurlyBracket,
            TokType::Dot,
            TokType::Identifier("len".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // A block nested in an entry is a statement body again.
    assert_eq!(
        lex_types("let m = {\n    1: {\n        f()\n        g()\n    },\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Colon,
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // Inserted: the value's brace holds statements.
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// `{}` and `{ x }` hold neither separator, so the position decides: a value is
// wanted after an `=`, and a block is what stands at the start of a statement.
#[test]
fn empty_and_singleton_braces_follow_the_position() {
    // After an `=`, `{}` is the empty map and `{ x }` a set of one: both close a
    // value, so the chain on the next line continues it.
    for src in ["let m = {}\n.len()\n", "let s = {x}\n.len()\n"] {
        let toks = lex_types(src);
        assert_eq!(
            toks.last(),
            Some(&TokType::Semicolon),
            "expected one trailing separator in {:?}",
            src
        );
        assert_eq!(
            toks.iter().filter(|t| **t == TokType::Semicolon).count(),
            1,
            "a literal's `}}` must not end the line in {:?}",
            src
        );
    }
    // The empty set, and the empty map said out loud — the spelling that works
    // in a position where a bare `{}` would be a block.
    assert_eq!(
        lex_types("let s = {,}\n.len()\n")
            .iter()
            .filter(|t| **t == TokType::Semicolon)
            .count(),
        1
    );
    assert_eq!(
        lex_types("let m = {:}\n.len()\n")
            .iter()
            .filter(|t| **t == TokType::Semicolon)
            .count(),
        1
    );
    // At the start of a statement the same braces are a block, so the newlines
    // inside them end statements.
    assert_eq!(
        lex_types("{\n    f()\n    g()\n}\n"),
        vec![
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}
