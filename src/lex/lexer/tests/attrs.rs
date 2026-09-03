// `%name` and its arguments, which is a prefix of what it annotates -- so no
// separator is inserted at the end of the list.

use super::*;

// An attribute is a prefix of the declaration it annotates, so no separator is
// inserted at the end of one however many lines the list runs to. `%name` is
// one token: the sigil is spent by the lexer and never reaches the parser.
#[test]
fn lexes_attributes() {
    assert_eq!(
        lex_types("%inline\n%repr(C)\npub fn f();"),
        vec![
            TokType::AttrName("inline".to_string()),
            TokType::AttrName("repr".to_string()),
            TokType::LParen,
            TokType::Identifier("C".to_string()),
            TokType::RParen,
            TokType::Pub,
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // The statement in front of a list still ends: `@` is no continuation.
    assert_eq!(
        lex_types("let x = 1\n%inline\nfn f();"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
            TokType::AttrName("inline".to_string()),
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // Only a declaration follows one, so a brace holding an attribute holds
    // statements — not a set of one.
    assert_eq!(
        lex_types("let v = {\n%inline\nfn f();\n}")[3],
        TokType::LCurlyBracket
    );
    assert_eq!(
        lex_types("let v = {\n%inline\nfn f();\n}")[4],
        TokType::AttrName("inline".to_string())
    );
}

// Each of the five attributes lexes, arguments and all, and none of them ends
// the statement its declaration begins.
#[test]
fn lexes_the_five_attributes() {
    assert_eq!(
        lex_types("%symbol(\"malloc\")\nfn malloc(n: u64): *u8;"),
        vec![
            TokType::AttrName("symbol".to_string()),
            TokType::LParen,
            TokType::StringLiteral("malloc".to_string()),
            TokType::RParen,
            TokType::Fn,
            TokType::Identifier("malloc".to_string()),
            TokType::LParen,
            TokType::Identifier("n".to_string()),
            TokType::Colon,
            TokType::U64,
            TokType::RParen,
            TokType::Colon,
            TokType::Star,
            TokType::U8,
            TokType::Semicolon,
        ]
    );
    // `%noinline` is a word of its own: `never` names the empty type now, so
    // `%inline(never)` would put a keyword where an IDENTIFIER belongs.
    assert_eq!(
        lex_types("%must_use\n%noinline\n%test\nfn f();"),
        vec![
            TokType::AttrName("must_use".to_string()),
            TokType::AttrName("noinline".to_string()),
            TokType::AttrName("test".to_string()),
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // `must_use` is a word with a `_` in it, not the wildcard and a name.
    assert_eq!(
        lex_types("%deprecated(\"use clamp\")\nlet x = 1\n"),
        vec![
            TokType::AttrName("deprecated".to_string()),
            TokType::LParen,
            TokType::StringLiteral("use clamp".to_string()),
            TokType::RParen,
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
}
