// A `<` that opens a type argument list, and the `>>` that closes two of them.
//
// The scanner keeps a context open from the `<` it decided was generic, and
// what these hold it to is that the context closes again -- a comparison must
// not leave one open, or the next `>>` splits where a shift was written.

use super::*;

// A call's type arguments hold commas of their own, and a comma is also what
// tells a collection literal's `{` from a block's (section 7). The one must not
// be read as the other: `fn f(): i32 { id<i32, str>(1) }` is a block holding a
// call, and nothing about it is a map.
#[test]
fn a_type_argument_list_holds_its_own_commas() {
    assert_eq!(
        lex_types("fn f(): i32 { id<i32, str>(1) }\n"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            // A block, and not the value `{` a top-level comma would make it.
            TokType::LCurlyBracket,
            TokType::Identifier("id".to_string()),
            TokType::LessGeneric,
            TokType::I32,
            TokType::Comma,
            TokType::Str,
            TokType::GreaterThan,
            TokType::LParen,
            TokType::IntLiteral(1, None),
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A comma that really is between entries still says so, and a comparison
    // still opens nothing: `a < b` and `c > d` are two of them.
    assert_eq!(lex_types("let m = {1: 2, 3: 4}\n")[3], TokType::LCurlyValue);
    assert_eq!(lex_types("let s = {a < b, c > d}\n")[3], TokType::LCurlyValue);
    // And a nested list closes on a `>>` without leaving one open.
    assert_eq!(
        lex_types("fn f(): i32 { m<Map<i32, str>, u8>(1) }\n")[6],
        TokType::LCurlyBracket
    );
}

// The `>>` closing nested generics must split, while a real shift must not.
#[test]
fn splits_nested_generic_close() {
    assert_eq!(
        lex_types("Map<str, List<i32>>"),
        vec![
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Identifier("List".to_string()),
            TokType::LessThan,
            TokType::I32,
            TokType::GreaterThan,
            TokType::GreaterThan,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("bits >> 2"),
        vec![
            TokType::Identifier("bits".to_string()),
            TokType::RShift,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("bits >>= 2"),
        vec![
            TokType::Identifier("bits".to_string()),
            TokType::RShiftEquals,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
}

// A `<` that turns out to be a comparison must not leave a generic context
// open, or the next `>>` would wrongly split.
#[test]
fn comparison_does_not_open_generics() {
    // A literal may appear in a type argument (an array size), so it is the
    // `&&` that abandons the context here.
    assert_eq!(
        lex_types("a < 1 && b >> c"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::LessThan,
            TokType::IntLiteral(1, None),
            TokType::And,
            TokType::Identifier("b".to_string()),
            TokType::RShift,
            TokType::Identifier("c".to_string()),
            TokType::Semicolon,
        ]
    );
    // Nor can a `<` after anything but a name open one.
    assert_eq!(
        lex_types("f() < 2"),
        vec![
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::LessThan,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
        ]
    );
}

// A generic type closes a declaration, so a newline after `>` ends it.
#[test]
fn generic_close_ends_statement() {
    assert_eq!(
        lex_types("let v: Vec<i32>\nlet w = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
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
}

// A root is a word, so a type argument list holding one has to survive it.
#[test]
fn a_root_keeps_a_generic_context_open() {
    let toks = lex_types("let m: Map<str, List<super::Node>> = empty()\n");
    // The `>>` splits, which is what says the context was still open.
    let closes = toks.iter().filter(|t| **t == TokType::GreaterThan).count();
    assert_eq!(closes, 2, "{:?}", toks);
}

// A signature may carry `const`, its own generic parameters and a `where`
// clause, and the clause may start on a line of its own.
#[test]
fn lexes_const_fn_impl_generics_and_where() {
    assert_eq!(
        lex_types("const fn square(n: i32): i32 { n * n }"),
        vec![
            TokType::Const,
            TokType::Fn,
            TokType::Identifier("square".to_string()),
            TokType::LParen,
            TokType::Identifier("n".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            TokType::LCurlyBracket,
            TokType::Identifier("n".to_string()),
            TokType::Star,
            TokType::Identifier("n".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // `impl<T>` opens a generic context, so the `>>` of `Stack<Vec<T>>` splits.
    assert_eq!(
        lex_types("impl<T> Stack<Vec<T>> {}"),
        vec![
            TokType::Impl,
            TokType::LessThan,
            TokType::Identifier("T".to_string()),
            TokType::GreaterThan,
            TokType::Identifier("Stack".to_string()),
            TokType::LessThan,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Identifier("T".to_string()),
            TokType::GreaterThan,
            TokType::GreaterThan,
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // `where` continues the line above it, and `+` joins two bounds.
    assert_eq!(
        lex_types("fn sort<T>(xs: *T[])\n    where T: Ord + Show {\n    f()\n}"),
        vec![
            TokType::Fn,
            TokType::Identifier("sort".to_string()),
            TokType::LessThan,
            TokType::Identifier("T".to_string()),
            TokType::GreaterThan,
            TokType::LParen,
            TokType::Identifier("xs".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::Identifier("T".to_string()),
            TokType::LBracket,
            TokType::RBracket,
            TokType::RParen,
            TokType::Where,
            TokType::Identifier("T".to_string()),
            TokType::Colon,
            TokType::Identifier("Ord".to_string()),
            TokType::Plus,
            TokType::Identifier("Show".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // Nothing before the `}`, so `f()` is the block's trailing value.
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // An inferred type argument no longer abandons the generic context.
    assert_eq!(
        lex_types("let v: Vec<_>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Underscore,
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
