mod lex;
mod prep;

use lex::lexer::Lexer;
use lex::tokens::TokType;
use prep::comments::strip_comments;
use prep::mangle_prep::prep_mangle;

fn dump(source: &str) {
    println!("source:\n{}\n", source);
    dump_tokens(source);
}

fn dump_tokens(source: &str) {
    let mut lexer = Lexer::new(source);
    loop {
        let tok = lexer.next_token();
        println!("{:>2}:{:<3} {:?}", tok.line, tok.col, tok.toktype);
        if tok.toktype == TokType::EOF {
            break;
        }
    }
    println!();
}

fn dump_strip(source: &str) {
    let stripped = strip_comments(source);
    println!("source:\n{}\n", source);
    println!("stripped:\n{}\n", stripped);

    // Comments are blanked out, not deleted, so line/col stay put.
    dump_tokens(&stripped);
    println!();
}

fn dump_mangle(name: &str) {
    let mangled: String = name.chars().map(prep_mangle).collect();
    println!("mangle: {} -> {}\n", name, mangled);
}

fn main() {
    dump("let x = 25;");

    // Same program with no semicolons at all.
    dump("let x = 25\nlet y = x + 1\n");

    // Line comment: everything after // becomes spaces on the same line.
    dump_strip("let x = 25; // the answer\nlet y = x + 1\n");

    // Block comment: newlines inside it survive so later lines keep their numbers.
    dump_strip("let x = /* a\nmultiline\ncomment */ 25\n");

    // Unterminated block comment runs to end of input.
    dump_strip("let x = 1 /* never closed\n");

    // Generics: the `>>` closing a nested argument list is two tokens.
    dump("let m: Map<str, List<i32>> = empty()\n");

    // ...but a real shift still lexes as one.
    dump("let n = bits >> 2\n");

    dump("trait Show<T> {\n    fn show(this: T): str\n}\n");

    dump("impl Show<i32> for Box {\n    fn show(this: i32): str { return \"box\" }\n}\n");

    dump("let n = c as i64 + 1;");

    dump("for i in 0..10 {}\nfor j in 0..=n {}\n");

    // A struct body separates fields with commas, so that is what a newline
    // inserts — and nothing is inserted before the closing brace.
    dump("struct P {\n    x: i32\n    y: i32\n}\n");

    // The two kinds of body nest: the arm's block ends without a separator,
    // the arm itself with a comma.
    dump("match x {\n    1 => {\n        f()\n    }\n    2 => g()\n}\n");

    dump_mangle("my_var_name");
    dump_mangle("already_ok");
}

#[cfg(test)]
fn lex_types(source: &str) -> Vec<TokType> {
    let mut lexer = Lexer::new(source);
    let mut out = Vec::new();
    loop {
        let tok = lexer.next_token();
        if tok.toktype == TokType::EOF {
            return out;
        }
        out.push(tok.toktype);
    }
}

#[test]
fn lexes_trait_and_cast_keywords() {
    assert_eq!(
        lex_types("trait Show {}"),
        vec![
            TokType::Trait,
            TokType::Identifier("Show".to_string()),
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            // Inserted at end of input, as `}` can end a statement.
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("impl Show for Box {}"),
        vec![
            TokType::Impl,
            TokType::Identifier("Show".to_string()),
            TokType::For,
            TokType::Identifier("Box".to_string()),
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("c as i64"),
        vec![
            TokType::Identifier("c".to_string()),
            TokType::As,
            TokType::I64,
            TokType::Semicolon,
        ]
    );
    // `as` is only a keyword on its own; it still prefixes identifiers.
    assert_eq!(
        lex_types("assert"),
        vec![TokType::Identifier("assert".to_string()), TokType::Semicolon]
    );
}

/// A struct, enum or match body separates entries with commas, so that is what
/// a newline inside one inserts.
#[test]
fn inserts_commas_in_comma_bodies() {
    assert_eq!(
        lex_types("struct P {\n    x: i32\n    y: i32\n}\n"),
        vec![
            TokType::Struct,
            TokType::Identifier("P".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Comma,
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::I32,
            // No separator before `}`: the brace closes the last field itself.
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("enum E {\n    A\n    B(i32)\n}\n"),
        vec![
            TokType::Enum,
            TokType::Identifier("E".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("A".to_string()),
            TokType::Comma,
            TokType::Identifier("B".to_string()),
            TokType::LParen,
            TokType::I32,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A written comma already ends the entry, so nothing is inserted after it.
    assert_eq!(
        lex_types("struct P {\n    x: i32,\n    y: i32,\n}\n"),
        vec![
            TokType::Struct,
            TokType::Identifier("P".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Comma,
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

/// The body of a match arm is a block of statements, so the two kinds of body
/// nest: the arm's `}` is followed by a comma, the statement inside it is not.
#[test]
fn brace_kinds_nest() {
    assert_eq!(
        lex_types("match x {\n    1 => {\n        f()\n    }\n    2 => g()\n}\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // Statement body: nothing before the `}` that closes it.
            TokType::RCurlyBracket,
            // Back in the match body, so the arm is closed by a comma.
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::FatArrow,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

/// A function body holds statements, even though its declaration may sit inside
/// a trait or impl, and semicolons still end them.
#[test]
fn fn_body_stays_a_statement_body() {
    assert_eq!(
        lex_types("fn f() {\n    let x = 1\n    g(x)\n}\n"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::LCurlyBracket,
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1),
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A trait body holds signatures, which are statements too.
    assert_eq!(
        lex_types("trait Show {\n    fn show(this): str\n    fn id(this): i32\n}\n"),
        vec![
            TokType::Trait,
            TokType::Identifier("Show".to_string()),
            TokType::LCurlyBracket,
            TokType::Fn,
            TokType::Identifier("show".to_string()),
            TokType::LParen,
            TokType::This,
            TokType::RParen,
            TokType::Colon,
            TokType::Str,
            TokType::Semicolon,
            TokType::Fn,
            TokType::Identifier("id".to_string()),
            TokType::LParen,
            TokType::This,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

/// The float types are keywords, and like the other primitives they can end a
/// declaration — so a newline after one inserts a semicolon.
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

/// The `>>` closing nested generics must split, while a real shift must not.
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
            TokType::IntLiteral(2),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("bits >>= 2"),
        vec![
            TokType::Identifier("bits".to_string()),
            TokType::RShiftEquals,
            TokType::IntLiteral(2),
            TokType::Semicolon,
        ]
    );
}

/// A `<` that turns out to be a comparison must not leave a generic context
/// open, or the next `>>` would wrongly split.
#[test]
fn comparison_does_not_open_generics() {
    // A literal cannot start a type argument, so the context is abandoned.
    assert_eq!(
        lex_types("a < 1 && b >> c"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::LessThan,
            TokType::IntLiteral(1),
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
            TokType::IntLiteral(2),
            TokType::Semicolon,
        ]
    );
}

/// A generic type closes a declaration, so a newline after `>` ends it.
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
            TokType::IntLiteral(1),
            TokType::Semicolon,
        ]
    );
}

/// Ranges glue straight onto integer literals, so `..` has to win over the
/// number lexer's "junk after a literal" check.
#[test]
fn lexes_range_operators() {
    assert_eq!(
        lex_types("0..10"),
        vec![
            TokType::IntLiteral(0),
            TokType::DotDot,
            TokType::IntLiteral(10),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("0..=10"),
        vec![
            TokType::IntLiteral(0),
            TokType::DotDotEquals,
            TokType::IntLiteral(10),
            TokType::Semicolon,
        ]
    );
    // Hex bounds: the base reader must stop at the dots too.
    assert_eq!(
        lex_types("0x10..0x20"),
        vec![
            TokType::IntLiteral(16),
            TokType::DotDot,
            TokType::IntLiteral(32),
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
            TokType::FloatLiteral(1.5),
            TokType::DotDot,
            TokType::FloatLiteral(2.5),
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
            TokType::IntLiteral(0),
            TokType::DotDot,
            TokType::IntLiteral(10),
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

/// An open range ends a statement; a bounded one ends at its upper bound.
#[test]
fn range_terminates_statement() {
    assert_eq!(
        lex_types("let x = 1..10\nlet y = 2\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1),
            TokType::DotDot,
            TokType::IntLiteral(10),
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::IntLiteral(2),
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
            TokType::IntLiteral(1),
            TokType::DotDot,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::IntLiteral(2),
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
            TokType::IntLiteral(1),
            TokType::DotDot,
            TokType::RBracket,
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

/// Ranges must not cost the diagnostic for a genuinely doubled decimal point.
#[test]
fn still_rejects_doubled_decimal_point() {
    assert!(matches!(lex_types("1.2.3")[0], TokType::Error(_)));
}

/// No statement starts with `as`, so a cast may hang off the previous line.
#[test]
fn cast_continues_across_newline() {
    assert_eq!(
        lex_types("let n = x\n    as i64\n"),
        vec![
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::Identifier("x".to_string()),
            TokType::As,
            TokType::I64,
            TokType::Semicolon,
        ]
    );
}

/// Blanking rather than deleting only pays off if the output lines up with the
/// input character for character.
#[test]
fn strip_preserves_length_and_lines() {
    let cases = [
        "let x = 25; // the answer\nlet y = x + 1\n",
        "let x = /* a\nmultiline\ncomment */ 25\n",
        "let x = 1 /* never closed\n",
        "a /**/ b",
        "a /*/ b",
        "a // c",
        "no comments here\n",
        "/*",
        "//",
    ];
    for src in cases {
        let out = strip_comments(src);
        assert_eq!(
            src.chars().count(),
            out.chars().count(),
            "length changed for {:?} -> {:?}",
            src,
            out
        );
        assert_eq!(
            src.matches('\n').count(),
            out.matches('\n').count(),
            "newline count changed for {:?} -> {:?}",
            src,
            out
        );
    }
}
/// Peeking must leave the scanner exactly where it was: a peek before every
/// `next_token` has to yield the same stream as no peeks at all — line and
/// column included — even where lexing depends on scanner state, as semicolon
/// insertion and `>>` splitting do.
#[test]
fn peek_does_not_consume() {
    let sources = [
        "let x = 25\nlet y = x + 1\n",
        "let m: Map<str, List<i32>> = empty()\n",
        "let n = bits >> 2\n",
        "for i in 0..10 {}\n",
        // Brace kinds are scanner state too, so they must roll back as well.
        "struct P {\n    x: i32\n    y: i32\n}\n",
        "match x {\n    1 => {\n        f()\n    }\n    2 => g()\n}\n",
    ];
    for src in sources {
        let mut lexer = Lexer::new(src);
        for expected in lex_types(src) {
            let peeked = lexer.peek();
            assert_eq!(peeked, lexer.peek(), "second peek differed in {:?}", src);
            assert_eq!(peeked, lexer.next_token(), "peek differed from next in {:?}", src);
            assert_eq!(peeked.toktype, expected);
        }
        assert_eq!(lexer.peek().toktype, TokType::EOF);
        assert_eq!(lexer.next_token().toktype, TokType::EOF);
    }
}

/// Every open form: from, to, to-inclusive, and full.
#[test]
fn lexes_open_ranges() {
    let range_only = |src| {
        let mut toks = lex_types(src);
        toks.pop(); // trailing inserted semicolon
        toks.drain(..3); // `let _ =`
        toks
    };
    assert_eq!(range_only("let a = 1.."), vec![TokType::IntLiteral(1), TokType::DotDot]);
    assert_eq!(range_only("let b = ..10"), vec![TokType::DotDot, TokType::IntLiteral(10)]);
    assert_eq!(
        range_only("let c = ..=10"),
        vec![TokType::DotDotEquals, TokType::IntLiteral(10)]
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
