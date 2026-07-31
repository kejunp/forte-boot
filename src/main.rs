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

    // A struct body holds entries, and their commas are the writer's: a newline
    // inside one inserts nothing at all.
    dump("struct P {\n    x: i32,\n    y: i32,\n}\n");

    // A struct literal is entries too, and its `}` closes a value, so the
    // `.norm()` below still continues the line.
    dump("let p = Point {\n    x: 1,\n    y: 2,\n}\n.norm()\n");

    // The two kinds of body nest: inside the arm's block a newline ends a
    // statement, while the comma ending the arm itself is written.
    dump("match x {\n    1 => {\n        f()\n        g()\n    },\n    2 => h()\n}\n");

    // `[]` is an array, `{}` with colons a map, `{}` without a set, and `#`
    // glued to either makes it hashed.
    dump("let a = [1, 2, 3]\nlet m = {1: 2, 3: 4}\nlet s = {1, 2, 3}\nlet h = #{1: 2}\n");

    // The empty map is `{}` and the empty set `{,}`; a one-element set needs no
    // trailing comma. All of them close a value, so the chain continues.
    dump("let m = {}\nlet s = {,}\nlet one = {x}\n.len()\n");

    // The same braces hold statements where a statement could stand, and the
    // separators come back with them.
    dump("let v = {\n    f()\n    g()\n}\n{\n    h()\n    k()\n}\n");

    // `::` reaches into a type, `.` into a value or a module.
    dump("let c = shapes.Color::Red\n");

    // A `}` ends the line it sits on, so the `-1` is a statement of its own —
    // and `->` is how to say it was not.
    dump("match x {\n    1 => a\n}\n-1\n");

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

/// A struct, enum or match body holds entries, and the commas between them are
/// the writer's. A newline inside one inserts nothing, exactly as inside a
/// `(...)`; the `;` of a statement is the only separator the lexer synthesises.
#[test]
fn entry_bodies_insert_nothing() {
    assert_eq!(
        lex_types("struct P {\n    x: i32\n    y: i32\n}\n"),
        vec![
            TokType::Struct,
            TokType::Identifier("P".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::I32,
            // Nothing here: the comma the writer left out stays left out.
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::RCurlyBracket,
            // Outside the body again, where a newline does end a statement.
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
            TokType::Identifier("B".to_string()),
            TokType::LParen,
            TokType::I32,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Written out, the commas are simply the tokens they always were.
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
/// nest: inside the arm's block a newline ends a statement, while in the match
/// body around it a newline does nothing and the arm's comma is written.
#[test]
fn brace_kinds_nest() {
    assert_eq!(
        lex_types("match x {\n    1 => {\n        f()\n        g()\n    },\n    2 => h()\n}\n"),
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
            // A statement body, so this newline inserts a semicolon...
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            // ...and nothing before the `}` that closes it.
            TokType::RCurlyBracket,
            // Back in the match body: the comma ending the arm is written.
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::FatArrow,
            TokType::Identifier("h".to_string()),
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
        // Brace kinds are scanner state too, so they must roll back as well —
        // including a pending header, and a literal's brace inside one.
        "struct P {\n    x: i32\n    y: i32\n}\n",
        "match x {\n    1 => {\n        f()\n    }\n    2 => g()\n}\n",
        "let p = Point {\n    x: 1\n    y: 2\n}\n",
        "if (Cfg { on: true }).on {\n    f()\n}\n",
        // A collection literal's brace is decided by a lookahead, which is the
        // scanner run and rewound — so a peek around one nests two of them.
        "let m = {\n    1: {\n        f()\n        g()\n    },\n}\n",
        "let s = #{1, 2}\nlet b = {\n    f()\n    g()\n}\n",
        "for x in {1, 2} {\n    f(x)\n    g(x)\n}\n",
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

/// if, while, for and match are expressions, so the separator rules have to
/// leave a control-flow form usable as a value: no semicolon before the `else`
/// that continues it, none before the `}` that makes it a block's trailing
/// expression, and one after it when the next line starts a new statement.
#[test]
fn control_flow_lexes_as_an_expression() {
    // Bound to a name: `else` continues the line, and the closing `}` ends the
    // statement because a real one follows.
    assert_eq!(
        lex_types("let x = if c {\n    1\n} else {\n    2\n}\nlet y = x\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::If,
            TokType::Identifier("c".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            // Nothing before the `}`, so the `1` is the block's value.
            TokType::RCurlyBracket,
            TokType::Else,
            TokType::LCurlyBracket,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::Identifier("x".to_string()),
            TokType::Semicolon,
        ]
    );
    // As the trailing expression of a function body: the match `}` is followed
    // by the body's `}`, so it takes no separator at all.
    assert_eq!(
        lex_types("fn f(): i32 {\n    match x {\n        1 => 2,\n        _ => 3,\n    }\n}\n"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            TokType::LCurlyBracket,
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::IntLiteral(2),
            TokType::Comma,
            TokType::Identifier("_".to_string()),
            TokType::FatArrow,
            TokType::IntLiteral(3),
            TokType::Comma,
            // Two closers in a row, and no separator before either.
            TokType::RCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Used for its effect, the same form is an expression statement, and the
    // newline after its `}` supplies the semicolon.
    assert_eq!(
        lex_types("while c {\n    f()\n}\ng()\n"),
        vec![
            TokType::While,
            TokType::Identifier("c".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

/// A `break` may carry the loop's value, but only on its own line: `break` can
/// end a statement, so a newline after it inserts the semicolon and whatever
/// follows is a statement of its own — the same treatment `return` gets.
#[test]
fn break_carries_a_value_on_its_own_line() {
    assert_eq!(
        lex_types("while true {\n    break 1\n}\n"),
        vec![
            TokType::While,
            TokType::True,
            TokType::LCurlyBracket,
            TokType::Break,
            TokType::IntLiteral(1),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("break\nf()\n"),
        vec![
            TokType::Break,
            // Inserted: the `f()` below is not the break's value.
            TokType::Semicolon,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

/// `::` reaches into a type, `:` annotates one, and `.` reaches into a value or
/// a module. All three can meet in one line.
#[test]
fn lexes_path_separator() {
    assert_eq!(
        lex_types("let c: Color = Color::Red"),
        vec![
            TokType::Let,
            TokType::Identifier("c".to_string()),
            TokType::Colon,
            TokType::Identifier("Color".to_string()),
            TokType::Equals,
            TokType::Identifier("Color".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Red".to_string()),
            TokType::Semicolon,
        ]
    );
    // Through a module, into the type, then into the value it produces.
    assert_eq!(
        lex_types("shapes.Color::Red.name"),
        vec![
            TokType::Identifier("shapes".to_string()),
            TokType::Dot,
            TokType::Identifier("Color".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Red".to_string()),
            TokType::Dot,
            TokType::Identifier("name".to_string()),
            TokType::Semicolon,
        ]
    );
    // A trait bound is still one colon, and `<T: Show>` still closes cleanly.
    assert_eq!(
        lex_types("fn f<T: Show>()"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LessThan,
            TokType::Identifier("T".to_string()),
            TokType::Colon,
            TokType::Identifier("Show".to_string()),
            TokType::GreaterThan,
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

/// A `{` opens one of three things, and the lexer has to know which: a header's
/// body, a struct literal, or a block. A header claims the first `{` at its own
/// bracket depth — which is sound because the grammar bans a struct literal from
/// the top level of a header — and a `{` straight after a type name anywhere
/// else is a literal.
#[test]
fn struct_literal_is_not_a_block() {
    // A literal is a value, so nothing is inserted inside it: the commas
    // between its fields are the writer's, exactly as in a call's arguments.
    assert_eq!(
        lex_types("let p = Point {\n    x: 1,\n    y: 2,\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("p".to_string()),
            TokType::Equals,
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2),
            TokType::Comma,
            TokType::RCurlyBracket,
            // Outside the literal again, so the statement ends as usual.
            TokType::Semicolon,
        ]
    );
    // Leave one out and it stays out — no separator appears between `1` and `y`.
    assert_eq!(
        lex_types("Point {\n    x: 1\n    y: 2\n}"),
        vec![
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1),
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A block inside a field's value is a body again, so its statements do get
    // separators — the suppression is the innermost brace's, not the outermost.
    assert_eq!(
        lex_types("Point {\n    x: if c {\n        f()\n        g()\n    } else { 2 },\n}"),
        vec![
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::If,
            TokType::Identifier("c".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // Inserted: inside the block, a newline still ends a statement.
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Else,
            TokType::LCurlyBracket,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // And its `}` closes a value, so a chained call on the next line still
    // continues the line — no `->` needed.
    assert_eq!(
        lex_types("let n = Point { x: 1 }\n    .norm()\n"),
        vec![
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1),
            TokType::RCurlyBracket,
            TokType::Dot,
            TokType::Identifier("norm".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // The hard case: a condition that is a bare name looks exactly like the
    // head of a struct literal. The `if` owns the brace, so it is a block.
    assert_eq!(
        lex_types("if ready {\n    f()\n    g()\n}\n"),
        vec![
            TokType::If,
            TokType::Identifier("ready".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // A statement body, so this is a semicolon and not a comma.
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A header only owns a `{` at its own bracket depth, so a literal nested in
    // one is still a literal.
    assert_eq!(
        lex_types("if (Cfg { on: true }).on {\n    f()\n}\n"),
        vec![
            TokType::If,
            TokType::LParen,
            TokType::Identifier("Cfg".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("on".to_string()),
            TokType::Colon,
            TokType::True,
            TokType::RCurlyBracket,
            TokType::RParen,
            TokType::Dot,
            TokType::Identifier("on".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A signature with no body gets no separator before the `}` of the trait
    // around it, so its header has to be closed by that `}` — or it would still
    // be waiting when the literal below turned up, and swallow its brace.
    assert_eq!(
        lex_types("trait S {\n    fn show(this): str\n}\nlet p = Point {\n    x: 1\n    y: 2\n}\n"),
        vec![
            TokType::Trait,
            TokType::Identifier("S".to_string()),
            TokType::LCurlyBracket,
            TokType::Fn,
            TokType::Identifier("show".to_string()),
            TokType::LParen,
            TokType::This,
            TokType::RParen,
            TokType::Colon,
            TokType::Str,
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("p".to_string()),
            TokType::Equals,
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyBracket,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1),
            // Still a literal, so still no separator between the fields. Had
            // the stale header swallowed this brace, it would be a block and a
            // `;` would appear here.
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

/// A *block's* `}` at the end of a line ends the statement, even when the next
/// line opens with an operator that could have continued it. Any other closer
/// still lets one through, so a method chain hanging off `)` keeps working.
#[test]
fn close_brace_ends_the_line() {
    assert_eq!(
        lex_types("match x {\n    1 => a\n}\n-1\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            // The match is a statement; the `-1` below is its own.
            TokType::Semicolon,
            TokType::Minus,
            TokType::IntLiteral(1),
            TokType::Semicolon,
        ]
    );
    // `->` splices them back together for the case that wanted an operand.
    assert_eq!(
        lex_types("match x {\n    1 => a\n} ->\n-1\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            TokType::Minus,
            TokType::IntLiteral(1),
            TokType::Semicolon,
        ]
    );
    // A `)` is not a `}`: a chained call still hangs off the line above.
    assert_eq!(
        lex_types("f()\n.g()\n"),
        vec![
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Dot,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // Keywords still continue: `else` after the `}` of a branch, `as` after a
    // block being cast.
    assert_eq!(
        lex_types("if c {\n    1\n}\nelse {\n    2\n}\n"),
        vec![
            TokType::If,
            TokType::Identifier("c".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::RCurlyBracket,
            TokType::Else,
            TokType::LCurlyBracket,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // And a leading comma still separates entries rather than being separated
    // from: `,` punctuates, it does not operate.
    assert_eq!(
        lex_types("match x {\n    1 => { a }\n    , 2 => b\n}\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::LCurlyBracket,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::FatArrow,
            TokType::Identifier("b".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

/// `[...]` is an array, `{...}` with colons a map, `{...}` without a set, and a
/// glued `#` makes either one hashed. All of them are values: their entries are
/// separated by written commas, and their `}` closes a value rather than a
/// statement.
#[test]
fn lexes_collection_literals() {
    assert_eq!(
        lex_types("let a = [1, 2]\nlet s = {1, 2}\nlet m = {1: 2}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("a".to_string()),
            TokType::Equals,
            TokType::LBracket,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::Colon,
            TokType::IntLiteral(2),
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
            TokType::LCurlyBracket,
            TokType::StringLiteral("a".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::StringLiteral("b".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2),
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
            TokType::LCurlyBracket,
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
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
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

/// `{}` and `{ x }` hold neither separator, so the position decides: a value is
/// wanted after an `=`, and a block is what stands at the start of a statement.
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

/// A struct literal may not stand at the top level of a header, which is what
/// lets a header claim the `{` in front of it. A collection literal may, so a
/// header gives up a brace that can only be one — and keeps waiting for the
/// body, which is the next brace at its own depth.
#[test]
fn header_gives_up_a_literal_brace() {
    assert_eq!(
        lex_types("for x in {1, 2} {\n    f(x)\n    g(x)\n}\n"),
        vec![
            TokType::For,
            TokType::Identifier("x".to_string()),
            TokType::In,
            // The iterable, not the body: nothing is inserted between its
            // elements, and the comma between them is written.
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            // The body, still claimed by the `for`, and a statement body.
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A `#` says as much on its own, and nesting does not confuse the header:
    // the body is the next brace at the header's *brace* depth, not just its
    // bracket depth.
    assert_eq!(
        lex_types("for x in #{{1, 2}, {3}} {\n    f(x)\n    g(x)\n}\n"),
        vec![
            TokType::For,
            TokType::Identifier("x".to_string()),
            TokType::In,
            TokType::HashTag,
            TokType::LCurlyBracket,
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::LCurlyBracket,
            TokType::IntLiteral(3),
            TokType::RCurlyBracket,
            TokType::RCurlyBracket,
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            // Reached the body, so the newline ends a statement again.
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A match body holds entries, whose commas look exactly like a set's, so a
    // match keeps its brace whatever is inside it.
    assert_eq!(
        lex_types("match x {\n    1 => a,\n    2 => b,\n}\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::Comma,
            TokType::IntLiteral(2),
            TokType::FatArrow,
            TokType::Identifier("b".to_string()),
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // And a condition that is a bare name still gives the `if` its body, since
    // a body of statements is what `{ f() ... }` looks like.
    assert_eq!(
        lex_types("if ready {\n    f()\n    g()\n}\n"),
        vec![
            TokType::If,
            TokType::Identifier("ready".to_string()),
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

/// A `;` or a keyword that only a statement can start with settles a brace as a
/// block, wherever it stands.
#[test]
fn statements_still_make_a_block() {
    assert_eq!(
        lex_types("let x = {\n    let a = 1\n    a\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::Let,
            TokType::Identifier("a".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1),
            // A statement body: the `let` inside decided it.
            TokType::Semicolon,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // The separator the writer put in says as much: `{ f(); g() }` is a block
    // even in a position that wants a value.
    assert_eq!(
        lex_types("let x = {\n    f();\n    g()\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
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
    // Only the brace's own level counts: this comma is the call's.
    assert_eq!(
        lex_types("let x = {\n    f(a, b)\n    g()\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Identifier("a".to_string()),
            TokType::Comma,
            TokType::Identifier("b".to_string()),
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
