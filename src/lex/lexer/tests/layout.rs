// Section 7: where a newline ends a statement, and what a `{` opens.
//
// The largest file here because it is the largest thing the lexer decides. A
// separator is inserted at a newline where a statement could have ended, so
// every one of these is a pair: the source, and the tokens a reader would say
// it came to.

use super::*;

// A struct, enum or match body holds entries, and the commas between them are
// the writer's. A newline inside one inserts nothing, exactly as inside a
// `(...)`; the `;` of a statement is the only separator the lexer synthesises.
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

// The body of a match arm is a block of statements, so the two kinds of body
// nest: inside the arm's block a newline ends a statement, while in the match
// body around it a newline does nothing and the arm's comma is written.
#[test]
fn brace_kinds_nest() {
    assert_eq!(
        lex_types("match x {\n    1 => {\n        f()\n        g()\n    },\n    2 => h()\n}\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1, None),
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
            TokType::IntLiteral(2, None),
            TokType::FatArrow,
            TokType::Identifier("h".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// A function body holds statements, even though its declaration may sit inside
// a trait or impl, and semicolons still end them.
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
            TokType::IntLiteral(1, None),
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
        lex_types("trait Show {\n    fn show(&self): str\n    fn id(&self): i32\n}\n"),
        vec![
            TokType::Trait,
            TokType::Identifier("Show".to_string()),
            TokType::LCurlyBracket,
            TokType::Fn,
            TokType::Identifier("show".to_string()),
            TokType::LParen,
            TokType::Ampersand,
            TokType::SelfKw,
            TokType::RParen,
            TokType::Colon,
            TokType::Str,
            TokType::Semicolon,
            TokType::Fn,
            TokType::Identifier("id".to_string()),
            TokType::LParen,
            TokType::Ampersand,
            TokType::SelfKw,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// No statement starts with `as`, so a cast may hang off the previous line.
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

// if, while, for and match are expressions, so a control-flow form has to stay
// usable as a value: no semicolon before the `else` that continues it, none
// before the `}` that makes it a trailing expression, one after it otherwise.
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
            TokType::IntLiteral(1, None),
            // Nothing before the `}`, so the `1` is the block's value.
            TokType::RCurlyBracket,
            TokType::Else,
            TokType::LCurlyBracket,
            TokType::IntLiteral(2, None),
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
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::IntLiteral(2, None),
            TokType::Comma,
            TokType::Underscore,
            TokType::FatArrow,
            TokType::IntLiteral(3, None),
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

// A `break` may carry the loop's value, but only on its own line: `break` can
// end a statement, so a newline after it inserts the semicolon and whatever
// follows is a statement of its own — the same treatment `return` gets.
#[test]
fn break_carries_a_value_on_its_own_line() {
    assert_eq!(
        lex_types("while true {\n    break 1\n}\n"),
        vec![
            TokType::While,
            TokType::True,
            TokType::LCurlyBracket,
            TokType::Break,
            TokType::IntLiteral(1, None),
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

// A `{` opens a header's body, a struct literal or a block, and the lexer has to
// know which. A header claims the first `{` at its own bracket depth, which is
// sound because the grammar bans a struct literal from a header's top level; a
// `{` straight after a type name anywhere else is a literal.
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
            TokType::LCurlyValue,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2, None),
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
            TokType::LCurlyValue,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2, None),
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
            TokType::LCurlyValue,
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
            TokType::IntLiteral(2, None),
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
            TokType::LCurlyValue,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
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
            TokType::LCurlyValue,
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
        lex_types("trait S {\n    fn show(&self): str\n}\nlet p = Point {\n    x: 1\n    y: 2\n}\n"),
        vec![
            TokType::Trait,
            TokType::Identifier("S".to_string()),
            TokType::LCurlyBracket,
            TokType::Fn,
            TokType::Identifier("show".to_string()),
            TokType::LParen,
            TokType::Ampersand,
            TokType::SelfKw,
            TokType::RParen,
            TokType::Colon,
            TokType::Str,
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("p".to_string()),
            TokType::Equals,
            TokType::Identifier("Point".to_string()),
            TokType::LCurlyValue,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
            // Still a literal, so still no separator between the fields. Had
            // the stale header swallowed this brace, it would be a block and a
            // `;` would appear here.
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// A *block's* `}` at the end of a line ends the statement, even when the next
// line opens with an operator that could have continued it. Any other closer
// still lets one through, so a method chain hanging off `)` keeps working.
#[test]
fn close_brace_ends_the_line() {
    assert_eq!(
        lex_types("match x {\n    1 => a\n}\n-1\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            // The match is a statement; the `-1` below is its own.
            TokType::Semicolon,
            TokType::Minus,
            TokType::IntLiteral(1, None),
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
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            TokType::Minus,
            TokType::IntLiteral(1, None),
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
            TokType::IntLiteral(1, None),
            TokType::RCurlyBracket,
            TokType::Else,
            TokType::LCurlyBracket,
            TokType::IntLiteral(2, None),
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
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::LCurlyBracket,
            TokType::Identifier("a".to_string()),
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::FatArrow,
            TokType::Identifier("b".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// A struct literal may not stand at the top level of a header, which lets a
// header claim the `{` in front of it. A collection literal may, so a header
// gives up a brace that can only be one and waits for the next at its depth.
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
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::IntLiteral(2, None),
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
            TokType::LCurlyValue,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Comma,
            TokType::LCurlyValue,
            TokType::IntLiteral(3, None),
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
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::Comma,
            TokType::IntLiteral(2, None),
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

// A `;` or a keyword that only a statement can start with settles a brace as a
// block, wherever it stands.
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
            TokType::IntLiteral(1, None),
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

// Nothing but a statement starts with `const`, so a brace holding one holds
// statements — the `:` of the type annotation must not make it a map.
#[test]
fn const_makes_a_brace_a_block() {
    assert_eq!(
        lex_types("let v = {\n    const N: i32 = 2\n    N\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::Const,
            TokType::Identifier("N".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Equals,
            TokType::IntLiteral(2, None),
            TokType::Semicolon,
            TokType::Identifier("N".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// An import's group is a `{` after a `::`, and nothing else is: it holds entries
// and so takes no inserted separators, however many lines it runs to.
#[test]
fn an_import_group_is_a_value_brace() {
    let one = lex_types("import a::{b};");
    assert_eq!(one[3], TokType::LCurlyValue);

    let many = lex_types("import a::{b, c};");
    assert_eq!(many[3], TokType::LCurlyValue);

    // A group over several lines gathers no semicolons, its commas being
    // written; the one after the `}` is the statement's own.
    assert_eq!(
        lex_types("import a::{\n    b,\n    c\n}\n"),
        vec![
            TokType::Import,
            TokType::Identifier("a".to_string()),
            TokType::ColonColon,
            TokType::LCurlyValue,
            TokType::Identifier("b".to_string()),
            TokType::Comma,
            TokType::Identifier("c".to_string()),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// Every loop takes a `break` with a value, and a bare `break` still ends its
// own statement at a line break.
#[test]
fn every_loop_breaks_with_a_value() {
    assert_eq!(
        lex_types("let found = for x in xs {\n    if p(x) { break x }\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("found".to_string()),
            TokType::Equals,
            TokType::For,
            TokType::Identifier("x".to_string()),
            TokType::In,
            TokType::Identifier("xs".to_string()),
            TokType::LCurlyBracket,
            TokType::If,
            TokType::Identifier("p".to_string()),
            TokType::LParen,
            TokType::Identifier("x".to_string()),
            TokType::RParen,
            TokType::LCurlyBracket,
            TokType::Break,
            TokType::Identifier("x".to_string()),
            TokType::RCurlyBracket,
            // Nothing between the two `}` — rule (c) inserts none before one.
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A bare `break` is complete, so the next line starts a statement.
    assert_eq!(
        lex_types("while c {\n    break\n}\n"),
        vec![
            TokType::While,
            TokType::Identifier("c".to_string()),
            TokType::LCurlyBracket,
            TokType::Break,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
}

// `unsafe` heads a body only where a `{` really follows it. That is what keeps
// the one-line form from swallowing the brace of whatever it prefixes, and it
// is the whole of the difference between the two forms.
#[test]
fn unsafe_claims_only_a_brace_that_follows_it() {
    // With a brace: a statement body, so the newlines inside it insert.
    assert_eq!(
        lex_types("unsafe {\n    f()\n    g()\n}\n"),
        vec![
            TokType::Unsafe,
            TokType::LCurlyBracket,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            // A block and not a set: `{ f() ... }` holds statements.
            TokType::Semicolon,
            TokType::Identifier("g".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Without one: the brace below belongs to the literal, so its fields are
    // entries and nothing is inserted between them. A waiting header would have
    // made it a block and put a `;` after the `1`.
    assert_eq!(
        lex_types("unsafe p = P {\n    x: 1\n    y: 2\n}\n"),
        vec![
            TokType::Unsafe,
            TokType::Identifier("p".to_string()),
            TokType::Equals,
            TokType::Identifier("P".to_string()),
            TokType::LCurlyValue,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::IntLiteral(1, None),
            TokType::Identifier("y".to_string()),
            TokType::Colon,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Only a statement starts with `unsafe`, so one inside a brace settles it as
    // a block — the same thing `let` and `return` do.
    assert_eq!(
        lex_types("let v = {\n    unsafe f()\n    g()\n}\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Equals,
            TokType::LCurlyBracket,
            TokType::Unsafe,
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
