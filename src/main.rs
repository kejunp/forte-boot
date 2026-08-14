mod cfg;
mod error;
mod expand;
mod lex;
mod parse;
mod prep;
mod tir;

use lex::lexer::Lexer;
use lex::tokens::TokType;
use error::Source;
use expand::Expander;
use tir::lower::Lowerer;
use parse::parser::Parser;
use prep::preprocess;

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

fn dump_prep(source: &str) {
    let prepped = preprocess(source);
    println!("source:\n{}\n", source);
    println!("preprocessed:\n{}\n", prepped);

    // The pass rewrites in place -- a comment is blanked rather than deleted --
    // so every character keeps its line and column.
    dump_tokens(&prepped);
    println!();
}

// Parses `source` and shows what it had to say about it. A source is held and
// quoted in the same place on purpose: every phase reports a `Span` and none of
// them knows what the text is or what it is called.
//
// The preprocessor is what makes that split necessary. The lexer reads a copy
// with the comments blanked out, and a phase quoting the text it was handed
// would show a reader a line they did not write. Blanking keeps every character
// where it was, so a span from the stripped copy lands in the written one.
//
// A parse that recovers reports more than one thing, and all of them print.
fn dump_parse(path: &str, source: &str) {
    let prepped = preprocess(source);
    debug_assert_eq!(
        source.chars().count(),
        prepped.chars().count(),
        "preprocessing must not move anything"
    );

    let mut parser = Parser::new(Lexer::new(&prepped));
    let root = parser.parse();
    let written: Vec<char> = source.chars().collect();
    if !parser.errors().is_empty() {
        println!("{}\n", parser.errors().render(&Source::new(path, &written)));
        return;
    }

    // Macros are spent before anything else looks at the tree. A parse that
    // failed does not reach here: what expansion would make of a tree the
    // parser recovered through says more about the recovery than the source.
    let mut expander = Expander::new(&mut parser);
    let root = expander.expand(&root);
    if !expander.errors().is_empty() {
        println!("{}\n", expander.errors().render(&Source::new(path, &written)));
        return;
    }

    // The tree the rest of the compiler would read. Lowering is the last pass
    // that cares how any of it was written.
    //
    // It stops here. What comes next is `sema`, which turns this into the
    // typed tree the CFG is built from -- and neither of those is written, so
    // there is nothing yet to hand `cfg::lower` a TTIR to work on.
    let mut lowerer = Lowerer::new(&parser);
    lowerer.lower(&root);
    if !lowerer.errors().is_empty() {
        println!("{}\n", lowerer.errors().render(&Source::new(path, &written)));
        return;
    }
    let tir = lowerer.finish();
    println!(
        "{}: lowered -- {} items, {} expressions, {} types, {} patterns\n",
        path,
        tir.items.len(),
        tir.exprs.len(),
        tir.types.len(),
        tir.pats.len()
    );
}

fn main() {
    dump("let x = 25;");

    // Same program with no semicolons at all.
    dump("let x = 25\nlet y = x + 1\n");

    // Line comment: everything after // becomes spaces on the same line.
    dump_prep("let x = 25; // the answer\nlet y = x + 1\n");

    // Block comment: newlines inside it survive so later lines keep their numbers.
    dump_prep("let x = /* a\nmultiline\ncomment */ 25\n");

    // Unterminated block comment runs to end of input.
    dump_prep("let x = 1 /* never closed\n");

    // Generics: the `>>` closing a nested argument list is two tokens.
    dump("let m: Map<str, List<i32>> = empty()\n");

    // ...but a real shift still lexes as one.
    dump("let n = bits >> 2\n");

    dump("trait Show<T> {\n    fn show(&self): str\n}\n");

    dump("impl Show<i32> for Box {\n    fn show(&self): str { return \"box\" }\n}\n");

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

    // A call may name its type arguments, and no `::` is needed to say so: the
    // lexer looks ahead for the matching `>` and the `(` after it. The second
    // line is the comparison the first would be without that look.
    dump("let a = foo<MyType>(x)\nlet b = a < b && c > d\n");

    // `::` reaches a namespace, a module or a type; `.` reaches a value and
    // nothing else. All three meet in one name here.
    dump("let c = shapes::Color::Red.name\n");

    // A `}` ends the line it sits on, so the `-1` is a statement of its own —
    // and `->` is how to say it was not.
    dump("match x {\n    1 => a\n}\n-1\n");

    // A lone `_` is the wildcard: the match-all pattern, and the name of a
    // binding whose value is deliberately unused. `_foo` is still a name.
    dump("match x {\n    1 => a,\n    _ => b,\n}\nlet _ = f()\nfor _ in 0..3 {}\nlet _foo = 1\n");

    // A constant is worked out at compile time, so it needs both a type and a
    // value. Only a statement starts with `const`, so the brace below is a
    // block and not a map, whatever its `:` looks like.
    dump("pub const MAX: i32 = 1 << 20\nlet v = {\n    const N: i32 = 2\n    N\n}\n");

    // `&` is an immutable reference and `*` a mutable one — neither a pointer,
    // so nothing dereferences them and `a = b` writes through.
    dump("fn swap(a: *i32, b: *i32) {\n    let t = a\n    a = b\n    b = t\n}\n");

    // A reference is a type like any other, and the lexer keeps its generic
    // context open across one, so the `>>` below still splits.
    dump("let v: Vec<&str> = empty()\nlet m: Map<str, List<*Node>> = empty()\n");

    // `&&` is the logical operator where an operand ends in front of it and two
    // references where none does, so a reference to a reference is written as
    // one expects.
    dump("let rr: &&i32 = &&x\nlet ok = a && b\n");

    // `T[8]` is a raw fixed-size array — a value, copied whole — and `T[]` a
    // run of unknown length, which only a reference can hold: `&T[]` reads it
    // and `*T[]` writes to it. A slice is a run, so it is borrowed the same way.
    dump("let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\nlet s: &i32[] = &a\nlet w: *i32[] = *a[1..3]\n");

    // A tuple is two or more types or values in parentheses: positional,
    // declared nowhere, and reached into by number. The comma is what makes
    // one — `(i32)` is an i32 — and a number after a `.` is an index and so a
    // whole one, which is what keeps `p.0.1` two of them rather than a float.
    dump("fn divmod(a: i32, b: i32): (i32, i32) {\n    (a / b, a % b)\n}\n");
    dump("let p: (i32, str) = (1, `one`)\nlet n = p.0\nlet d = q.0.1\n");

    // An attribute is `%name` with its arguments, and a prefix of what it
    // annotates — so no separator is inserted at the end of the list.
    dump("%inline\n%repr(C)\npub fn f();\n");

    // An impl makes methods for a struct; anything else that wants a name in
    // front of it goes in a namespace, reached with a `::` like a module.
    dump("namespace limits {\n    pub const MAX: i32 = 255\n}\nlet n = limits::MAX\n");

    // `null` is a type and its one value, so it is what a loop nobody broke
    // out of yields, and what a function with no return type returns.
    dump("let found = for x in xs {\n    if p(x) { break x }\n}\nfn log(m: str): null;\n");

    // `|` is a token of its own now: pattern alternation and a closure's
    // parameters. `||` splits into two of them where no operand precedes it.
    dump("let f = |x: i32| x * 2\nlet g = || 0\nlet ok = a || b\n");

    // A lifetime is `'a`, one token: `~` spells nothing else, so nothing has
    // to be told apart from the `'a'` of a character literal.
    dump("fn longest<'a>(x: &'a str, y: &'a str): &'a str;\nstruct Parser<'a> {\n    text: &'a str,\n}\n");

    // It stands where a type parameter stands, bounds included, and a `'_` is
    // the one with no name worth giving.
    dump("fn f<'a, 'b: 'a, T: Show + 'a>(x: &'a T) where T: 'a;\nlet p: &'_ i32 = &x\n");

    // A name for a type, generic parameters and all.
    dump("type Pair<T> = (T, T)\ntype Ref<'a> = &'a str\nlet p: Pair<i32> = (1, 2)\n");

    // A macro is declared with a word and invoked with a sigil. `$x` is one
    // token, as `%name` and `'a` are.
    dump("macro twice($x:expr) {\n    $x\n    $x\n}\nlet n = @twice(f())\n");

    // `%` is the remainder operator too, and where it stands tells them apart.
    dump("let r = a % b\n%inline\nfn f();\n");

    // A signature carries `const`, its own generic parameters and a `where`
    // clause, and bounds are joined with `+`.
    dump("const fn square(n: i32): i32 { n * n }\nimpl<T> Stack<T> where T: Ord + Show {\n    fn len(&self): i32;\n}\n");

    // A constant sizes an array, and `_` is both an inferred argument and a
    // digit separator.
    dump("const ROWS: i32 = 8\nlet grid: i32[ROWS][ROWS]\nlet v: Vec<_> = f()\nlet big = 2_147_483_647\n");

    // A number may name its own type, and the `_` in front of the suffix is
    // that same separator: `5u8` says the same thing. A float suffix on a whole
    // number makes a float of it.
    dump("let n = 5_u8\nlet r = 2.6_f32\nlet mask = 0xFF_u8\nlet w = 5_f32\n");

    // A closure captures by `&` where it reads and `*` where it writes; `move`
    // takes a copy instead. The `||` after `move` is still two `|`.
    dump("let show = || print(n)\nlet bump = || n = n + 1\nlet own = move || n + 1\n");

    // Parentheses group a type, so the other reading of a reference and a
    // suffix finally has a spelling.
    dump("let view: &i32[]\nlet refs: (&i32)[8]\n");

    // The five attributes. `%symbol` is the one the mangler makes necessary:
    // nothing outside the language can predict `3add3i323i32`.
    dump("%symbol(\"malloc\")\nfn malloc(n: u64): *u8;\n%must_use\n%noinline\nfn parse(s: str): i32;\n");

    // `never` is the empty type — no values, so an expression of it agrees
    // with anything beside it. `null` is its opposite: one value, no news.
    dump("fn panic(m: str): never;\nlet x = match c {\n    1 => 5,\n    _ => panic(\"no\"),\n}\n");

    // `unsafe` marks a fn whose caller has something to prove, and prefixes the
    // statement that answers for it — a block where there is more than one, and
    // the statement itself where there is not. Only a `{` glued to the word
    // opens a body, so the brace below is still the literal's.
    dump("pub unsafe fn write(dst: *u8[], n: u64);\nunsafe {\n    let buf = malloc(n)\n    fill(buf, n)\n}\nunsafe free(q)\nunsafe p = P { x: 1 }\n");

    // What the parser makes of a source it can take, and of five it cannot.
    // Each mistake is shown against the line it was written on.
    dump_parse("ok.fc", "fn main() {\n    let x = 1  // fine\n    g(x)\n}\n");

    // A comment on the line a mistake is on. The parse never sees it -- it was
    // blanked out before the lexer ran -- and the quoted line has it back.
    dump_parse("note.fc", "fn main() {\n    let x = /* huh */ ;  // why\n}\n");

    // A type is wanted and an `=` is written: the caret sits on the token the
    // tables turned down, and the margin says what was being written.
    dump_parse("annot.fc", "fn main() {\n    let x: = 5\n}\n");

    // A near-miss the language has a rule about, rather than a slip: `;` where
    // the entries of a struct are separated by `,`.
    dump_parse("field.fc", "struct P {\n    x: i32,\n    y: i32;\n}\n");

    // The `}` that gave it away is two lines from the `(` that caused it, so
    // the opener gets a snippet of its own.
    dump_parse("args.fc", "fn main() {\n    f(1, 2\n}\n");

    // A token the lexer gave up inside of: the caret runs to the end of the
    // line, which is as far as the reader can see it.
    dump_parse("string.fc", "fn main() {\n    let s = \"unclosed\n}\n");

    // Another it gave up inside of: a word glued to a number that names no
    // type. The twelve that would have are spelled out, the set being closed.
    dump_parse("suffix.fc", "fn main() {\n    let n = 5_u9\n}\n");

    // One mistake does not hide the next: the parse recovers and goes on, and
    // both are reported against their own lines.
    dump_parse("two.fc", "fn a() { let x = ; }\nfn b() { let y = ; }\n");

    // A macro is spent before anything else sees the tree, and what it says
    // when it cannot be is a diagnostic like any other.
    dump_parse("macro.fc", "macro twice($x:expr) {\n    $x\n    $x\n}\nfn main() {\n    @twice(f());\n}\n");
    dump_parse("nomacro.fc", "fn main() {\n    @nope(1);\n}\n");
    dump_parse("arity.fc", "macro one($x:expr) {\n    $x\n}\nfn main() {\n    @one(1, 2);\n}\n");
    dump_parse("frag.fc", "macro n($x:ident) {\n    $x\n}\nfn main() {\n    @n(1 + 2);\n}\n");

    // An import is a tree of the names it reaches, and lowering flattens it: a
    // group is spelling, and what comes out is one leaf for each name.
    dump_parse(
        "import.fc",
        "pub import shapes::{circle, square::*, poly::{tri, quad}};\n\
         import super::super::helpers::trim as t;\n\
         import suite::limits::MAX;\n\
         pub(suite) fn area(): i32 { suite::limits::MAX }\n\
         impl Buf {\n\
             pub fn len(&self): i32;\n\
             pub fn clear(*self);\n\
             fn into_vec(self): Vec<u8>;\n\
         }\n\
         namespace n { type T = i32 }\n",
    );

    // The closed set of attributes is checked while the CFG is built: a name
    // the compiler does not know is an error naming what was probably meant.
    dump_parse("attr.fc", "%inlien\nfn f();\n");
    dump_parse("target.fc", "%symbol(\"s\")\nstruct P {\n    x: i32,\n}\n");

    // Simplification: the arithmetic folds, the fold settles the branch, the
    // branch leaves one value, and the value lands where the name was.
    dump_parse("opt.fc", "fn main() {\n    let n = if 2 * 3 > 5 { 10 + 1 } else { 0 }\n    g(n);\n    return;\n    h();\n}\n");
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

// Every token's column and width, which is what a diagnostic underlines.
#[cfg(test)]
fn lex_spans(source: &str) -> Vec<(usize, usize)> {
    let mut lexer = Lexer::new(source);
    let mut out = Vec::new();
    loop {
        let tok = lexer.next_token();
        if tok.toktype == TokType::EOF {
            return out;
        }
        out.push((tok.col, tok.len));
    }
}

// A token knows how wide it was written, which its type cannot answer: `0x10`
// and `16` are the same literal, and a string has lost its quotes and escapes.
#[test]
fn a_token_knows_how_wide_it_was_written() {
    // The inserted separator at the end is a place and not a piece: no width.
    assert_eq!(
        lex_spans("let x = 25\n"),
        vec![(1, 3), (5, 1), (7, 1), (9, 2), (11, 0)]
    );
    // Written in a base, and with the separators a reader may put in it.
    assert_eq!(lex_spans("0x10"), vec![(1, 4), (5, 0)]);
    assert_eq!(lex_spans("2_147_483_647"), vec![(1, 13), (14, 0)]);
    // The quotes are the literal's, though its value has none.
    assert_eq!(lex_spans("\"hi\""), vec![(1, 4), (5, 0)]);
    assert_eq!(lex_spans("'\\n'"), vec![(1, 4), (5, 0)]);
    // A `>>` that closes two generic lists is two tokens of one character, not
    // one of two -- the width follows the split.
    assert_eq!(
        lex_spans("Map<str, List<i32>>"),
        vec![
            (1, 3),   // Map
            (4, 1),   // <
            (5, 3),   // str
            (8, 1),   // ,
            (10, 4),  // List
            (14, 1),  // <
            (15, 3),  // i32
            (18, 1),  // the first `>`
            (19, 1),  // the second
            (20, 0),  // the inserted separator
        ]
    );
    // A real shift is still one token, and two characters wide.
    assert_eq!(lex_spans("bits >> 2"), vec![(1, 4), (6, 2), (9, 1), (10, 0)]);
    // A token the lexer gave up inside of covers what it read before it did.
    // An unterminated string runs to the end of the input, so its width counts
    // the newline it ran past; a diagnostic quoting one line stops at the end
    // of that line, which is where a caret can still be seen.
    assert_eq!(lex_spans("let s = \"oops\n"), vec![(1, 3), (5, 1), (7, 1), (9, 6)]);
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

// Blanking rather than deleting only pays off if the output lines up with the
// input character for character, which is what lets a diagnostic quote the
// source as written while the parse runs on the preprocessed copy.
#[test]
fn preprocessing_preserves_length_and_lines() {
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
        "let my_var = 1  // a_b\n",
    ];
    for src in cases {
        let out = preprocess(src);
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
// Peeking must leave the scanner exactly where it was: a peek before every
// `next_token` yields the same stream as no peeks at all, line and column
// included, even where lexing depends on scanner state.
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
        "match x {\n    1 => a,\n    _ => b,\n}\n",
        "let _ = f()\nfor _ in 0..3 {}\n",
        // `unsafe` decides its brace by looking at the character after it, so
        // both readings have to survive a peek.
        "unsafe {\n    f()\n    g()\n}\n",
        "unsafe p = P {\n    x: 1\n    y: 2\n}\n",
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

// `::` reaches into a namespace, a module or a type, `:` annotates one, and `.`
// reaches into a value and nothing else. All three can meet in one line.
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
    // The two separators interleave in any order, and the lexer keeps them
    // apart wherever they meet. This one is no longer a program a checker
    // would take -- a module is reached with `::` now -- but which of them
    // means what is settled above the lexer, and it emits both regardless.
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

// A lone `_` is its own token: the match-all pattern, and the name of a
// binding whose value is deliberately unused.
#[test]
fn lexes_wildcard() {
    // The wildcard arm of a match.
    assert_eq!(
        lex_types("match x {\n    1 => a,\n    _ => b,\n}\n"),
        vec![
            TokType::Match,
            TokType::Identifier("x".to_string()),
            TokType::LCurlyBracket,
            TokType::IntLiteral(1, None),
            TokType::FatArrow,
            TokType::Identifier("a".to_string()),
            TokType::Comma,
            TokType::Underscore,
            TokType::FatArrow,
            TokType::Identifier("b".to_string()),
            TokType::Comma,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // A discarded binding, an unused parameter, and an unused loop variable —
    // every place a name can be bound.
    assert_eq!(
        lex_types("let _ = f()"),
        vec![
            TokType::Let,
            TokType::Underscore,
            TokType::Equals,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("fn f(_: i32) {}"),
        vec![
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::Underscore,
            TokType::Colon,
            TokType::I32,
            TokType::RParen,
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("for _ in 0..3 {}"),
        vec![
            TokType::For,
            TokType::Underscore,
            TokType::In,
            TokType::IntLiteral(0, None),
            TokType::DotDot,
            TokType::IntLiteral(3, None),
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // Repeated in one pattern, which a name could not be: a `_` binds nothing.
    assert_eq!(
        lex_types("Pair::Of(_, _)"),
        vec![
            TokType::Identifier("Pair".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Of".to_string()),
            TokType::LParen,
            TokType::Underscore,
            TokType::Comma,
            TokType::Underscore,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
}

// A name reaches the parser as it was written: nothing rewrites one on the way,
// and an `_` in a name is a character of that name. Both places a rewrite was
// tried are wrong -- over the source text it cannot tell a name from a digit
// separator, and on tokens the declaration is not yet resolved or typed. That
// belongs to codegen, and this test says so if it drifts back.
#[test]
fn a_name_comes_through_as_it_was_written() {
    assert_eq!(
        lex_types("my_var_name"),
        vec![TokType::Identifier("my_var_name".to_string()), TokType::Semicolon]
    );
    // The three a text-level rewrite got wrong, none of which is a name.
    assert_eq!(
        lex_types("2_147_483_647"),
        vec![TokType::IntLiteral(2_147_483_647, None), TokType::Semicolon]
    );
    assert_eq!(
        lex_types("\"a_b\""),
        vec![TokType::StringLiteral("a_b".to_string()), TokType::Semicolon]
    );
    assert_eq!(lex_types("_"), vec![TokType::Underscore, TokType::Semicolon]);
    // A keyword is settled before a name is built, so none is rewritten. No
    // separator follows this one: a `const` cannot end a statement.
    assert_eq!(lex_types("const"), vec![TokType::Const]);
}

// Reserved as a whole word only. An underscore that starts a longer word is
// just a character of that word, exactly as it was before.
#[test]
fn wildcard_is_a_whole_word_only() {
    for word in ["_x", "__", "_1", "_foo_bar", "x_"] {
        assert_eq!(
            lex_types(word),
            vec![TokType::Identifier(word.to_string()), TokType::Semicolon],
            "{:?} should still lex as an identifier",
            word
        );
    }
}

// A `_` names a binding, so it closes a declaration as a name does. Inside a
// type argument list it is an inferred argument, but it names no type of its
// own: it opens no generic context and heads no struct literal.
#[test]
fn wildcard_behaves_like_a_name_but_not_a_type() {
    // `let _` is as complete as `let x`, so the newline ends it.
    assert_eq!(
        lex_types("let _\nlet y = 1\n"),
        vec![
            TokType::Let,
            TokType::Underscore,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("y".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // `in` still continues the line after one, so a `for` header may break.
    assert_eq!(
        lex_types("for _\n    in xs {}"),
        vec![
            TokType::For,
            TokType::Underscore,
            TokType::In,
            TokType::Identifier("xs".to_string()),
            TokType::LCurlyBracket,
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // No generic context opens after it, so the `>>` below is a real shift.
    assert_eq!(
        lex_types("_ < 1 && b >> c"),
        vec![
            TokType::Underscore,
            TokType::LessThan,
            TokType::IntLiteral(1, None),
            TokType::And,
            TokType::Identifier("b".to_string()),
            TokType::RShift,
            TokType::Identifier("c".to_string()),
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
    use lex::tokens::NumSuffix;

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

// `const` is a declaration of its own, and a keyword only as a whole word.
#[test]
fn lexes_const_declaration() {
    assert_eq!(
        lex_types("const MAX: i32 = 20;"),
        vec![
            TokType::Const,
            TokType::Identifier("MAX".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Equals,
            TokType::IntLiteral(20, None),
            TokType::Semicolon,
        ]
    );
    // Its `;` is inserted at a line break like any other statement's, and it
    // takes a visibility like any other declaration.
    assert_eq!(
        lex_types("pub const PI: f64 = 3.5\nlet r = PI\n"),
        vec![
            TokType::Pub,
            TokType::Const,
            TokType::Identifier("PI".to_string()),
            TokType::Colon,
            TokType::F64,
            TokType::Equals,
            TokType::FloatLiteral(3.5, None),
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("r".to_string()),
            TokType::Equals,
            TokType::Identifier("PI".to_string()),
            TokType::Semicolon,
        ]
    );
    for word in ["constant", "consts", "const_x", "_const"] {
        assert_eq!(
            lex_types(word),
            vec![TokType::Identifier(word.to_string()), TokType::Semicolon],
            "{:?} should still lex as an identifier",
            word
        );
    }
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

// A visibility's `(suite)` is a prefix of the declaration it marks, so its `)`
// ends no statement -- the rule `%repr(C)` already follows.
#[test]
fn pub_suite_ends_no_statement() {
    assert_eq!(
        lex_types("pub(suite)\nfn f();"),
        vec![
            TokType::Pub,
            TokType::LParen,
            TokType::Suite,
            TokType::RParen,
            TokType::Fn,
            TokType::Identifier("f".to_string()),
            TokType::LParen,
            TokType::RParen,
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

// A reference is a type like any other: it heads a parameter, and the lexer
// keeps its generic context open across one.
#[test]
fn lexes_reference_types() {
    assert_eq!(
        lex_types("fn swap(a: &Point, b: *i32);"),
        vec![
            TokType::Fn,
            TokType::Identifier("swap".to_string()),
            TokType::LParen,
            TokType::Identifier("a".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::Identifier("Point".to_string()),
            TokType::Comma,
            TokType::Identifier("b".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::I32,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // The context survives both, so the `>>` is two closers and the `>` ends
    // the declaration.
    assert_eq!(
        lex_types("let m: Map<str, List<*Node>>\nlet v: Vec<&i32>\nlet w = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Identifier("List".to_string()),
            TokType::LessThan,
            TokType::Star,
            TokType::Identifier("Node".to_string()),
            TokType::GreaterThan,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Ampersand,
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
    // `&&` still cannot stand in a type argument, so a `<` in front of one was
    // a comparison and the `>>` after it is a real shift.
    assert_eq!(
        lex_types("a < b && c >> d"),
        vec![
            TokType::Identifier("a".to_string()),
            TokType::LessThan,
            TokType::Identifier("b".to_string()),
            TokType::And,
            TokType::Identifier("c".to_string()),
            TokType::RShift,
            TokType::Identifier("d".to_string()),
            TokType::Semicolon,
        ]
    );
}

// A fixed array and a view are ordinary types: they end a declaration at the
// `]` that closes them, and they stand in a type argument list like any other.
#[test]
fn lexes_array_and_view_types() {
    // `T[8]` owns its eight, and the `]` closes the statement.
    assert_eq!(
        lex_types("let a: i32[8]\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("a".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // A run is held only behind a reference, and the ref op says which kind.
    assert_eq!(
        lex_types("let s: &i32[] = &a\nlet w: *i32[] = *a[1..3]\n"),
        vec![
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::Equals,
            TokType::Ampersand,
            TokType::Identifier("a".to_string()),
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("w".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::Equals,
            TokType::Star,
            TokType::Identifier("a".to_string()),
            TokType::LBracket,
            TokType::IntLiteral(1, None),
            TokType::DotDot,
            TokType::IntLiteral(3, None),
            TokType::RBracket,
            TokType::Semicolon,
        ]
    );
    // Only the first suffix may be `[]`, so a view of rows stacks the two.
    assert_eq!(
        lex_types("fn rows(m: &i32[][3]);"),
        vec![
            TokType::Fn,
            TokType::Identifier("rows".to_string()),
            TokType::LParen,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
            TokType::LBracket,
            TokType::IntLiteral(3, None),
            TokType::RBracket,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // A view in a type argument keeps the generic context open, so the `>`
    // closes it and ends the declaration.
    assert_eq!(
        lex_types("let m: Map<str, &i32[]>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Ampersand,
            TokType::I32,
            TokType::LBracket,
            TokType::RBracket,
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

// `null` names a type as well as a value, so it stands in a type argument
// list, ends a declaration there, and `void` is an ordinary identifier again.
#[test]
fn null_is_a_type_and_a_literal() {
    assert_eq!(
        lex_types("fn log(m: str): null;"),
        vec![
            TokType::Fn,
            TokType::Identifier("log".to_string()),
            TokType::LParen,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Str,
            TokType::RParen,
            TokType::Colon,
            TokType::Null,
            TokType::Semicolon,
        ]
    );
    // The same token on both sides of the `=`.
    assert_eq!(
        lex_types("let x: null = null"),
        vec![
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Colon,
            TokType::Null,
            TokType::Equals,
            TokType::Null,
            TokType::Semicolon,
        ]
    );
    // A type argument, so the generic context survives it and the `>` closes.
    assert_eq!(
        lex_types("let s: Map<str, null>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("s".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Null,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // `void` is no longer reserved.
    assert_eq!(
        lex_types("void"),
        vec![TokType::Identifier("void".to_string()), TokType::Semicolon]
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

// A namespace body holds items, so it is a statement body: separators are
// inserted inside it as they are at file scope.
#[test]
fn lexes_namespace_declaration() {
    assert_eq!(
        lex_types("pub namespace limits {\n    const MAX: i32 = 255\n    fn clamp(n: i32): i32;\n}\nlet n = limits::MAX\n"),
        vec![
            TokType::Pub,
            TokType::Namespace,
            TokType::Identifier("limits".to_string()),
            TokType::LCurlyBracket,
            TokType::Const,
            TokType::Identifier("MAX".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::Equals,
            TokType::IntLiteral(255, None),
            TokType::Semicolon,
            TokType::Fn,
            TokType::Identifier("clamp".to_string()),
            TokType::LParen,
            TokType::Identifier("n".to_string()),
            TokType::Colon,
            TokType::I32,
            TokType::RParen,
            TokType::Colon,
            TokType::I32,
            TokType::Semicolon,
            TokType::RCurlyBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::Identifier("limits".to_string()),
            TokType::ColonColon,
            TokType::Identifier("MAX".to_string()),
            TokType::Semicolon,
        ]
    );
    // Only a statement starts with it, so a brace holding one holds statements.
    assert_eq!(
        lex_types("let v = {\n    namespace a { }\n    1\n}\n")[3],
        TokType::LCurlyBracket
    );
    // Reserved as a whole word only.
    assert_eq!(
        lex_types("namespaces"),
        vec![TokType::Identifier("namespaces".to_string()), TokType::Semicolon]
    );
}

// A qualified name reaches through a namespace with `::`, and it may do so
// inside a type argument list without abandoning the generic context.
#[test]
fn namespace_paths_use_the_scope_separator() {
    assert_eq!(
        lex_types("let c = shapes::Color::Red"),
        vec![
            TokType::Let,
            TokType::Identifier("c".to_string()),
            TokType::Equals,
            TokType::Identifier("shapes".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Color".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Red".to_string()),
            TokType::Semicolon,
        ]
    );
    // The `>` still closes the list, so the newline ends the declaration.
    assert_eq!(
        lex_types("let m: Map<str, limits::Kind>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Identifier("Map".to_string()),
            TokType::LessThan,
            TokType::Str,
            TokType::Comma,
            TokType::Identifier("limits".to_string()),
            TokType::ColonColon,
            TokType::Identifier("Kind".to_string()),
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

// Parentheses group a type, which is what gives an array of references a
// spelling. They may stand in a type argument without abandoning the context.
#[test]
fn lexes_grouped_types() {
    assert_eq!(
        lex_types("let xs: (&i32)[8]\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("xs".to_string()),
            TokType::Colon,
            TokType::LParen,
            TokType::Ampersand,
            TokType::I32,
            TokType::RParen,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("let v: Vec<(&i32)[8]>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::LParen,
            TokType::Ampersand,
            TokType::I32,
            TokType::RParen,
            TokType::LBracket,
            TokType::IntLiteral(8, None),
            TokType::RBracket,
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

// `never` is a type name like any other: it ends a declaration, stands in a
// type argument, and is a whole word only.
#[test]
fn lexes_the_never_type() {
    assert_eq!(
        lex_types("fn panic(m: str): never;"),
        vec![
            TokType::Fn,
            TokType::Identifier("panic".to_string()),
            TokType::LParen,
            TokType::Identifier("m".to_string()),
            TokType::Colon,
            TokType::Str,
            TokType::RParen,
            TokType::Colon,
            TokType::Never,
            TokType::Semicolon,
        ]
    );
    // It ends a type, so the newline after it inserts a separator.
    assert_eq!(
        lex_types("fn stop(): never\nlet n = 1\n"),
        vec![
            TokType::Fn,
            TokType::Identifier("stop".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Colon,
            TokType::Never,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("let v: Vec<never>\nlet n = 1\n"),
        vec![
            TokType::Let,
            TokType::Identifier("v".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Never,
            TokType::GreaterThan,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("n".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    for word in ["nevermore", "never_", "_never"] {
        assert_eq!(
            lex_types(word),
            vec![TokType::Identifier(word.to_string()), TokType::Semicolon],
            "{:?} should still lex as an identifier",
            word
        );
    }
}

// `unsafe` marks a fn whose caller has something to prove, and prefixes the
// statement that answers for it. Those two places are the only two.
#[test]
fn lexes_unsafe() {
    // On a signature it stands after the visibility and in front of the `fn`.
    assert_eq!(
        lex_types("pub unsafe fn write(dst: *u8[], n: u64);"),
        vec![
            TokType::Pub,
            TokType::Unsafe,
            TokType::Fn,
            TokType::Identifier("write".to_string()),
            TokType::LParen,
            TokType::Identifier("dst".to_string()),
            TokType::Colon,
            TokType::Star,
            TokType::U8,
            TokType::LBracket,
            TokType::RBracket,
            TokType::Comma,
            TokType::Identifier("n".to_string()),
            TokType::Colon,
            TokType::U64,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    // The one-line form: no braces, so the statement it prefixes ends the line
    // as it would have on its own.
    assert_eq!(
        lex_types("unsafe free(q)\nlet x = 1\n"),
        vec![
            TokType::Unsafe,
            TokType::Identifier("free".to_string()),
            TokType::LParen,
            TokType::Identifier("q".to_string()),
            TokType::RParen,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::IntLiteral(1, None),
            TokType::Semicolon,
        ]
    );
    // A `let` is a statement too, which is how a value leaves an unsafe region.
    assert_eq!(
        lex_types("unsafe let buf = malloc(n)\nlet b = buf\n"),
        vec![
            TokType::Unsafe,
            TokType::Let,
            TokType::Identifier("buf".to_string()),
            TokType::Equals,
            TokType::Identifier("malloc".to_string()),
            TokType::LParen,
            TokType::Identifier("n".to_string()),
            TokType::RParen,
            TokType::Semicolon,
            TokType::Let,
            TokType::Identifier("b".to_string()),
            TokType::Equals,
            TokType::Identifier("buf".to_string()),
            TokType::Semicolon,
        ]
    );
    for word in ["unsafely", "unsafe_", "_unsafe"] {
        assert_eq!(
            lex_types(word),
            vec![TokType::Identifier(word.to_string()), TokType::Semicolon],
            "{:?} should still lex as an identifier",
            word
        );
    }
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
