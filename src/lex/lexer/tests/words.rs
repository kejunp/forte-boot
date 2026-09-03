// Keywords, names, and the words that are one but look like the other.
//
// A word reserved as a whole word only is the theme: `gc` is a modifier and
// `gc_root` is a name, `_` is the wildcard and `_foo` is not.

use super::*;

// `gc` stands between the intro and the name and ends nothing: no separator is
// inserted after it, and it is reserved as a whole word only, so `gcx` and
// `gc_root` still lex as the identifiers they are.
#[test]
fn lexes_gc_as_a_binding_modifier() {
    assert_eq!(
        lex_types("let gc x = #{1: 2}\n"),
        vec![
            TokType::Let,
            TokType::Gc,
            TokType::Identifier("x".to_string()),
            TokType::Equals,
            TokType::HashTag,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Colon,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    // It heads no body, so a `{` after one is decided by what it holds as it
    // would be after any other name-shaped position: this is a set literal.
    assert_eq!(
        lex_types("var gc s = {1, 2}\n"),
        vec![
            TokType::Var,
            TokType::Gc,
            TokType::Identifier("s".to_string()),
            TokType::Equals,
            TokType::LCurlyValue,
            TokType::IntLiteral(1, None),
            TokType::Comma,
            TokType::IntLiteral(2, None),
            TokType::RCurlyBracket,
            TokType::Semicolon,
        ]
    );
    assert_eq!(
        lex_types("gcx gc_root"),
        vec![
            TokType::Identifier("gcx".to_string()),
            TokType::Identifier("gc_root".to_string()),
            TokType::Semicolon,
        ]
    );
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

// `ptr` and `addr` are the two words a raw pointer is written with: one names
// the type and the other makes one. Neither ends an operand, so neither can
// have a separator inserted after it and a type may run onto the next line.
#[test]
fn lexes_ptr_and_addr() {
    assert_eq!(
        lex_types("unsafe let p: ptr u8 = addr b\n"),
        vec![
            TokType::Unsafe,
            TokType::Let,
            TokType::Identifier("p".to_string()),
            TokType::Colon,
            TokType::Ptr,
            TokType::U8,
            TokType::Equals,
            TokType::Addr,
            TokType::Identifier("b".to_string()),
            TokType::Semicolon,
        ]
    );
    // A pointer stands in a type argument list, which the lexer has to allow
    // for: a `<` opens a generic context and the first token no type argument
    // could hold abandons it, taking the `>>` splitting with it.
    assert_eq!(
        lex_types("let all: Vec<ptr u8> = empty();"),
        vec![
            TokType::Let,
            TokType::Identifier("all".to_string()),
            TokType::Colon,
            TokType::Identifier("Vec".to_string()),
            TokType::LessThan,
            TokType::Ptr,
            TokType::U8,
            TokType::GreaterThan,
            TokType::Equals,
            TokType::Identifier("empty".to_string()),
            TokType::LParen,
            TokType::RParen,
            TokType::Semicolon,
        ]
    );
    for word in ["ptrs", "ptr_", "_ptr", "address", "addr_", "_addr"] {
        assert_eq!(
            lex_types(word),
            vec![TokType::Identifier(word.to_string()), TokType::Semicolon],
            "{:?} should still lex as an identifier",
            word
        );
    }
}
