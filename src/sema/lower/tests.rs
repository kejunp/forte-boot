// What the checker makes of a source. Unlike every other test under `sema`,
// these start from text: the whole pipeline runs, so what is asserted on is
// what a reader would have got.

use super::*;
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::parse::parser::Parser;
use crate::prep::preprocess;
use crate::tir::lower::Lowerer as TIRLowerer;

// Source to typed tree. The passes before this one must all succeed: what this
// makes of a tree they turned down is not what is under test.
fn typed(source: &str) -> (TTIRProgram, Vec<String>) {
    let prepped = preprocess(source);
    let mut p = Parser::new(Lexer::new(&prepped));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{}\n{:#?}", source, p.errors());
    let root = {
        let mut e = Expander::new(&mut p);
        let out = e.expand(&root);
        assert!(e.errors().is_empty(), "{}\n{:#?}", source, e.errors());
        out
    };
    let mut l = TIRLowerer::new(&p);
    l.lower(&root);
    assert!(l.errors().is_empty(), "{}\n{:#?}", source, l.errors());
    let tir = l.finish();

    let (ttir, errors) = Lowerer::new(&tir).lower(vec!["t".to_string()]);
    let text: Vec<char> = source.chars().collect();
    let quoted = crate::error::Source::new("t.fc", &text);
    let said = errors.iter().map(|e| e.render(&quoted)).collect();
    (ttir, said)
}

fn clean(source: &str) -> TTIRProgram {
    let (ttir, said) = typed(source);
    assert!(said.is_empty(), "{}\n{:#?}", source, said);
    ttir
}

fn refused(source: &str) -> String {
    typed(source).1.join("\n")
}

// Everything a file declares becomes an item, and every one of them a symbol.
#[test]
fn a_file_becomes_a_typed_tree() {
    let ttir = clean(
        "struct Point {\n    pub x: i32,\n    pub y: i32,\n}\n\
         pub const MAX: i32 = 255;\n\
         pub fn add(a: i32, b: i32): i32 { a + b }\n",
    );
    assert_eq!(ttir.modules.len(), 1);
    assert_eq!(ttir.modules[0].path, vec!["t".to_string()]);
    assert_eq!(ttir.modules[0].roots.len(), 3);
    // The fn has a body, and its parameters are slots of it.
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "add" => Some(f),
        _ => None,
    }).expect("add");
    let body = f.body.expect("a body");
    assert_eq!(f.params.len(), 2);
    assert_eq!(f.params[0].slot, Some(0));
    assert_eq!(ttir.bodies[body].locals.len(), 2);
}

// "a name has become the declaration it names": a struct's field is reached by
// the index it turned out to be, and the name is gone.
#[test]
fn a_field_becomes_the_index_it_is() {
    let ttir = clean(
        "struct Point {\n    pub x: i32,\n    pub y: i32,\n}\n\
         fn second(p: &Point): i32 { p.y }\n",
    );
    let found = ttir.exprs.iter().any(|e| matches!(e.kind, TTIRExprKind::Field { index: 1, .. }));
    assert!(found, "{:#?}", ttir.exprs);
}

// An alias is followed and nothing of it is left in a type.
#[test]
fn an_alias_is_followed() {
    let ttir = clean("type Count = i32\nfn f(n: Count): Count { n }\n");
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) => Some(f),
        _ => None,
    }).expect("a fn");
    assert_eq!(ttir.types[f.ret], Ty::Prim(TIRPrim::I32));
}

// A number with no suffix is a hole, so what it is depends on what it is put
// beside -- which is what lets one line say `i64` and the next `u8`.
#[test]
fn a_number_takes_the_type_it_is_put_beside() {
    let ttir = clean("fn f() {\n    let a: i64 = 5\n    let b: u8 = 5\n}\n");
    let body = ttir.bodies.first().expect("a body");
    let tys: Vec<&Ty> = body.locals.iter().map(|l| &ttir.types[l.ty]).collect();
    assert_eq!(tys, vec![&Ty::Prim(TIRPrim::I64), &Ty::Prim(TIRPrim::U8)]);
}

// ---- What it turns down ---------------------------------------------------

#[test]
fn an_argument_of_the_wrong_type_is_refused() {
    let out = refused("fn add(a: i32, b: i32): i32 { a }\nfn f() { add(\"x\", 1); }\n");
    assert!(out.contains("argument 1 is `str` and it takes `i32`"), "{}", out);
}

#[test]
fn the_wrong_number_of_arguments_is_refused() {
    let out = refused("fn add(a: i32, b: i32): i32 { a }\nfn f() { add(1); }\n");
    assert!(out.contains("this takes 2 and was handed 1"), "{}", out);
}

#[test]
fn a_field_that_is_not_there_is_refused() {
    let out = refused("struct P {\n    pub x: i32,\n}\nfn f(p: &P): i32 { p.nope }\n");
    assert!(out.contains("has no field `nope`"), "{}", out);
}

#[test]
fn a_type_that_is_not_declared_is_refused() {
    let out = refused("fn f(n: Nowhere): i32 { 1 }\n");
    assert!(out.contains("no type is called `Nowhere`"), "{}", out);
}

#[test]
fn a_name_that_is_not_declared_is_refused() {
    let out = refused("fn f(): i32 { nope }\n");
    assert!(out.contains("nothing is called `nope`"), "{}", out);
}

// A body gives back what its signature said it would.
#[test]
fn a_body_is_held_to_its_signature() {
    let out = refused("fn f(): i32 { \"no\" }\n");
    assert!(out.contains("gives back `str` and the signature says `i32`"), "{}", out);
}

// The two ways of an `if` are worth one type between them. Both sides here are
// fixed on purpose: a number is a hole, and a hole would simply take whatever
// the other way was -- see the note at the top of `lower.rs`.
#[test]
fn the_two_ways_of_an_if_agree() {
    let out = refused("fn f(c: bool): bool {\n    if c { true } else { \"x\" }\n}\n");
    assert!(out.contains("one way gives") && out.contains("and the other"), "{}", out);
}

// The hole, said out loud: an unsuffixed number takes anything, so an `if` on
// one is accepted. This is the gap the note at the top of `lower.rs` names, and
// it is here so that closing it breaks a test rather than going unnoticed.
#[test]
fn a_number_is_too_free_and_this_is_where_that_shows() {
    let out = refused("fn f() {\n    if 5 { }\n}\n");
    assert_eq!(out, "", "a number that only numbers could fill would refuse this");
}

// What this pass cannot do yet says so, once, and gives the expression an
// `Error` so the rest of the body is still checked.
#[test]
fn what_it_cannot_type_yet_says_so() {
    for (source, what) in [
        ("fn f(c: i32): i32 {\n    match c {\n        _ => 1,\n    }\n}\n", "a `match`"),
        ("fn f() {\n    let m = {1: 2}\n}\n", "a map"),
        ("fn f() {\n    let g = |x: i32| x\n}\n", "a closure"),
        ("fn f() {\n    let r = 0..10\n}\n", "a range"),
    ] {
        let out = refused(source);
        assert!(
            out.contains(&format!("`sema` cannot type {} yet", what)),
            "{}\n{}",
            source,
            out
        );
    }
}
