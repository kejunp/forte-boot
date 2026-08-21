// What the checker makes of a source. Unlike every other test under `sema`,
// these start from text: the whole pipeline runs, so what is asserted on is
// what a reader would have got.

use super::*;
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::parse::parser::Parser;
use crate::prep::preprocess;
use crate::tir::lower::Lowerer as TIRLowerer;
use crate::tir::ttir_nodes::TTIRPatKind;

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

// ---- Struct literals ------------------------------------------------------

// "In declaration order, whatever order they were written in": the fields come
// out where they were declared, so everything below reads one shape.
#[test]
fn a_struct_literal_is_put_in_declaration_order() {
    let ttir = clean(
        "struct Point {\n    pub x: i32,\n    pub y: str,\n}\n\
         fn make(): Point { Point { y: \"a\", x: 1 } }\n",
    );
    let (item, fields) = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::StructLit { item, fields } => Some((*item, fields.clone())),
        _ => None,
    }).expect("a struct literal");
    assert!(matches!(ttir.items[item].kind, TTIRItemKind::Struct { .. }));
    // Written y-then-x, held x-then-y -- and the types say which is which.
    assert_eq!(ttir.types[ttir.exprs[fields[0]].ty], Ty::Prim(TIRPrim::I32));
    assert_eq!(ttir.types[ttir.exprs[fields[1]].ty], Ty::Prim(TIRPrim::Str));
}

#[test]
fn a_struct_literal_is_held_to_its_fields() {
    let with = "struct P {\n    pub x: i32,\n    pub y: i32,\n}\n";
    // A field of the wrong type.
    let out = refused(&format!("{}fn f(): P {{ P {{ x: \"a\", y: 1 }} }}\n", with));
    assert!(out.contains("`x` is `str` and the field is `i32`"), "{}", out);
    // A field that is not there.
    let out = refused(&format!("{}fn f(): P {{ P {{ x: 1, y: 2, z: 3 }} }}\n", with));
    assert!(out.contains("`P` has no field `z`"), "{}", out);
    // A field left out: "a struct is built with every field it declares".
    let out = refused(&format!("{}fn f(): P {{ P {{ x: 1 }} }}\n", with));
    assert!(out.contains("`P` is not whole"), "{}", out);
    assert!(out.contains("`y` left out"), "{}", out);
    // And one given twice.
    let out = refused(&format!("{}fn f(): P {{ P {{ x: 1, y: 2, x: 3 }} }}\n", with));
    assert!(out.contains("`x` is given twice"), "{}", out);
}

#[test]
fn only_a_struct_is_built_with_a_brace() {
    let out = refused("enum E {\n    A,\n}\nfn f() {\n    let e = E { x: 1 }\n}\n");
    assert!(out.contains("`E` is not a struct"), "{}", out);
}

// ---- Match ----------------------------------------------------------------

// "A `<const_pattern>` tests and any other name binds, which makes what a
// pattern means depend on what is in scope" (section 5.2).
#[test]
fn a_name_tests_where_it_names_a_constant_and_binds_where_it_does_not() {
    let ttir = clean(
        "const MAX: i32 = 255;\n\
         fn f(n: i32): i32 {\n    match n {\n        MAX => 1,\n        other => other,\n    }\n}\n",
    );
    let kinds: Vec<&TTIRPatKind> = ttir.pats.iter().map(|p| &p.kind).collect();
    assert!(kinds.iter().any(|k| matches!(k, TTIRPatKind::Const(_))), "{:?}", kinds);
    assert!(kinds.iter().any(|k| matches!(k, TTIRPatKind::Bind(_))), "{:?}", kinds);
}

// What a pattern binds stands in that arm and nowhere else.
#[test]
fn what_an_arm_binds_stands_in_that_arm() {
    clean(
        "fn f(n: i32): i32 {\n    match n {\n        held => held,\n    }\n}\n",
    );
    let out = refused(
        "fn f(n: i32): i32 {\n    match n {\n        held => 1,\n    }\n    held\n}\n",
    );
    assert!(out.contains("nothing is called `held`"), "{}", out);
}

// Every arm is worth the one type.
#[test]
fn every_arm_is_worth_one_type() {
    let out = refused(
        "fn f(c: bool): bool {\n    match c {\n        true => true,\n        _ => \"no\",\n    }\n}\n",
    );
    assert!(out.contains("one arm gives") && out.contains("and another"), "{}", out);
}

// "an expression of it agrees with anything beside it" -- so a `never` arm
// agrees with whatever the others are worth, which is what a `panic` arm is.
#[test]
fn a_never_arm_agrees_with_the_rest() {
    clean(
        "fn f(n: i32): i32 {\n    match n {\n        1 => 5,\n        _ => return 0,\n    }\n}\n",
    );
}

// A variant is reached through its enum, and what it carries is tested with it.
#[test]
fn a_variant_pattern_reaches_what_it_carries() {
    let ttir = clean(
        "enum Shape {\n    Dot,\n    Line(i32),\n}\n\
         fn f(s: Shape): i32 {\n    match s {\n        Shape::Line(n) => n,\n        Shape::Dot => 0,\n    }\n}\n",
    );
    let variants: Vec<usize> = ttir
        .pats
        .iter()
        .filter_map(|p| match &p.kind {
            TTIRPatKind::Variant { variant, .. } => Some(*variant),
            _ => None,
        })
        .collect();
    assert_eq!(variants, vec![1, 0], "{:?}", ttir.pats);
    // The `n` it bound is an i32, which is what the variant carries.
    let bound = ttir.bodies[0].locals.iter().find(|l| {
        matches!(&l.name, crate::tir::tir_nodes::TIRBinding::Name(n) if n == "n")
    }).expect("n");
    assert_eq!(ttir.types[bound.ty], Ty::Prim(TIRPrim::I32));
}

// A tuple pattern reaches into a tuple, member by member.
#[test]
fn a_tuple_pattern_reaches_its_members() {
    let ttir = clean(
        "fn f(p: (i32, str)): str {\n    match p {\n        (n, s) => s,\n    }\n}\n",
    );
    let s = ttir.bodies[0].locals.iter().find(|l| {
        matches!(&l.name, crate::tir::tir_nodes::TIRBinding::Name(n) if n == "s")
    }).expect("s");
    assert_eq!(ttir.types[s.ty], Ty::Prim(TIRPrim::Str));

    let out = refused("fn f(n: i32): i32 {\n    match n {\n        (a, b) => a,\n    }\n}\n");
    assert!(out.contains("`i32` is not a tuple"), "{}", out);
}

// "Fields in declaration order, `None` where the pattern named none" -- so a
// pattern may test some fields and leave the rest.
#[test]
fn a_struct_pattern_may_name_some_of_the_fields() {
    let ttir = clean(
        "struct P {\n    pub x: i32,\n    pub y: str,\n}\n\
         fn f(p: P): i32 {\n    match p {\n        P { x } => x,\n    }\n}\n",
    );
    let fields = ttir.pats.iter().find_map(|p| match &p.kind {
        TTIRPatKind::Struct { fields, .. } => Some(fields.clone()),
        _ => None,
    }).expect("a struct pattern");
    assert_eq!(fields.len(), 2);
    assert!(fields[0].is_some());
    // `y` was not named, so nothing tests it.
    assert!(fields[1].is_none());
}

// A pattern is held to what it is tested on.
#[test]
fn a_pattern_is_held_to_the_scrutinee() {
    let out = refused("fn f(s: str): i32 {\n    match s {\n        true => 1,\n        _ => 0,\n    }\n}\n");
    assert!(out.contains("this tests `bool` against `str`"), "{}", out);
}

// A variant may be struct-shaped, and is written like a struct: which it is is
// what the path names.
#[test]
fn a_struct_shaped_variant_is_reached_by_name() {
    let ttir = clean(
        "enum Shape {\n    Dot,\n    Box { w: i32, h: str },\n}\n\
         fn f(s: Shape): str {\n    match s {\n        Shape::Box { h } => h,\n        _ => \"\",\n    }\n}\n",
    );
    // The `h` it bound is the `str` the variant carries, and the `w` it did not
    // name is a wildcard rather than a hole.
    let held = ttir.bodies[0].locals.iter().find(|l| {
        matches!(&l.name, crate::tir::tir_nodes::TIRBinding::Name(n) if n == "h")
    }).expect("h");
    assert_eq!(ttir.types[held.ty], Ty::Prim(TIRPrim::Str));

    let elems = ttir.pats.iter().find_map(|p| match &p.kind {
        TTIRPatKind::Variant { elems, .. } if !elems.is_empty() => Some(elems.clone()),
        _ => None,
    }).expect("a struct-shaped variant");
    assert_eq!(elems.len(), 2);
    assert!(matches!(ttir.pats[elems[0]].kind, TTIRPatKind::Wildcard));
    assert!(matches!(ttir.pats[elems[1]].kind, TTIRPatKind::Bind(_)));

    let out = refused(
        "enum Shape {\n    Box { w: i32 },\n}\n\
         fn f(s: Shape): i32 {\n    match s {\n        Shape::Box { nope } => 1,\n    }\n}\n",
    );
    assert!(out.contains("carries no `nope`"), "{}", out);
}
