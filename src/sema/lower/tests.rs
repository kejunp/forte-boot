// What the checker makes of a source. Unlike every other test under `sema`,
// these start from text: the whole pipeline runs, so what is asserted on is
// what a reader would have got.

use super::*;
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::parse::parser::Parser;
use crate::prep::preprocess;
use crate::tir::lower::Lowerer as TIRLowerer;
use crate::tir::ttir_nodes::{TTIRBound, TTIRCaptureMode, TTIRGeneric, TTIRPatKind, TTIRSubject};
use crate::tir::tir_nodes::TIRRefOp;

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

// A number goes in a hole only numbers fill, so it takes whatever numeric type
// it is put beside and nothing else.
#[test]
fn a_number_only_goes_where_a_number_goes() {
    let out = refused("fn f() {\n    if 5 { }\n}\n");
    assert!(out.contains("an `if` asks a `bool`"), "{}", out);
    let out = refused("fn f(): str { 5 }\n");
    assert!(out.contains("gives back") && out.contains("`str`"), "{}", out);
    // And a whole number is not a fractional one.
    let out = refused("fn f() {\n    let x: f32 = 1\n    let y: i32 = 1.5\n}\n");
    assert!(out.contains("`i32`"), "{}", out);
}

// A number nobody said anything about is what it would have been written as.
#[test]
fn a_number_on_its_own_is_an_i32() {
    let ttir = clean("fn f() {\n    var n = 0\n    let x = 1.5\n}\n");
    let tys: Vec<&Ty> = ttir.bodies[0].locals.iter().map(|l| &ttir.types[l.ty]).collect();
    assert_eq!(tys, vec![&Ty::Prim(TIRPrim::I32), &Ty::Prim(TIRPrim::F64)]);
}

// Every expression form is typed now. What is left for the checker is not a
// form it cannot read but a rule it does not yet hold anyone to -- a bound, a
// region, an exhaustive `match`.
#[test]
fn every_expression_form_is_typed() {
    let with = "struct Range<T> {\n    pub n: i32,\n}\n\
                struct Map<K, V> {\n    pub n: i32,\n}\n\
                struct Set<T> {\n    pub n: i32,\n}\n\
                struct P {\n    pub x: i32,\n}\n\
                enum E {\n    A,\n    B(i32),\n}\n\
                impl P {\n    fn get(&self): i32 { self.x }\n}\n";
    clean(&format!(
        "{}fn f(p: P, v: i32[2]): i32 {{\n\
         \x20   let a = P {{ x: 1 }}\n\
         \x20   let b = E::B(2)\n\
         \x20   let c = E::A\n\
         \x20   let d = {{1: 2}}\n\
         \x20   let e = {{1, 2}}\n\
         \x20   let g = 0..3\n\
         \x20   let h = |x: i32| x\n\
         \x20   let i = p.get()\n\
         \x20   for x in v {{ }}\n\
         \x20   match b {{ E::A => 0, E::B(n) => n }}\n\
         }}\n",
        with
    ));
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

// ---- Closures -------------------------------------------------------------

// "A name the body uses but did not declare is captured, and how is worked out
// per name, each taking the least the body asks of it. Reading one takes a `&`
// of it and assigning to one takes a `*`" (section 5). The prose's own example.
#[test]
fn a_capture_takes_the_least_the_body_asks() {
    let ttir = clean(
        // Three fns and not one block: a capture is a borrow that lasts as long
        // as the closure, so a `&` and a `*` of one name in one block is the
        // aliasing rule being broken and not the capture rule being shown.
        "fn f() {\n\
         \x20   var n = 0\n\
         \x20   let show = || n\n\
         }\n\
         fn g() {\n\
         \x20   var n = 0\n\
         \x20   let bump = || n = n + 1\n\
         }\n\
         fn h() {\n\
         \x20   var n = 0\n\
         \x20   let own = move || n\n\
         }\n",
    );
    let modes: Vec<TTIRCaptureMode> = ttir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Closure { captures, .. } => captures.first().map(|c| c.mode),
            _ => None,
        })
        .collect();
    assert_eq!(
        modes,
        vec![
            // `|| n` reads it.
            TTIRCaptureMode::Ref(TIRRefOp::Imm),
            // `|| n = n + 1` assigns to it.
            TTIRCaptureMode::Ref(TIRRefOp::Mut),
            // "a `move` closure captures every name by value instead".
            TTIRCaptureMode::Value,
        ]
    );
}

// A closure's parameters are slots of its own body, and a name it did not
// declare is a slot of its own too -- standing for the one outside it.
#[test]
fn a_closure_is_a_body_of_its_own() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = |x: i32| x + n\n}\n");
    let (captures, body) = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Closure { captures, body } => Some((captures.clone(), *body)),
        _ => None,
    }).expect("a closure");
    assert_eq!(captures.len(), 1);
    // The slot inside stands for the slot outside, and the two are not the same
    // number: `outer` is the frame's and `slot` is the closure's.
    let inner = &ttir.bodies[body];
    assert_eq!(inner.locals.len(), 2, "the parameter and what it caught");
    assert_eq!(captures[0].slot, 1);
    assert_eq!(captures[0].outer, 0);
}

// A name used twice is caught once.
#[test]
fn a_name_is_caught_once_however_often_it_is_used() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = || n + n + n\n}\n");
    let captures = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Closure { captures, .. } => Some(captures.clone()),
        _ => None,
    }).expect("a closure");
    assert_eq!(captures.len(), 1);
}

// A closure inside a closure takes what it needs from the one that took it.
#[test]
fn a_closure_inside_a_closure_catches_through_it() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = || || n\n}\n");
    let held: Vec<usize> = ttir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Closure { captures, .. } => Some(captures.len()),
            _ => None,
        })
        .collect();
    // Both of them caught it: the inner one from the outer, and the outer one
    // from the fn.
    assert_eq!(held, vec![1, 1]);
}

// ---- Method calls ---------------------------------------------------------

// "A method, resolved to the one it calls. `.` and `::` are both gone": the
// TIR has no method call of its own, and which a call of a field is, is settled
// here.
#[test]
fn a_call_of_a_field_may_be_a_method() {
    let ttir = clean(
        "struct Buf {\n    pub n: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.len() }\n",
    );
    let found = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Method { item, .. } => Some(*item),
        _ => None,
    }).expect("a method call");
    let TTIRItemKind::Fn(f) = &ttir.items[found].kind else { panic!() };
    assert_eq!(f.name, "len");
}

// A method is reached through a reference too: "a reference stands for the
// place it refers to and is read, called, indexed and reached into exactly as
// that place is".
#[test]
fn a_method_is_reached_through_a_reference() {
    clean(
        "struct Buf {\n    pub n: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: &Buf): i32 { b.len() }\n",
    );
}

// The receiver is not one of the arguments, so what a call was handed is what
// is left after it.
#[test]
fn a_method_is_held_to_what_it_takes() {
    let with = "struct Buf {\n    pub n: i32,\n}\n\
                impl Buf {\n    fn put(&self, x: i32): i32 { x }\n}\n";
    clean(&format!("{}fn f(b: Buf): i32 {{ b.put(1) }}\n", with));
    let out = refused(&format!("{}fn f(b: Buf): i32 {{ b.put(\"x\") }}\n", with));
    assert!(out.contains("argument 1 is `str` and it takes `i32`"), "{}", out);
    let out = refused(&format!("{}fn f(b: Buf): i32 {{ b.put(1, 2) }}\n", with));
    assert!(out.contains("`put` takes 1 and was handed 2"), "{}", out);
}

// A field of the same name wins: it is the nearer thing, and a struct holding
// a fn is reached before an impl is looked in.
#[test]
fn a_field_is_reached_before_an_impl_is() {
    let out = refused(
        "struct Buf {\n    pub len: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.len() }\n",
    );
    // The field is not a fn, so calling it says so rather than finding the
    // method.
    assert!(out.contains("`i32` is not a fn"), "{}", out);
}

// ---- Maps, sets and ranges ------------------------------------------------

// "A map and a set are `Map<K, V>` and `Set<T>`, and the hashed kinds are types
// of their own, `HashMap<K, V>` and `HashSet<T>` -- so which one you named says
// how it behaves, and a `#{` literal builds the hashed one" (section 8).
#[test]
fn a_literal_builds_the_type_a_library_declared() {
    let with = "struct Map<K, V> {\n    pub n: i32,\n}\n\
                struct HashMap<K, V> {\n    pub n: i32,\n}\n\
                struct Set<T> {\n    pub n: i32,\n}\n\
                struct HashSet<T> {\n    pub n: i32,\n}\n";
    let ttir = clean(&format!(
        "{}fn f() {{\n    let m = {{1: 2}}\n    let h = #{{1: 2}}\n    let s = {{1, 2}}\n    let g = #{{1, 2}}\n}}\n",
        with
    ));
    let names: Vec<String> = ttir.bodies[0]
        .locals
        .iter()
        .map(|l| match &ttir.types[l.ty] {
            Ty::Named { item, .. } => match &ttir.items[*item].kind {
                TTIRItemKind::Struct { name, .. } => name.clone(),
                _ => "?".to_string(),
            },
            other => format!("{:?}", other),
        })
        .collect();
    // The `#` is what says hashed, and the hashed kind is its own type.
    assert_eq!(names, vec!["Map", "HashMap", "Set", "HashSet"]);
}

// Every key is one type and every value another, which is what makes a map a
// map rather than a list of pairs.
#[test]
fn a_map_holds_one_type_of_key_and_one_of_value() {
    let with = "struct Map<K, V> {\n    pub n: i32,\n}\n";
    clean(&format!("{}fn f() {{\n    let m = {{1: \"a\", 2: \"b\"}}\n}}\n", with));
    let out = refused(&format!("{}fn f() {{\n    let m = {{1: \"a\", \"b\": 2}}\n}}\n", with));
    assert!(out.contains("every key of a map is one type"), "{}", out);
}

#[test]
fn a_set_holds_one_type() {
    let with = "struct Set<T> {\n    pub n: i32,\n}\n";
    clean(&format!("{}fn f() {{\n    let s = {{1, 2, 3}}\n}}\n", with));
    let out = refused(&format!("{}fn f() {{\n    let s = {{1, \"a\"}}\n}}\n", with));
    assert!(out.contains("every element of a set is one type"), "{}", out);
}

// "every bound is optional: `1..10`, `1..`, `..10`, `..=n`, `..`" -- and
// however many were written, a range runs between one type.
#[test]
fn a_range_runs_between_one_type() {
    let with = "struct Range<T> {\n    pub n: i32,\n}\n";
    clean(&format!(
        "{}fn f() {{\n    let a = 1..10\n    let b = 1..\n    let c = ..10\n    let e = 1..=9\n}}\n",
        with
    ));
    let out = refused(&format!("{}fn f() {{\n    let r = 1..\"x\"\n}}\n", with));
    assert!(out.contains("a range runs between one type"), "{}", out);
}

// `..` with neither bound is the one shape that says nothing about what it
// runs between, so on its own it leaves the type open -- and the checker says
// so rather than guessing.
//
// This is the cost of one `Range<T>` for all four shapes. Four types would put
// the empty one in a type with no element at all, which is what Rust's
// `RangeFull` is; the prose names neither, so this is the choice and this is
// what it costs.
#[test]
fn a_range_with_no_bounds_says_nothing_about_what_it_runs_between() {
    let with = "struct Range<T> {\n    pub n: i32,\n}\n";
    let out = refused(&format!("{}fn f() {{\n    let d = ..\n}}\n", with));
    assert!(out.contains("never worked out"), "{}", out);
    // Put where something says what it holds, it is settled like any other.
    clean(&format!("{}fn f(r: Range<i32>) {{\n    let d: Range<i32> = ..\n}}\n", with));
}

// A literal is syntax for a type a library declares, so a suite that declares
// none says so rather than building something that is not there.
#[test]
fn a_literal_with_no_type_behind_it_says_so() {
    let out = refused("fn f() {\n    let m = {1: 2}\n}\n");
    assert!(out.contains("no type is called `Map`"), "{}", out);
    let out = refused("fn f() {\n    let s = #{1, 2}\n}\n");
    assert!(out.contains("no type is called `HashSet`"), "{}", out);
    let out = refused("fn f() {\n    let r = 1..2\n}\n");
    assert!(out.contains("no type is called `Range`"), "{}", out);
}

// ---- Loops ----------------------------------------------------------------

// The loop variable holds what the thing being run through holds, and it
// stands in the body and nowhere else.
#[test]
fn a_for_binds_what_it_runs_through() {
    let ttir = clean("fn f(v: i32[3]) {\n    for x in v {\n        let y = x + 1\n    }\n}\n");
    let x = ttir.bodies[0].locals.iter().find(|l| {
        matches!(&l.name, crate::tir::tir_nodes::TIRBinding::Name(n) if n == "x")
    }).expect("x");
    assert_eq!(ttir.types[x.ty], Ty::Prim(TIRPrim::I32));

    let out = refused("fn f(v: i32[3]): i32 {\n    for x in v {\n    }\n    x\n}\n");
    assert!(out.contains("nothing is called `x`"), "{}", out);
}

// The closed set the language has, there being no protocol to ask.
#[test]
fn what_may_be_run_through_is_a_closed_set() {
    let with = "struct Range<T> {\n    pub n: i32,\n}\n\
                struct Set<T> {\n    pub n: i32,\n}\n";
    // An array, a view of one, a range and a set.
    clean(&format!("{}fn f(v: i32[3]) {{\n    for x in v {{\n    }}\n}}\n", with));
    clean(&format!("{}fn f(v: &i32[]) {{\n    for x in v {{\n    }}\n}}\n", with));
    clean(&format!("{}fn f() {{\n    for i in 0..10 {{\n    }}\n}}\n", with));
    clean(&format!("{}fn f() {{\n    for i in {{1, 2}} {{\n    }}\n}}\n", with));

    // And a thing that is none of them says so, and says why the set is closed.
    let out = refused(&format!("{}fn f(n: i32) {{\n    for x in n {{\n    }}\n}}\n", with));
    assert!(out.contains("there is no running through a `i32`"), "{}", out);
    assert!(out.contains("no iterator protocol"), "{}", out);
}

// "while, for -- the operand of the `break` that leaves it. Every loop takes
// one... and where none is given the loop is `null`" (section 5.1).
#[test]
fn a_loop_is_worth_the_break_that_leaves_it() {
    // `break x` in a `for` as much as in a `while`.
    let ttir = clean(
        "fn f(v: i32[3]): i32 {\n    for x in v {\n        break x\n    }\n}\n",
    );
    let held = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::For { .. } => Some(e.ty),
        _ => None,
    }).expect("a for");
    assert_eq!(ttir.types[held], Ty::Prim(TIRPrim::I32));

    let ttir = clean("fn f(c: bool): i32 {\n    while c {\n        break 1\n    }\n}\n");
    let held = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::While { .. } => Some(e.ty),
        _ => None,
    }).expect("a while");
    assert_eq!(ttir.types[held], Ty::Prim(TIRPrim::I32));
}

// "a loop that ends by itself with the condition going false or the sequence
// running out" is `null`, and a bare `break` is too.
#[test]
fn a_loop_that_ends_by_itself_is_null() {
    let ttir = clean("fn f(c: bool) {\n    while c {\n        break\n    }\n}\n");
    let held = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::While { .. } => Some(e.ty),
        _ => None,
    }).expect("a while");
    assert_eq!(ttir.types[held], Ty::Prim(TIRPrim::Null));
}

// Every `break` leaving one loop agrees on a type.
#[test]
fn every_break_of_one_loop_agrees() {
    let out = refused(
        "fn f(c: bool): i32 {\n    while c {\n        if c { break 1 } else { break \"x\" }\n    }\n}\n",
    );
    assert!(out.contains("one `break` gives") && out.contains("and another"), "{}", out);
}

// A `break` of the inner loop is the inner loop's, not the outer one's.
#[test]
fn a_break_belongs_to_the_loop_it_is_in() {
    let ttir = clean(
        "fn f(c: bool): i32 {\n\
         \x20   while c {\n\
         \x20       while c {\n\
         \x20           break 1\n\
         \x20       }\n\
         \x20   }\n\
         \x20   0\n\
         }\n",
    );
    let held: Vec<&Ty> = ttir
        .exprs
        .iter()
        .filter(|e| matches!(e.kind, TTIRExprKind::While { .. }))
        .map(|e| &ttir.types[e.ty])
        .collect();
    // The inner is worth what its `break` gave; the outer, having none of its
    // own, is `null`.
    assert_eq!(held, vec![&Ty::Prim(TIRPrim::I32), &Ty::Prim(TIRPrim::Null)]);
}

// A `while` asks a `bool` as an `if` does.
#[test]
fn a_while_asks_a_bool() {
    let out = refused("fn f() {\n    while 5 {\n    }\n}\n");
    assert!(out.contains("a `while` asks a `bool`"), "{}", out);
}

#[test]
fn a_break_outside_a_loop_is_refused() {
    let out = refused("fn f() {\n    break\n}\n");
    assert!(out.contains("`break` is not in a loop"), "{}", out);
}

// ---- Paths and variants ---------------------------------------------------

// "`::` reaches into a namespace, a module or a type" -- and what it reaches is
// a declaration, so the whole path is looked up rather than the base typed as
// a value. An enum is not one.
#[test]
fn a_variant_is_a_value_reached_through_its_enum() {
    let ttir = clean("enum C {\n    A,\n    B(i32),\n}\nfn f(): C { C::A }\n");
    let (item, fields) = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::VariantLit { item, fields, .. } => Some((*item, fields.clone())),
        _ => None,
    }).expect("a variant");
    assert!(matches!(ttir.items[item].kind, TTIRItemKind::Enum { .. }));
    assert!(fields.is_empty(), "`A` carries nothing");
}

// A variant that carries something is built by handing it that.
#[test]
fn a_variant_that_carries_is_built_with_what_it_carries() {
    let with = "enum C {\n    A,\n    B(i32),\n}\n";
    let ttir = clean(&format!("{}fn f(): C {{ C::B(2) }}\n", with));
    let fields = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::VariantLit { fields, .. } if !fields.is_empty() => Some(fields.clone()),
        _ => None,
    }).expect("a variant");
    assert_eq!(fields.len(), 1);

    let out = refused(&format!("{}fn f(): C {{ C::B(\"x\") }}\n", with));
    assert!(out.contains("value 1 is `str` and it carries `i32`"), "{}", out);
    let out = refused(&format!("{}fn f(): C {{ C::B(1, 2) }}\n", with));
    assert!(out.contains("`B` carries 1 and was given 2"), "{}", out);
    let out = refused(&format!("{}fn f(): C {{ C::Nope }}\n", with));
    assert!(out.contains("nothing is called `C::Nope`"), "{}", out);
}

// A namespace is reached the same way.
#[test]
fn a_namespace_member_is_reached_through_it() {
    clean(
        "namespace limits {\n    pub const MAX: i32 = 255;\n}\n\
         fn f(): i32 { limits::MAX }\n",
    );
}

// ---- Type arguments -------------------------------------------------------

// "what it stands for is settled at the call and not at the declaration": every
// parameter gets a hole at each use, so one declaration serves every caller.
#[test]
fn a_generic_works_out_its_own_parameters() {
    let ttir = clean(
        "fn id<T>(x: T): T { x }\n\
         fn f(): i32 { id(1) }\n\
         fn g(): str { id(\"a\") }\n",
    );
    // Two calls of one declaration, each settled to its own type.
    let calls: Vec<&Ty> = ttir
        .exprs
        .iter()
        .filter(|e| matches!(e.kind, TTIRExprKind::Call { .. }))
        .map(|e| &ttir.types[e.ty])
        .collect();
    assert_eq!(calls, vec![&Ty::Prim(TIRPrim::I32), &Ty::Prim(TIRPrim::Str)]);
}

// And where they are written, they are what is put there.
#[test]
fn type_arguments_may_be_written_at_the_call() {
    clean("fn id<T>(x: T): T { x }\nfn f(): i32 { id<i32>(1) }\n");

    // Written, they are held to: `id<str>(1)` is an i32 where a str was asked.
    let out = refused("fn id<T>(x: T): T { x }\nfn f(): str { id<str>(1) }\n");
    assert!(out.contains("argument 1 is"), "{}", out);
    // The wrong number of them.
    let out = refused("fn id<T>(x: T): T { x }\nfn f(): i32 { id<i32, str>(1) }\n");
    assert!(out.contains("takes 1 type arguments and was given 2"), "{}", out);
    // And on something that has none.
    let out = refused("fn plain(x: i32): i32 { x }\nfn f(): i32 { plain<i32>(1) }\n");
    assert!(out.contains("takes no type arguments"), "{}", out);
}

// A parameter that appears twice is one type at each call.
#[test]
fn one_parameter_is_one_type_across_a_signature() {
    clean("fn pair<T>(a: T, b: T): T { a }\nfn f(): i32 { pair(1, 2) }\n");
    let out = refused("fn pair<T>(a: T, b: T): T { a }\nfn f(): i32 { pair(1, \"x\") }\n");
    assert!(out.contains("argument 2 is `str`"), "{}", out);
}

// ---- Trait bounds ---------------------------------------------------------

// A parameter is held to what it was declared with, and an impl is how a type
// says it answers: "an impl makes methods for its type".
#[test]
fn a_parameter_is_held_to_its_bound() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Buf {\n    pub n: i32,\n}\n\
                struct Raw {\n    pub n: i32,\n}\n\
                impl Show for Buf {\n    fn show(&self): str { \"buf\" }\n}\n\
                fn tell<T: Show>(x: T): str { \"x\" }\n";
    clean(&format!("{}fn f(b: Buf): str {{ tell(b) }}\n", with));

    let out = refused(&format!("{}fn f(r: Raw): str {{ tell(r) }}\n", with));
    assert!(out.contains("`Raw` does not answer `Show`"), "{}", out);
    assert!(out.contains("`T` is held to it here"), "{}", out);
    assert!(out.contains("`impl Show for Raw` is how a type says it does"), "{}", out);
}

// "`fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing", so a
// predicate about a parameter is folded into that parameter's bounds and the
// two spellings come out as one.
#[test]
fn a_where_about_a_parameter_is_folded_into_it() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Raw {\n    pub n: i32,\n}\n";
    let inline = refused(&format!(
        "{}fn tell<T: Show>(x: T): str {{ \"x\" }}\nfn f(r: Raw): str {{ tell(r) }}\n",
        with
    ));
    let written = refused(&format!(
        "{}fn tell<T>(x: T): str where T: Show {{ \"x\" }}\nfn f(r: Raw): str {{ tell(r) }}\n",
        with
    ));
    assert!(inline.contains("does not answer `Show`"), "{}", inline);
    assert_eq!(inline, written, "the two spellings say the same thing");
}

// Written arguments are held to the bounds as worked-out ones are.
#[test]
fn a_written_type_argument_is_held_to_the_bound() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Raw {\n    pub n: i32,\n}\n\
                fn tell<T: Show>(x: T): str { \"x\" }\n";
    let out = refused(&format!("{}fn f(r: Raw): str {{ tell<Raw>(r) }}\n", with));
    assert!(out.contains("`Raw` does not answer `Show`"), "{}", out);
}

// A generic holding another generic to a trait is answered by whoever calls it
// and not here: `T` says it answers `Show`, so passing it on is fine.
#[test]
fn a_parameter_answers_a_bound_it_was_declared_with() {
    clean(
        "trait Show {\n    fn show(&self): str;\n}\n\
         fn tell<T: Show>(x: T): str { \"x\" }\n\
         fn pass<U: Show>(y: U): str { tell(y) }\n",
    );
}

// The bounds are on the tree for whatever reads it: `is_copy` in
// `sema::borrows` asks exactly this.
#[test]
fn the_bounds_are_kept_on_the_declaration() {
    let ttir = clean(
        "trait Ord {\n    fn cmp(&self): i32;\n}\n\
         fn sort<T: Ord>(x: T): T { x }\n",
    );
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "sort" => Some(f),
        _ => None,
    }).expect("sort");
    let TTIRGeneric::Type { name, bounds } = &f.generics[0] else { panic!() };
    assert_eq!(name, "T");
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0], TTIRBound::Trait(_)));
}

// A `where` about something that is not a parameter has no parameter to fold
// into, and is kept as the predicate it is.
#[test]
fn a_where_about_a_built_type_is_kept() {
    let ttir = clean(
        "trait Show {\n    fn show(&self): str;\n}\n\
         struct Vec<T> {\n    pub n: i32,\n}\n\
         fn f<T>(x: T): i32 where Vec<T>: Show { 1 }\n",
    );
    let held = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "f" => Some(f),
        _ => None,
    }).expect("f");
    assert_eq!(held.wheres.len(), 1, "{:?}", held.wheres);
    assert!(matches!(held.wheres[0].subject, TTIRSubject::Type(_)));
    // And the parameter it is not about kept none of it.
    let TTIRGeneric::Type { bounds, .. } = &held.generics[0] else { panic!() };
    assert!(bounds.is_empty());
}

// ---- Exhaustiveness -------------------------------------------------------

// A `match` is worth "the arm taken" (section 5.1), so a match where no arm is
// taken is worth nothing -- and every other expression in the language is
// worth something.
#[test]
fn an_enum_is_taken_by_naming_every_variant() {
    let with = "enum Color {\n    Red,\n    Green,\n    Blue,\n}\n";
    clean(&format!(
        "{}fn f(c: Color): i32 {{\n    match c {{\n        Color::Red => 1,\n        Color::Green => 2,\n        Color::Blue => 3,\n    }}\n}}\n",
        with
    ));

    let out = refused(&format!(
        "{}fn f(c: Color): i32 {{\n    match c {{\n        Color::Red => 1,\n        Color::Green => 2,\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("this `match` does not take everything"), "{}", out);
    assert!(out.contains("`Color::Blue` is not taken"), "{}", out);
    assert!(out.contains("a `_` arm takes whatever is left"), "{}", out);
}

// "The two differ only in that the wildcard binds nothing" -- so either takes
// everything, and one arm of those settles it.
#[test]
fn a_name_or_a_wildcard_takes_everything() {
    let with = "enum Color {\n    Red,\n    Green,\n}\n";
    clean(&format!(
        "{}fn f(c: Color): i32 {{\n    match c {{\n        Color::Red => 1,\n        _ => 2,\n    }}\n}}\n",
        with
    ));
    clean(&format!(
        "{}fn f(c: Color): i32 {{\n    match c {{\n        other => 1,\n    }}\n}}\n",
        with
    ));
}

// "There is no counting the i32s": nothing but a name takes them all.
#[test]
fn a_number_is_taken_only_by_a_name() {
    let out = refused("fn f(n: i32): i32 {\n    match n {\n        1 => 1,\n        2 => 2,\n    }\n}\n");
    assert!(out.contains("`i32` is not taken"), "{}", out);
    clean("fn f(n: i32): i32 {\n    match n {\n        1 => 1,\n        _ => 2,\n    }\n}\n");
}

// Two values, and both have to be written.
#[test]
fn a_bool_is_taken_by_both_of_it() {
    clean("fn f(c: bool): i32 {\n    match c {\n        true => 1,\n        false => 2,\n    }\n}\n");
    let out = refused("fn f(c: bool): i32 {\n    match c {\n        true => 1,\n    }\n}\n");
    assert!(out.contains("`false` is not taken"), "{}", out);
}

// What a variant carries is followed where it carries one thing.
#[test]
fn what_one_variant_carries_is_followed() {
    let with = "enum E {\n    A,\n    B(bool),\n}\n";
    // Both of the `bool` it carries, so `B` is taken.
    clean(&format!(
        "{}fn f(e: E): i32 {{\n    match e {{\n        E::A => 0,\n        E::B(true) => 1,\n        E::B(false) => 2,\n    }}\n}}\n",
        with
    ));
    // Only one of them, so it is not.
    let out = refused(&format!(
        "{}fn f(e: E): i32 {{\n    match e {{\n        E::A => 0,\n        E::B(true) => 1,\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("`E::B` is not taken"), "{}", out);
    // And a `_` where it carries takes the whole variant.
    clean(&format!(
        "{}fn f(e: E): i32 {{\n    match e {{\n        E::A => 0,\n        E::B(_) => 1,\n    }}\n}}\n",
        with
    ));
}

// A tuple and a struct each have one shape, so a pattern that takes everything
// in every place takes the whole of it.
#[test]
fn a_tuple_and_a_struct_are_taken_by_binding_them() {
    clean("fn f(p: (i32, str)): str {\n    match p {\n        (n, s) => s,\n    }\n}\n");
    clean(
        "struct P {\n    pub x: i32,\n    pub y: i32,\n}\n\
         fn f(p: P): i32 {\n    match p {\n        P { x } => x,\n    }\n}\n",
    );
    // But a member that tests does not.
    let out = refused("fn f(p: (i32, str)): str {\n    match p {\n        (0, s) => s,\n    }\n}\n");
    assert!(out.contains("does not take everything"), "{}", out);
}

// An arm below one that takes everything is never reached. A warning: the
// program means something, and what it means is that the arm is dead.
#[test]
fn an_arm_below_a_catch_all_is_never_reached() {
    let out = refused(
        "enum Color {\n    Red,\n    Green,\n}\n\
         fn f(c: Color): i32 {\n    match c {\n        other => 1,\n        Color::Red => 2,\n    }\n}\n",
    );
    assert!(out.contains("warning: this arm is never reached"), "{}", out);
    assert!(out.contains("an arm above takes everything"), "{}", out);
    // And it is a warning and not a refusal: the program still means something.
    assert!(!out.contains("error:"), "{}", out);
}

// The one place this asks for more than it has to: a variant carrying several
// things is taken only by an arm that takes everything in every place. It is
// written down here so that sharpening it breaks a test rather than going
// unnoticed.
#[test]
fn a_variant_carrying_several_things_wants_one_arm_that_takes_them_all() {
    let with = "enum E {\n    P(bool, bool),\n}\n";
    clean(&format!(
        "{}fn f(e: E): i32 {{\n    match e {{\n        E::P(a, b) => 1,\n    }}\n}}\n",
        with
    ));
    // Four arms that between them take every pair, and this does not see it.
    let out = refused(&format!(
        "{}fn f(e: E): i32 {{\n    match e {{\n\
         \x20       E::P(true, true) => 1,\n\
         \x20       E::P(true, false) => 2,\n\
         \x20       E::P(false, true) => 3,\n\
         \x20       E::P(false, false) => 4,\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("`E::P` is not taken"), "{}", out);
}

// ---- Regions ---------------------------------------------------------------

// The fn a name belongs to, and the region every reference in its signature
// stands in, parameters first and the return last.
fn signature(ttir: &TTIRProgram, name: &str) -> (Vec<usize>, Vec<usize>, Vec<(usize, usize)>) {
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == name => Some(f),
        _ => None,
    }).expect("the fn");
    let lives = |ty: usize| match &ttir.types[ty] {
        Ty::Ref { life, .. } => vec![*life],
        _ => Vec::new(),
    };
    let Ty::Fn { params, ret, .. } = &ttir.types[f.ty] else { panic!("a fn type") };
    let brought = params.iter().flat_map(|&p| lives(p)).collect();
    (brought, lives(*ret), f.outlives.clone())
}

// "Every reference in a signature with no lifetime of its own gets one, and a
// reference in the return type gets the shortest-lived of the ones the
// parameters brought in" (§3). Three references, three regions, and the return
// is outlived by both of the others.
#[test]
fn a_signature_with_nothing_written_gets_its_regions_worked_out() {
    let ttir = clean("fn pick(x: &str, y: &str): &str {\n    x\n}\n");
    let (brought, given, outlives) = signature(&ttir, "pick");
    assert_eq!(brought, vec![1, 2]);
    assert_eq!(given, vec![3]);
    // Not "the shorter of the two", which is not a region: both of them
    // outlive the result, which says the same thing and can be checked.
    assert_eq!(outlives, vec![(1, 3), (2, 3)]);
}

// "Writing a lifetime ... is only ever a sharpening: `fn first<'a>(x: &'a str,
// y: &str): &'a str` says the result outlives y, which the rule alone would not
// have said" (§3). So `x` and the result are one region, `y` is another, and
// the rule adds nothing on top.
#[test]
fn a_written_lifetime_is_one_region_in_two_places() {
    let ttir = clean("fn first<'a>(x: &'a str, y: &str): &'a str {\n    x\n}\n");
    let (brought, given, outlives) = signature(&ttir, "first");
    assert_eq!(brought, vec![1, 2]);
    assert_eq!(given, vec![1]);
    assert!(outlives.is_empty(), "{:?}", outlives);
}

// A signature holding no reference has nothing to say about regions, and a
// signature whose references are all in the parameters has nothing either.
#[test]
fn a_signature_with_nothing_to_tie_ties_nothing() {
    let ttir = clean("fn none(x: i32): i32 {\n    x\n}\nfn takes(x: &str): i32 {\n    1\n}\n");
    assert_eq!(signature(&ttir, "none"), (vec![], vec![], vec![]));
    assert_eq!(signature(&ttir, "takes"), (vec![1], vec![], vec![]));
}

// Region 0 is what a reference outside a signature gets: how long one held in a
// local is good for is not what a signature promises, and nothing asks yet.
#[test]
fn a_reference_in_a_body_stands_in_no_region_of_the_signature() {
    let ttir = clean("fn f(): i32 {\n    let x = 1;\n    let r: &i32 = &x;\n    1\n}\n");
    let lives: Vec<usize> = ttir.bodies[0]
        .locals
        .iter()
        .filter_map(|l| match &ttir.types[l.ty] {
            Ty::Ref { life, .. } => Some(*life),
            _ => None,
        })
        .collect();
    assert_eq!(lives, vec![0]);
}

// A lifetime nothing declares is refused where it is written. The rule never
// fails for want of one, so the only way to get here is to have written it.
#[test]
fn a_lifetime_nothing_declares_is_refused() {
    let out = refused("fn f<'a>(x: &'b str): i32 {\n    1\n}\n");
    assert!(out.contains("no lifetime is called `'b`"), "{}", out);
    assert!(out.contains("nothing declares it"), "{}", out);
}

// A lifetime bounding a type, `T: 'a`, and a lifetime bounding a lifetime,
// `'a: 'b`, both name a region the declaration declared -- so both of them read
// as that region, and neither is left standing for nothing.
#[test]
fn a_lifetime_written_in_a_bound_is_the_region_it_names() {
    let ttir = clean(
        "fn f<'a, 'b, T: 'a>(x: &'a T, y: &'b T): &'a T where 'a: 'b {\n    x\n}\n",
    );
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "f" => Some(f),
        _ => None,
    }).expect("f");
    // `'a` is region 1, `'b` is region 2 -- lifetimes are numbered in the order
    // they were declared, before any reference gets one of its own.
    assert_eq!(
        f.generics[0],
        TTIRGeneric::Life { name: "a".to_string(), region: 1, bounds: Vec::new() },
    );
    assert_eq!(
        f.generics[1],
        TTIRGeneric::Life { name: "b".to_string(), region: 2, bounds: Vec::new() },
    );
    // `T: 'a` holds T to region 1.
    assert_eq!(
        f.generics[2],
        TTIRGeneric::Type { name: "T".to_string(), bounds: vec![TTIRBound::Life(1)] },
    );
    // And `where 'a: 'b` is a predicate with no parameter to fold into, since
    // its subject is a region and not a type.
    assert_eq!(f.wheres.len(), 1);
    assert_eq!(f.wheres[0].subject, TTIRSubject::Region(1));
    assert_eq!(f.wheres[0].bounds, vec![TTIRBound::Life(2)]);
}

// A lifetime nothing declares is refused wherever it is written, and a bound is
// one of the places it can be written.
#[test]
fn an_undeclared_lifetime_in_a_bound_is_refused() {
    let out = refused("fn f<T: 'z>(x: T): i32 {\n    1\n}\n");
    assert!(out.contains("no lifetime is called `'z`"), "{}", out);
}

// A lifetime handed to a type as an argument is checked and then dropped:
// `Ty::Named` holds types, and what a `Ref<'a>` promises about its insides is
// nothing this pass compares. What it is not is unchecked.
#[test]
fn a_lifetime_handed_to_a_type_is_still_checked() {
    clean("struct Held<'a, T> {\n    pub it: &'a T,\n}\n\
           fn f<'a>(h: Held<'a, i32>): i32 {\n    1\n}\n");
    let out = refused(
        "struct Held<'a, T> {\n    pub it: &'a T,\n}\n\
         fn f(h: Held<'q, i32>): i32 {\n    1\n}\n",
    );
    assert!(out.contains("no lifetime is called `'q`"), "{}", out);
}

// A reference rooted at a local of the body stands in no region of the
// signature: it is good until the block that declared it ends, and the return
// type promises longer. This is the hole `borrows.rs` used to document.
#[test]
fn a_reference_to_a_local_may_not_leave_the_body() {
    let out = refused("fn f(): &i32 {\n    let x = 1;\n    &x\n}\n");
    assert!(out.contains("`x` does not live long enough"), "{}", out);
    assert!(out.contains("this gives back a reference to it"), "{}", out);
    // On the line the reference was written, and not on the signature.
    assert!(out.contains("3 |     &x"), "{}", out);
}

// And handing it through a name changes nothing: a reference is followed to
// what it was taken from, however many slots it has sat in.
#[test]
fn a_reference_handed_through_a_name_is_still_followed() {
    let out = refused("fn f(): &i32 {\n    let x = 1;\n    let r = &x;\n    r\n}\n");
    assert!(out.contains("`x` does not live long enough"), "{}", out);
    // Three lines: where it leaves, where the `&` was written, where x was bound.
    assert!(out.contains("4 |     r"), "{}", out);
    assert!(out.contains("the reference was taken here"), "{}", out);
    assert!(out.contains("it was bound here"), "{}", out);
}

// A reference the caller handed in goes on living where it lives, so giving it
// back is what the elision rule says a signature may always do.
#[test]
fn a_reference_the_caller_brought_may_go_back_out() {
    clean("fn f(p: &i32): &i32 {\n    p\n}\n");
    clean("struct P {\n    pub x: i32,\n}\nfn f(p: &P): &i32 {\n    &p.x\n}\n");
    clean("fn f(p: &i32): &i32 {\n    let r = p;\n    r\n}\n");
}

// "a reference in the return type gets the shortest-lived of the ones the
// parameters brought in" (§3), read from the caller's side: what a call gives
// back may point into anything that was handed to it.
#[test]
fn what_a_call_gives_back_points_where_its_arguments_did() {
    let out = refused(
        "fn pick(a: &i32, b: &i32): &i32 {\n    a\n}\n\
         fn f(p: &i32): &i32 {\n    let x = 1;\n    pick(p, &x)\n}\n",
    );
    assert!(out.contains("`x` does not live long enough"), "{}", out);
    // And the same call with nothing local in it is fine.
    clean(
        "fn pick(a: &i32, b: &i32): &i32 {\n    a\n}\n\
         fn f(p: &i32, q: &i32): &i32 {\n    pick(p, q)\n}\n",
    );
}

// A `return` is checked where it stands, since what follows it is not walked.
#[test]
fn a_returned_reference_to_a_local_is_refused_where_it_returns() {
    let out = refused("fn f(c: bool): &i32 {\n    let x = 1;\n    if c {\n        return &x;\n    }\n    return &x;\n}\n");
    assert!(out.contains("`x` does not live long enough"), "{}", out);
    assert!(out.contains("4 |         return &x;"), "{}", out);
}

// A signature that gives back no reference has no region to break, whatever its
// body does with the ones it takes.
#[test]
fn a_body_that_gives_back_no_reference_is_asked_nothing() {
    clean("fn f(): i32 {\n    let x = 1;\n    let r = &x;\n    1\n}\n");
}

// ---- Regions at the call ---------------------------------------------------

// "What the rule costs is precision, and it spends it at the call rather than
// at the declaration. A `pick` that only ever gives back x is held to y as
// well, so a caller whose y dies first is refused" (§3). This is that, and it
// is the whole bargain in one pair of fns.
#[test]
fn a_caller_is_held_to_every_parameter_the_result_is_tied_to() {
    let with = "fn pick(a: &i32, b: &i32): &i32 {\n    a\n}\n";
    let out = refused(&format!(
        "{}fn f(p: &i32): &i32 {{\n    let x = 1;\n    pick(p, &x)\n}}\n",
        with
    ));
    assert!(out.contains("`x` does not live long enough"), "{}", out);
}

// "Writing a lifetime is how the precision comes back ... `fn first<'a>(x: &'a
// str, y: &str): &'a str` says the result outlives y, which the rule alone
// would not have said, and every caller is held to that instead of to the
// shorter of the two" (§3). The same caller, and now it stands.
#[test]
fn a_written_lifetime_is_what_the_caller_gets_the_precision_from() {
    clean(
        "fn first<'a>(a: &'a i32, b: &i32): &'a i32 {\n    a\n}\n\
         fn f(p: &i32): &i32 {\n    let x = 1;\n    first(p, &x)\n}\n",
    );
}

// A fn whose result is no reference ties its caller to nothing, whatever it was
// handed. Otherwise every `len(&x)` would pin `x` to wherever the answer went.
#[test]
fn a_result_that_is_no_reference_ties_nothing() {
    clean(
        "fn len(s: &i32): i32 {\n    1\n}\n\
         fn f(p: &i32): &i32 {\n    let x = 1;\n    let n = len(&x);\n    p\n}\n",
    );
}

// The refusal with nothing being returned: a slot may not be given a reference
// to something that goes before it does. Depth is the ordering -- a block
// inside a block is shorter-lived, which is what "a local at the end of its
// block" (§2) comes to.
#[test]
fn a_slot_may_not_be_given_a_reference_that_goes_before_it() {
    let out = refused(
        "fn f(p: &i32) {\n    var r = p;\n    {\n        let inner = 2;\n\
         \x20       r = &inner;\n    }\n}\n",
    );
    assert!(out.contains("`inner` does not live long enough"), "{}", out);
    assert!(out.contains("this puts a reference to it somewhere longer-lived"), "{}", out);
    assert!(out.contains("5 |         r = &inner;"), "{}", out);
}

// And through a call, which is where the two halves meet: `pick` ties its
// result to both, so `inner` reaches `r` and `r` outlives the block.
#[test]
fn a_call_in_an_assignment_is_held_to_what_its_result_is_tied_to() {
    let with = "fn pick(a: &i32, b: &i32): &i32 {\n    a\n}\n";
    let out = refused(&format!(
        "{}fn f(p: &i32) {{\n    var r = p;\n    {{\n        let inner = 2;\n\
         \x20       r = pick(p, &inner);\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("`inner` does not live long enough"), "{}", out);
    // Two arguments and one of them is fine: the same call with nothing
    // short-lived in it stands.
    clean(&format!(
        "{}fn f(p: &i32, q: &i32) {{\n    var r = p;\n    {{\n\
         \x20       r = pick(p, q);\n    }}\n}}\n",
        with
    ));
}

// A block gives back its tail, so a reference taken inside one does not get out
// by being the value of a `let`.
#[test]
fn a_reference_does_not_leave_a_block_by_being_its_value() {
    let out = refused(
        "fn f() {\n    let r = {\n        let inner = 2;\n        &inner\n    };\n}\n",
    );
    assert!(out.contains("`inner` does not live long enough"), "{}", out);
    // Pointing at the `&`, which is the line that did it.
    assert!(out.contains("4 |         &inner"), "{}", out);
}

// One mistake is one message. A reference put in a slot that outlives it and
// then given back out of the body is one thing gone wrong said twice, and the
// first place is the one worth reading.
#[test]
fn a_reference_that_outstays_twice_is_refused_once() {
    let out = refused(
        "fn f(): &i32 {\n    let r = {\n        let inner = 2;\n        &inner\n    };\n    r\n}\n",
    );
    assert_eq!(out.matches("does not live long enough").count(), 1, "{}", out);
}

// A method's receiver stands where parameter 0 does, and the prose names this
// case: "`fn name(&self, sep: &str): &str` ties its result to sep as well as to
// the receiver, though what a method gives back is almost always the
// receiver's. Rust spends a whole elision rule on that one case; this spends
// none, and the method that wants it says so" (§3).
#[test]
fn a_method_ties_its_result_to_its_arguments_as_well_as_its_receiver() {
    let with = "struct S {\n    pub x: i32,\n}\n\
                impl S {\n    pub fn name(&self, sep: &i32): &i32 {\n        &self.x\n    }\n}\n";
    let out = refused(&format!(
        "{}fn f(s: &S): &i32 {{\n    let sep = 1;\n    s.name(&sep)\n}}\n",
        with
    ));
    assert!(out.contains("`sep` does not live long enough"), "{}", out);
}

// And the method that wants the precision says so: "Rust spends a whole elision
// rule on that one case; this spends none, and the method that wants it says
// so" (§3). One written `'a` on the receiver and the caller is held to the
// receiver alone.
#[test]
fn a_receiver_may_name_its_own_region() {
    clean(
        "struct S {\n    pub x: i32,\n}\n\
         impl S {\n    pub fn name<'a>(&'a self, sep: &i32): &'a i32 {\n        &self.x\n    }\n}\n\
         fn f(s: &S): &i32 {\n    let sep = 1;\n    s.name(&sep)\n}\n",
    );
}

// A receiver with no lifetime of its own gets one all the same -- it is a
// reference in a signature like any other -- so a method's result is tied to it
// and returning `&self.x` is what a method almost always does.
#[test]
fn a_receiver_with_nothing_written_is_still_a_region() {
    let ttir = clean(
        "struct S {\n    pub x: i32,\n}\n\
         impl S {\n    pub fn get(&self): &i32 {\n        &self.x\n    }\n}\n",
    );
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "get" => Some(f),
        _ => None,
    }).expect("get");
    // Region 1 is the receiver's, 2 is the result's, and the first outlives the
    // second -- which is the elision rule with one parameter to work from.
    assert_eq!(f.outlives, vec![(1, 2)]);
}

// ---- Closure captures ------------------------------------------------------

// "a closure that captures by reference cannot outlive what it captured, and
// `move` is the only thing that lets one be returned" (§8). A closure is the
// one value here whose type says nothing about what is inside it, so what it
// points into is read off its captures and not off `fn(): i32`.
#[test]
fn a_closure_that_captured_by_reference_may_not_outlive_what_it_captured() {
    let out = refused(
        "fn f() {\n    var c = || 1;\n    {\n        let n = 2;\n\
         \x20       c = || n;\n    }\n}\n",
    );
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(out.contains("5 |         c = || n;"), "{}", out);
}

// And `move` is what lets it out: by value the slot is not pointed at, so there
// is nothing left in the block for the closure to outlive.
#[test]
fn a_move_closure_is_what_lets_one_out() {
    clean(
        "fn f() {\n    var c = || 1;\n    {\n        let n = 2;\n\
         \x20       c = move || n;\n    }\n}\n",
    );
}

// A closure is a value like any other, so a block does not let one out by being
// the value of a `let` either.
#[test]
fn a_closure_does_not_leave_a_block_by_being_its_value() {
    let out = refused("fn f() {\n    let c = {\n        let n = 2;\n        || n\n    };\n}\n");
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(out.contains("4 |         || n"), "{}", out);
}

// What was taken by value is followed only as far as that value went: a `move`
// closure holding a reference points where the reference pointed, and not at
// the slot the reference sat in.
#[test]
fn a_captured_value_is_followed_as_far_as_it_points() {
    let out = refused(
        "fn f(p: &i32) {\n    var c = move || p;\n    {\n        let n = 2;\n\
         \x20       let r = &n;\n        c = move || r;\n    }\n}\n",
    );
    // `n`, which `r` points at -- and not `r`, which was copied into the closure.
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(!out.contains("`r` does not live long enough"), "{}", out);
}

// And what was taken by reference is followed one step further: the closure
// holds a reference to the slot, so the slot has to last, and so does whatever
// reading through it reaches.
#[test]
fn a_captured_reference_holds_the_slot_as_well_as_what_it_points_at() {
    let out = refused(
        "fn f(p: &i32) {\n    var c = move || p;\n    {\n        let n = 2;\n\
         \x20       let r = &n;\n        c = || r;\n    }\n}\n",
    );
    assert!(out.contains("`r` does not live long enough"), "{}", out);
    assert!(out.contains("`n` does not live long enough"), "{}", out);
}

// A closure that captured nothing points at nothing, whatever it is put in.
#[test]
fn a_closure_that_captured_nothing_may_go_anywhere() {
    clean("fn f() {\n    var c = || 1;\n    {\n        c = || 2;\n    }\n}\n");
}
