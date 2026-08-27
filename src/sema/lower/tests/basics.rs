// The tree that comes out, and the programs that do not get one.

use super::*;

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
