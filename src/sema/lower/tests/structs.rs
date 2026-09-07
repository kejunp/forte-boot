// Struct literals, held to the declaration field by field.

use super::*;

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

// ---- A brace after a path ----------------------------------------------------------

// The name in front of the brace is a `::` chain like any other name, and only
// the one-word spelling was taken. So a struct declared in a namespace could be
// reached, called and named in a signature, and could not be *built*: what it
// got was "a struct literal whose head is not a name".
#[test]
fn a_struct_reached_through_a_path_is_built() {
    clean(
        "namespace held {\n    pub struct Point {\n        pub x: i32,\n    }\n}\n\
         fn f(): held::Point { held::Point { x: 1 } }\n",
    );
}

// And a variant that names what it carries, which is the same brace over a
// different declaration: `E::Three { x: 5 }` builds the variant exactly as
// `E::Two(5)` builds the one that names nothing. It could be declared and
// matched and not built.
#[test]
fn a_variant_that_names_what_it_carries_is_built() {
    let with = "enum E {\n    One,\n    Two(i32),\n    Three { x: i32, y: bool },\n}\n";
    clean(&format!("{}fn f(): E {{ E::Three {{ x: 5, y: true }} }}\n", with));
    // Held to the same three things a struct literal is held to.
    let out = refused(&format!("{}fn f(): E {{ E::Three {{ x: 5 }} }}\n", with));
    assert!(out.contains("`Three` is missing y"), "{}", out);
    let out = refused(&format!("{}fn f(): E {{ E::Three {{ x: 5, y: true, z: 1 }} }}\n", with));
    assert!(out.contains("has no field `z`"), "{}", out);
    let out = refused(&format!("{}fn f(): E {{ E::Three {{ x: 5, x: 6, y: true }} }}\n", with));
    assert!(out.contains("`x` is given twice"), "{}", out);
    // And one that names nothing is not built by name.
    let out = refused(&format!("{}fn f(): E {{ E::Two {{ x: 5 }} }}\n", with));
    assert!(out.contains("does not name what it carries"), "{}", out);
}
