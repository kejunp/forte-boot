// `match`: what a pattern means, and whether a list of them leaves anything
// out.

use super::*;

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
