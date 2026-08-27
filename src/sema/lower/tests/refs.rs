// What carries a reference, which is what decides whether a region check has
// anything to ask at all.

use super::*;

// ---- What carries a reference ----------------------------------------------

// A value built out of references points where they did, whatever was built.
// A tuple was followed from the start; a struct, a variant, a map, a set and a
// range are the rest of them.
#[test]
fn every_aggregate_is_followed_to_what_it_was_built_from() {
    let with = "struct Held<'a> {\n    pub it: &'a i32,\n}\n\
                enum E<'a> {\n    Some(&'a i32),\n    None,\n}\n";
    for (ret, built) in [
        ("Held", "Held { it: &n }"),
        ("E", "E::Some(&n)"),
        ("(&i32, i32)", "(&n, 1)"),
        ("(&i32)[1]", "[&n]"),
    ] {
        let out = refused(&format!(
            "{}fn f(): {} {{\n    let n = 1;\n    {}\n}}\n",
            with, ret, built
        ));
        assert!(out.contains("`n` does not live long enough"), "{} -- {}", built, out);
    }
    // And each of them built out of what the caller handed in still stands.
    clean(&format!(
        "{}fn f(p: &i32): Held {{\n    Held {{ it: p }}\n}}\n\
         fn g(p: &i32): E {{\n    E::Some(p)\n}}\n",
        with
    ));
}

// A named type holds a reference where its *declaration* does. The regions are
// the declaration's and not the use's, so a `Held` written bare carries the
// same reference a `Held<'a>` does -- which is what lets this see one at all,
// since `Ty::Named` keeps no regions of its own.
#[test]
fn a_named_type_carries_what_it_was_declared_to_carry() {
    let out = refused(
        "struct Inner<'a> {\n    pub it: &'a i32,\n}\n\
         struct Outer<'a> {\n    pub inner: Inner<'a>,\n}\n\
         fn f(): Outer {\n    let n = 1;\n    Outer { inner: Inner { it: &n } }\n}\n",
    );
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    // A named type carrying nothing carries nothing, however it is built.
    clean(
        "struct Plain {\n    pub x: i32,\n}\n\
         fn f(): Plain {\n    let n = 1;\n    Plain { x: n }\n}\n",
    );
}

// A fn whose result is a named type carrying a reference is tied to every one
// of its parameters. The regions cannot be compared -- `Ty::Named` lost them --
// so the answer is the one §3 gives before anybody writes a lifetime: hold the
// caller to everything, which is never wrong.
#[test]
fn a_named_result_ties_a_caller_to_everything() {
    let with = "struct Held<'a> {\n    pub it: &'a i32,\n}\n\
                fn make(p: &i32): Held {\n    Held { it: p }\n}\n";
    let out = refused(&format!(
        "{}fn f(): Held {{\n    let n = 1;\n    make(&n)\n}}\n",
        with
    ));
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    clean(&format!("{}fn f(p: &i32): Held {{\n    make(p)\n}}\n", with));
}

// A name a pattern binds came out of what was matched on, so it points wherever
// that did. Not *at* it: what `opt` held is what comes out, and a reference
// `opt` was built from is a reference the arm gives back.
#[test]
fn a_name_bound_by_a_pattern_points_where_the_scrutinee_did() {
    let with = "enum E<'a> {\n    Some(&'a i32),\n    None,\n}\n";
    let out = refused(&format!(
        "{}fn f(p: &i32): &i32 {{\n    let n = 1;\n    let e = E::Some(&n);\n\
         \x20   match e {{\n        E::Some(v) => v,\n        E::None => p,\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    // Built out of what the caller handed in, the same arm gives back something
    // that outlives the body -- which is why the scrutinee's own slot is not a
    // root: `e` is a local, and holding the arm to `e` would refuse this.
    clean(&format!(
        "{}fn f(p: &i32): &i32 {{\n    let e = E::Some(p);\n\
         \x20   match e {{\n        E::Some(v) => v,\n        E::None => p,\n    }}\n}}\n",
        with
    ));
}

// And a loop variable comes out of what is being gone through, the same way.
#[test]
fn a_loop_variable_points_where_what_it_goes_through_did() {
    let out = refused(
        "fn f(): &i32 {\n    let a = 1;\n    let things = [&a];\n\
         \x20   for v in things {\n        return v;\n    }\n    &a\n}\n",
    );
    assert!(out.contains("`a` does not live long enough"), "{}", out);
    clean(
        "fn f(p: &i32): &i32 {\n    let things = [p];\n\
         \x20   for v in things {\n        return v;\n    }\n    p\n}\n",
    );
}

// ---- The regions a named type carries --------------------------------------

// A named type is handed one region per lifetime its declaration takes, written
// or not: "every reference in a signature with no lifetime of its own gets one"
// (§3) reaches a type that carries references and not only a reference.
#[test]
fn a_named_type_is_handed_a_region_for_every_lifetime_it_takes() {
    let with = "struct Held<'a> {\n    pub it: &'a i32,\n}\n";
    // Nothing written: the reference is region 1 and the `Held` gets region 2,
    // and the rule ties the second to the first.
    let ttir = clean(&format!(
        "{}fn make(p: &i32): Held {{\n    Held {{ it: p }}\n}}\n",
        with
    ));
    let (brought, given, outlives) = signature(&ttir, "make");
    assert_eq!(brought, vec![1]);
    assert!(given.is_empty(), "the return is a named type and not a reference");
    assert_eq!(outlives, vec![(1, 2)]);
}

// And a written one is the same sharpening it is anywhere else: `Held<'a>` ties
// the result to `p` and leaves `q` out of it.
#[test]
fn a_written_lifetime_sharpens_a_named_result_too() {
    let with = "struct Held<'a> {\n    pub it: &'a i32,\n}\n";
    let out = refused(&format!(
        "{}fn loose(p: &i32, q: &i32): Held {{\n    Held {{ it: p }}\n}}\n\
         fn f(p: &i32): Held {{\n    let n = 1;\n    loose(p, &n)\n}}\n",
        with
    ));
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    clean(&format!(
        "{}fn tight<'a>(p: &'a i32, q: &i32): Held<'a> {{\n    Held {{ it: p }}\n}}\n\
         fn f(p: &i32): Held {{\n    let n = 1;\n    tight(p, &n)\n}}\n",
        with
    ));
}

// A declaration that names no lifetime has no region to carry, and a fn whose
// result is such a type is held to everything -- the elision rule's own answer,
// which is never wrong and is what there is to say without a slot to say it in.
#[test]
fn a_declaration_that_names_no_lifetime_is_held_to_everything() {
    let out = refused(
        "struct Held {\n    pub it: &i32,\n}\n\
         fn make(p: &i32, q: &i32): Held {\n    Held { it: p }\n}\n\
         fn f(p: &i32): Held {\n    let n = 1;\n    make(p, &n)\n}\n",
    );
    assert!(out.contains("`n` does not live long enough"), "{}", out);
}

// Two `Held`s agree whatever regions they stand in: "a type that agrees but for
// its regions is a type that agrees", which is what `unify` already does for a
// reference and now does for what carries one.
#[test]
fn two_named_types_agree_whatever_regions_they_stand_in() {
    clean(
        "struct Held<'a> {\n    pub it: &'a i32,\n}\n\
         fn f<'a, 'b>(x: Held<'a>, y: Held<'b>, c: bool): Held<'a> {\n\
         \x20   if c {\n        x\n    } else {\n        x\n    }\n}\n",
    );
}

// ---- Fn types --------------------------------------------------------------

// "a closure that captures by reference cannot outlive what it captured, and
// `move` is the only thing that lets one be returned" (§8). The second half of
// that, now that there is somewhere to return one to.
#[test]
fn a_closure_that_captured_by_reference_may_not_be_returned() {
    let out = refused("fn f(): fn(): i32 {\n    let n = 2;\n    || n\n}\n");
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    // `move` takes the value, so there is nothing left behind to outlive.
    clean("fn f(): fn(): i32 {\n    let n = 2;\n    move || n\n}\n");
    // And one that captured nothing may go anywhere.
    clean("fn f(): fn(): i32 {\n    || 1\n}\n");
}

// A fn type stands where any type does: a parameter, a return, a field.
#[test]
fn a_fn_type_stands_where_a_type_does() {
    let ttir = clean(
        "fn takes(f: fn(i32): i32): i32 {\n    1\n}\n\
         struct Holds {\n    pub f: fn(): i32,\n}\n\
         fn gives(): fn(i32, str): bool {\n    |x, s| true\n}\n",
    );
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "gives" => Some(f),
        _ => None,
    }).expect("gives");
    let Ty::Fn { params, ret, is_unsafe, .. } = &ttir.types[f.ret] else { panic!("a fn type") };
    assert_eq!(params.len(), 2);
    assert_eq!(ttir.types[params[0]], Ty::Prim(TIRPrim::I32));
    assert_eq!(ttir.types[params[1]], Ty::Prim(TIRPrim::Str));
    assert_eq!(ttir.types[*ret], Ty::Prim(TIRPrim::Bool));
    // "there is no spelling for an unsafe fn type."
    assert!(!is_unsafe);
}

// "a `<return_type_opt>` left out is `null`" (§2) reaches a written fn type as
// much as a written fn.
#[test]
fn a_fn_type_with_no_return_gives_back_null() {
    let ttir = clean("fn takes(f: fn(i32)): i32 {\n    1\n}\n");
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "takes" => Some(f),
        _ => None,
    }).expect("takes");
    let Ty::Fn { params, .. } = &ttir.types[f.ty] else { panic!("a fn type") };
    let Ty::Fn { ret, .. } = &ttir.types[params[0]] else { panic!("a fn type") };
    assert_eq!(ttir.types[*ret], Ty::Prim(TIRPrim::Null));
}

// The suffix binds to the type inside the return, so `fn(): i32[8]` gives back
// eight numbers and `(fn(): i32)[8]` is eight closures.
#[test]
fn an_array_suffix_binds_inside_a_fn_types_return() {
    let ttir = clean(
        "fn a(f: fn(): i32[8]): i32 {\n    1\n}\n\
         fn b(f: (fn(): i32)[8]): i32 {\n    1\n}\n",
    );
    let of = |name: &str| {
        let f = ttir.items.iter().find_map(|i| match &i.kind {
            TTIRItemKind::Fn(f) if f.name == name => Some(f),
            _ => None,
        }).expect("the fn");
        let Ty::Fn { params, .. } = &ttir.types[f.ty] else { panic!("a fn type") };
        params[0]
    };
    // `a` takes a fn giving back an array.
    assert!(matches!(&ttir.types[of("a")], Ty::Fn { .. }));
    // `b` takes an array of fns.
    assert!(matches!(&ttir.types[of("b")], Ty::Array { .. }));
}
