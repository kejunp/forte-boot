// What a `::` spells, and the arguments hanging off what it found.

use super::*;

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
