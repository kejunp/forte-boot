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

// ---- What a call carries about the callee -----------------------------------------

// A call to a generic writes down what it made the callee's type parameters
// stand for. It did not, and `mir::mono` worked the same answer out again a
// pass later by matching the declaration's signature against the types the SIR
// values beside the call had -- inference done twice, the second time on an
// answer lowering is free to have rewritten.
//
// Lowering does rewrite it: `promote` replacing a load with the value that was
// stored is the ordinary case, and the two need not agree. Three wrong programs
// came out of that seam and the last was a segmentation fault.
fn types_on_calls(source: &str) -> Vec<usize> {
    let ttir = clean(source);
    ttir.exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Call { types, .. } => Some(types.len()),
            _ => None,
        })
        .collect()
}

#[test]
fn a_call_says_what_it_made_the_callees_parameters_stand_for() {
    // Worked out from the argument,
    assert_eq!(
        types_on_calls("fn id<T>(x: T): T { x }\nfn f(): i32 { id(1) }\n"),
        vec![1]
    );
    // written by hand, which settles them before the call is reached and so
    // leaves nothing in the type for the call to work back out,
    assert_eq!(
        types_on_calls("fn id<T>(x: T): T { x }\nfn f(): i32 { id<i32>(1) }\n"),
        vec![1]
    );
    // two of them,
    assert_eq!(
        types_on_calls(
            "fn two<A, B>(a: A, b: B): A { a }\nfn f(): i32 { two(1, true) }\n"
        ),
        vec![2]
    );
    // and none, which is every other call there is.
    assert_eq!(
        types_on_calls("fn plain(x: i32): i32 { x }\nfn f(): i32 { plain(1) }\n"),
        vec![0]
    );
}

// A method says it too, and says the same thing: what its own parameters and
// its impl's were made to stand for.
#[test]
fn a_method_says_it_as_well() {
    let ttir = clean(
        "struct Box<T> {\n    pub held: T,\n}\n\
         impl<T> Box<T> {\n    fn get(&self): T { self.held }\n}\n\
         fn f(): i32 {\n    let b = Box { held: 1 }\n    b.get()\n}\n",
    );
    let held: Vec<usize> = ttir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Method { types, .. } => Some(types.len()),
            _ => None,
        })
        .collect();
    assert_eq!(held, vec![1], "the impl's `T`, said at the call");
}
