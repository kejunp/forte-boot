// Regions: the ones a signature did not write, and holding a caller to the
// ones it did.

use super::*;

// ---- Regions ---------------------------------------------------------------

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
