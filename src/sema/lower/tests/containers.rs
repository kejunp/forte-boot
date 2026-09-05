// The map, set and range literals, and the types a library has to declare for
// them to build.

use super::*;

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

// ---- Generic types -----------------------------------------------------------

// A generic built by a literal carries what it was built with. Without this a
// `Held { v: 1 }` was typed as a bare `Held`, and the two do not unify -- so a
// generic struct could not be handed to anything that asked for one, which is
// to say a generic struct could not be used at all.
#[test]
fn a_generic_struct_carries_what_it_was_built_with() {
    let with = "struct Held<T> {\n    pub v: T,\n}\n";
    clean(&format!(
        "{}fn f(): Held<i32> {{\n    Held {{ v: 1 }}\n}}\n",
        with
    ));
}

// And what comes out of it is what went in, not the declaration's `T`.
#[test]
fn reading_a_field_of_a_generic_gives_the_type_it_was_built_with() {
    let with = "struct Held<T> {\n    pub v: T,\n}\n";
    clean(&format!("{}fn f(h: Held<i32>): i32 {{\n    h.v\n}}\n", with));
    let out = refused(&format!("{}fn f(h: Held<i32>): i64 {{\n    h.v\n}}\n", with));
    assert!(out.contains("i32"), "{}", out);
}

#[test]
fn two_uses_of_one_generic_are_two_types() {
    let with = "struct Held<T> {\n    pub v: T,\n}\n";
    let out = refused(&format!(
        "{}fn f(a: Held<i32>): Held<i64> {{\n    a\n}}\n",
        with
    ));
    assert!(out.contains("Held<i32>") && out.contains("Held<i64>"), "{}", out);
}

// The same omission was at every place a named type is made, and a variant is
// one of them: `Option::Some(1)` has to be an `Option<i32>`.
#[test]
fn a_generic_variant_carries_what_it_was_built_with() {
    let with = "enum Option<T> {\n    None,\n    Some(T),\n}\n";
    clean(&format!(
        "{}fn f(): Option<i64> {{\n    Option::Some(1)\n}}\n",
        with
    ));
}

// And a pattern that tests one binds what it really holds.
#[test]
fn matching_a_generic_variant_binds_the_type_it_holds() {
    let with = "enum Option<T> {\n    None,\n    Some(T),\n}\n";
    clean(&format!(
        "{}fn f(o: Option<i64>): i64 {{\n    match o {{\n\
         \x20       Option::Some(v) => v,\n        Option::None => 0,\n    }}\n}}\n",
        with
    ));
    let out = refused(&format!(
        "{}fn f(o: Option<i64>): i32 {{\n    match o {{\n\
         \x20       Option::Some(v) => v,\n        Option::None => 0,\n    }}\n}}\n",
        with
    ));
    assert!(!out.is_empty(), "an i64 is not an i32");
}

// A generic with two parameters keeps them apart and in order.
#[test]
fn two_parameters_stay_in_the_order_they_were_declared() {
    let with = "enum Result<T, E> {\n    Ok(T),\n    Err(E),\n}\n";
    clean(&format!(
        "{}fn f(): Result<i32, i64> {{\n    Result::Ok(1)\n}}\n",
        with
    ));
    // A literal would unify with either side, so the wrong-way case is put
    // with a value that is already one of the two.
    let out = refused(&format!(
        "{}fn f(a: i32): Result<i32, i64> {{\n    Result::Err(a)\n}}\n",
        with
    ));
    assert!(!out.is_empty(), "an i32 is not the error side");
    clean(&format!(
        "{}fn f(a: i32, b: i64): Result<i32, i64> {{\n    Result::Err(b)\n}}\n",
        with
    ));
}

// A struct pattern over a generic, which is the fourth of the six places.
#[test]
fn a_struct_pattern_over_a_generic_binds_what_it_holds() {
    let with = "struct Held<T> {\n    pub v: T,\n}\n";
    clean(&format!(
        "{}fn f(h: Held<i64>): i64 {{\n    match h {{\n        Held {{ v }} => v,\n    }}\n}}\n",
        with
    ));
}


// ---- Slices ------------------------------------------------------------------

// The `Range` a `..` builds. These tests declare their own, as the ones above
// do: a literal is syntax for a type a library declares, and there is no
// library here.
const RANGE: &str = "struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n";

// "A range is an expression, so a slice needs no rule of its own" (§5): the
// same `[` indexes by one and slices by two, and what the index turned out to
// be is what says which. "What a slice denotes is the run itself: `a[1..3]` is
// a place of type `T[]`".
#[test]
fn indexing_by_a_range_denotes_the_run_and_not_an_element() {
    clean(
        &format!("{}{}", RANGE, "fn f(): i32 {\n\
         \x20   let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   let s: &i32[] = &a[1..3]\n\
         \x20   s[0]\n\
         }\n"),
    );
}

// And by one value it is still the element, which is the half that must not
// have moved.
#[test]
fn indexing_by_one_value_is_still_the_element() {
    clean(
        &format!("{}{}", RANGE, "fn f(): i32 {\n\
         \x20   let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   let one: &i32 = &a[1]\n\
         \x20   a[2]\n\
         }\n"),
    );
}

// A view that writes is the other spelling, and it is the same rule.
#[test]
fn a_slice_may_be_borrowed_to_write_as_well_as_to_read() {
    clean(
        &format!("{}{}", RANGE, "fn f() {\n\
         \x20   var a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   let w: *i32[] = *a[1..3]\n\
         }\n"),
    );
}

// "`T[]` is a type of no known size, and nothing can hold one: no local, no
// field, no parameter and no return may be a `T[]`. It exists only behind a
// reference" (§3). A slice is where one turns up without being written, so it
// is where that rule is felt.
#[test]
fn a_run_may_not_be_held_by_a_name() {
    let out = refused(
        &format!("{}{}", RANGE, "fn f() {\n\
         \x20   let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\n\
         \x20   let x = a[1..3]\n\
         }\n"),
    );
    assert!(out.contains("is a run and nothing holds one"), "{}", out);
    assert!(out.contains("borrows a view of it"), "{}", out);
}
