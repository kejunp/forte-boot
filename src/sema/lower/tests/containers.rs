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
