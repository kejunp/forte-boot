// `while` and `for`, and the value a `break` may carry out of one.

use super::*;

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
