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
//
// Two of the three are the machine's: an array, a view of one and a `Range` are
// walked by index arithmetic, because a call to add one to a number would be a
// call to add one to a number. The third is a file's own, and it is how the set
// stays closed while anything may join it.
#[test]
fn what_may_be_run_through_is_a_closed_set() {
    let with = "struct Range<T> {\n    pub n: i32,\n}\n";
    // An array, a view of one, and a range.
    clean(&format!("{}fn f(v: i32[3]) {{\n    for x in v {{\n    }}\n}}\n", with));
    clean(&format!("{}fn f(v: &i32[]) {{\n    for x in v {{\n    }}\n}}\n", with));
    clean(&format!("{}fn f() {{\n    for i in 0..10 {{\n    }}\n}}\n", with));

    // And a thing that is none of them says so, and says why the set is closed.
    let out = refused(&format!("{}fn f(n: i32) {{\n    for x in n {{\n    }}\n}}\n", with));
    assert!(out.contains("there is no running through a `i32`"), "{}", out);
    assert!(out.contains("no iterator protocol"), "{}", out);
}

// A file joins the set by writing the three a walk calls beside its
// declaration: `step`, one on from where it was; `valid`, whether there is
// another; and `elem`, what is there. The cursor starts at -1 and every turn is
// those three in order, so stepping from -1 has to land on the first.
//
// What a turn hands over is `elem`'s answer, which is what lets a map be run
// through at all: it gives back a pair, and nothing below the checker has to
// know that a map is a thing that does.
#[test]
fn a_file_says_how_what_it_declares_is_run_through() {
    let with = "struct Held<T> { pub n: i64 }\n\
                fn step<T>(h: &Held<T>, at: i64): i64 { at + 1 }\n\
                fn valid<T>(h: &Held<T>, at: i64): bool { at < h.n }\n\
                fn elem<T>(h: &Held<T>, at: i64): T { elem(h, at) }\n";
    let ttir = clean(&format!(
        "{}fn f(h: Held<i32>): i32 {{\n\
         \x20   var t: i32 = 0\n\
         \x20   for x in h {{ t = t + x }}\n\
         \x20   t\n\
         }}\n",
        with
    ));
    // What comes out is the loop the three make, and not a `For`: three
    // ordinary calls, so no pass below this one has to learn a thing.
    assert!(
        !ttir.exprs.iter().any(|e| matches!(e.kind, TTIRExprKind::For { .. })),
        "a walk was left as a `For`"
    );
    assert!(ttir.exprs.iter().any(|e| matches!(e.kind, TTIRExprKind::While { .. })));

    // And one that writes only two of the three is not run through: the walk
    // is the three together, and two of them is nothing.
    let out = refused(
        "struct Held<T> { pub n: i64 }\n\
         fn step<T>(h: &Held<T>, at: i64): i64 { at + 1 }\n\
         fn valid<T>(h: &Held<T>, at: i64): bool { at < h.n }\n\
         fn f(h: Held<i32>) {\n    for x in h {\n    }\n}\n",
    );
    assert!(out.contains("there is no running through a `Held<i32>`"), "{}", out);
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

// ---- What a loop is worth ---------------------------------------------------

// "Every loop takes a `break x` and yields `null` where none is given" (§8) --
// and the first half of that did not work. The loop's own end and a `break` out
// of it arrived in one block, and that block wrote the `null`: the break wrote
// the slot and the null went on top of it, so every `break x` used as a value
// came to nought. It compiled, and it answered wrongly.
//
// What the tree shows is the shape of the fix -- two ways out and not one, so
// that the null can be written where a break does not reach. What the *answer*
// is, is `src/tests.rs`', running being the only thing that can say a value
// survived.
#[test]
fn a_loop_and_a_break_out_of_it_are_two_ways_out() {
    clean("fn f(): i32 {\n    let r = while true { break 7 }\n    r\n}\n");
    // With nothing broken, which is the `null` half and is what it always was.
    clean("fn f() {\n    var i = 0\n    while i < 3 { i = i + 1 }\n}\n");
    // A `break` carrying nothing out of a loop nobody reads.
    clean("fn f() {\n    var i = 0\n    while true { i = i + 1\n        if i > 3 { break } }\n}\n");
}
