// How long a thing is good for: the bounds written on a region, and how long
// a borrow stays in hand.

use super::*;

// ---- Bounds on regions -----------------------------------------------------

// `'a: 'b` says the first is good for at least as long as the second. It is
// nothing a declaration can be refused for -- it is what a caller is held to --
// so it is held to where §3 says every region refusal lands: at the call.
#[test]
fn a_lifetime_bound_is_held_to_at_the_call() {
    let with = "fn holds<'a, 'b>(x: &'a i32, y: &'b i32): i32 where 'a: 'b {\n    1\n}\n";
    // `x` came from outside and `y` from a local, so `'a` outlives `'b`.
    clean(&format!("{}fn f(p: &i32) {{\n    let n = 1;\n    holds(p, &n);\n}}\n", with));
    // The other way round, and it does not.
    let out = refused(&format!(
        "{}fn f(p: &i32) {{\n    let n = 1;\n    holds(&n, p);\n}}\n",
        with
    ));
    assert!(out.contains("`'a` does not outlive `'b`"), "{}", out);
    assert!(out.contains("this call is where it has to"), "{}", out);
    assert!(out.contains("the signature says `'a` outlives `'b`"), "{}", out);
}

// Written among the parameters instead of in a `where`, which says the same
// thing: "`fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing".
#[test]
fn a_bound_written_inline_says_what_a_where_says() {
    let out = refused(
        "fn holds<'a: 'b, 'b>(x: &'a i32, y: &'b i32): i32 {\n    1\n}\n\
         fn f(p: &i32) {\n    let n = 1;\n    holds(&n, p);\n}\n",
    );
    assert!(out.contains("`'a` does not outlive `'b`"), "{}", out);
}

// `T: 'a` is the same promise about a type: what T was handed has to be good
// for at least as long as what `'a` was.
#[test]
fn a_type_held_to_a_region_is_held_to_it_at_the_call() {
    let with = "fn holds<'a, T: 'a>(x: &'a i32, t: T): i32 {\n    1\n}\n";
    clean(&format!("{}fn f(p: &i32) {{\n    let n = 1;\n    holds(&n, p);\n}}\n", with));
    let out = refused(&format!(
        "{}fn f(p: &i32) {{\n    let n = 1;\n    holds(p, &n);\n}}\n",
        with
    ));
    assert!(out.contains("`T` does not outlive `'a`"), "{}", out);
}

// A method's receiver stands where parameter 0 does, and `&'a self` is the one
// borrow nobody writes -- so `'a` is how long the receiver itself is good for
// and not what it points into.
#[test]
fn a_receivers_region_is_the_receivers_own_life() {
    let with = "struct S {\n    pub x: i32,\n}\n\
                impl S {\n    pub fn m<'a, 'b>(&'a self, y: &'b i32): i32 where 'a: 'b {\n\
                \x20       1\n    }\n}\n";
    // The receiver outlives the argument, which is what the bound asks.
    clean(&format!(
        "{}fn f(s: &S) {{\n    let n = 1;\n    s.m(&n);\n}}\n",
        with
    ));
    // And here it does not: `s` is a block further in than `n` is.
    let out = refused(&format!(
        "{}fn f(): i32 {{\n    let n = 1;\n    {{\n        let s = S {{ x: 1 }};\n\
         \x20       s.m(&n)\n    }}\n}}\n",
        with
    ));
    assert!(out.contains("`'a` does not outlive `'b`"), "{}", out);
    assert!(out.contains("`'a` was handed this"), "{}", out);
    assert!(out.contains("`'b` was handed this, which lasts longer"), "{}", out);
}

// A lifetime takes no type argument at a call: what it stands for is a region,
// and regions are not what unification works out. So `<'a, T>` wants one
// argument and not two, and no hole is made that nothing could ever fill.
#[test]
fn a_lifetime_takes_no_type_argument() {
    // Written, and one is the right number.
    clean("fn holds<'a, T>(x: &'a i32, t: T): i32 {\n    1\n}\n\
           fn f(p: &i32) {\n    holds<i32>(p, 1);\n}\n");
    // And left out, which is where a hole for `'a` would have been left open.
    clean("fn holds<'a, T>(x: &'a i32, t: T): i32 {\n    1\n}\n\
           fn f(p: &i32) {\n    holds(p, 1);\n}\n");
    // Two written where one is wanted is still the wrong number.
    let out = refused("fn holds<'a, T>(x: &'a i32, t: T): i32 {\n    1\n}\n\
                       fn f(p: &i32) {\n    holds<i32, i32>(p, 1);\n}\n");
    assert!(out.contains("takes 1 type arguments and was given 2"), "{}", out);
}

// A `where` about a type that was built rather than declared: the subject is
// whatever it holds, and what it holds is what has to last.
#[test]
fn a_where_about_a_built_type_is_held_to_as_well() {
    clean(
        "struct Box<T> {\n    pub it: T,\n}\n\
         fn built<'a, T>(x: &'a i32, b: Box<T>): i32 where Box<T>: 'a {\n    1\n}\n\
         fn f(p: &i32, b: Box<i32>) {\n    built(p, b);\n}\n",
    );
}

// ---- How long a borrow is in hand ------------------------------------------

// A borrow lasts to the last place anything can reach through it, which is
// where the slot holding it is last read -- not to the end of the block.
#[test]
fn a_borrow_is_done_with_when_nothing_reads_it_again() {
    clean("fn f() {\n    var x = 1;\n    let r = &x;\n    let n = r;\n    let m = *x;\n}\n");
    let out = refused(
        "fn f() {\n    var x = 1;\n    let r = &x;\n    let m = *x;\n    let n = r;\n}\n",
    );
    assert!(out.contains("`x` is borrowed already"), "{}", out);
}

// A loop is where being written above is not being run above: the second turn
// reaches through the borrow again, so a slot last read inside one is in hand
// for all of it.
#[test]
fn a_borrow_read_inside_a_loop_is_in_hand_for_all_of_it() {
    let out = refused(
        "fn f() {\n    var x = 1;\n    let r = &x;\n    while true {\n\
         \x20       let m = *x;\n        let n = r;\n    }\n}\n",
    );
    assert!(out.contains("`x` is borrowed already"), "{}", out);
}

// A capture is a borrow like any other and ends like any other: what the
// closure holds is let go when nothing reads the closure again.
#[test]
fn a_capture_is_done_with_when_nothing_reads_the_closure_again() {
    clean(
        "fn f() {\n    var n = 0;\n    let show = || n;\n    let k = show;\n\
         \x20   let bump = || n = n + 1;\n}\n",
    );
    let out = refused(
        "fn f() {\n    var n = 0;\n    let show = || n;\n    let bump = || n = n + 1;\n\
         \x20   let k = show;\n}\n",
    );
    assert!(out.contains("`n` is borrowed already"), "{}", out);
}

// A declaration whose references name no lifetime carries a region for each of
// them all the same, so a written `'a` sharpens what it gives back the same way
// it does anywhere else.
#[test]
fn a_declaration_that_elides_its_references_still_carries_regions() {
    let with = "struct Held {\n    pub it: &i32,\n}\n";
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

// Two regions handed in one argument answer for their own halves, where the
// argument was written as the thing it is built out of.
#[test]
fn two_regions_of_one_argument_are_told_apart() {
    let with = "fn takes<'x, 'y>(p: (&'x i32, &'y i32)): i32 where 'x: 'y {\n    1\n}\n";
    clean(&format!("{}fn f(q: &i32) {{\n    let n = 1;\n    takes((q, &n));\n}}\n", with));
    let out = refused(&format!(
        "{}fn f(q: &i32) {{\n    let n = 1;\n    takes((&n, q));\n}}\n",
        with
    ));
    assert!(out.contains("`'x` does not outlive `'y`"), "{}", out);
}

// Which borrows keep a slot's extent: the ones that got as far as the value.
// "a local at the end of its block, a temporary at the end of its statement"
// (§2), and a `&` handed to something that gives back no reference is a
// temporary however it was written.
#[test]
fn a_borrow_that_reached_nothing_goes_with_the_statement() {
    // `len` gives back an `i32` and can hold nothing, so the `&x` is over when
    // the line is -- even though `n` is read after the `*`.
    clean(
        "fn len(s: &i32): i32 {\n    1\n}\n\
         fn f() {\n    var x = 1;\n    let n = len(&x);\n    let m = *x;\n    let k = n;\n}\n",
    );
    // `pick` gives back a reference tied to both, so both get as far as `r`.
    let out = refused(
        "fn pick(a: &i32, b: &i32): &i32 {\n    a\n}\n\
         fn f() {\n    var x = 1;\n    let r = pick(&x, &x);\n\
         \x20   let m = *x;\n    let k = r;\n}\n",
    );
    assert!(out.contains("`x` is borrowed already"), "{}", out);
}

// A declaration carries the regions of what it holds, however deep: the
// references inside `Inner` have to stand in a region, and `Outer` is where
// that region comes from.
#[test]
fn a_declaration_carries_the_regions_of_what_it_holds() {
    let with = "struct Inner {\n    pub it: &i32,\n}\n\
                struct Outer {\n    pub inner: Inner,\n}\n";
    let out = refused(&format!(
        "{}fn loose(p: &i32, q: &i32): Outer {{\n    Outer {{ inner: Inner {{ it: p }} }}\n}}\n\
         fn f(p: &i32): Outer {{\n    let n = 1;\n    loose(p, &n)\n}}\n",
        with
    ));
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    clean(&format!(
        "{}fn tight<'a>(p: &'a i32, q: &i32): Outer<'a> {{\n\
         \x20   Outer {{ inner: Inner {{ it: p }} }}\n}}\n\
         fn f(p: &i32): Outer {{\n    let n = 1;\n    tight(p, &n)\n}}\n",
        with
    ));
}

// A declaration reached from itself has no finite number of regions -- each
// turn round adds the last one's -- and the count stops rather than running
// away. Written down because a hang is what the other answer would be.
#[test]
fn a_declaration_reached_from_itself_is_counted_and_not_chased() {
    clean(
        "struct A {\n    pub b: &B,\n}\n\
         struct B {\n    pub a: &A,\n}\n\
         fn f(p: &i32): i32 {\n    1\n}\n",
    );
}
