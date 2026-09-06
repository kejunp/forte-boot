// Method calls, which are where a receiver has to be found before anything
// else can be looked up.

use super::*;

// ---- Method calls ---------------------------------------------------------

// "A method, resolved to the one it calls. `.` and `::` are both gone": the
// TIR has no method call of its own, and which a call of a field is, is settled
// here.
#[test]
fn a_call_of_a_field_may_be_a_method() {
    let ttir = clean(
        "struct Buf {\n    pub n: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.len() }\n",
    );
    let found = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Method { item, .. } => Some(*item),
        _ => None,
    }).expect("a method call");
    let TTIRItemKind::Fn(f) = &ttir.items[found].kind else { panic!() };
    assert_eq!(f.name, "len");
}

// A method is reached through a reference too: "a reference stands for the
// place it refers to and is read, called, indexed and reached into exactly as
// that place is".
#[test]
fn a_method_is_reached_through_a_reference() {
    clean(
        "struct Buf {\n    pub n: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: &Buf): i32 { b.len() }\n",
    );
}

// The receiver is not one of the arguments, so what a call was handed is what
// is left after it.
#[test]
fn a_method_is_held_to_what_it_takes() {
    let with = "struct Buf {\n    pub n: i32,\n}\n\
                impl Buf {\n    fn put(&self, x: i32): i32 { x }\n}\n";
    clean(&format!("{}fn f(b: Buf): i32 {{ b.put(1) }}\n", with));
    let out = refused(&format!("{}fn f(b: Buf): i32 {{ b.put(\"x\") }}\n", with));
    assert!(out.contains("argument 1 is `str` and it takes `i32`"), "{}", out);
    let out = refused(&format!("{}fn f(b: Buf): i32 {{ b.put(1, 2) }}\n", with));
    assert!(out.contains("`put` takes 1 and was handed 2"), "{}", out);
}

// A field of the same name wins where it could be the thing called: it is the
// nearer thing, and a struct holding a fn is reached before an impl is looked
// in.
#[test]
fn a_field_holding_a_fn_is_reached_before_an_impl_is() {
    let ttir = clean(
        "struct Buf {\n    pub run: fn(i32): i32,\n}\n\
         impl Buf {\n    fn run(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.run(1) }\n",
    );
    // A call of a field and not a method: nothing here resolved to the impl.
    assert!(
        !ttir.exprs.iter().any(|e| matches!(e.kind, TTIRExprKind::Method { .. })),
        "the field is the nearer thing",
    );
}

// And where it could not be, the method answers. Letting the field win there
// made the method unreachable and said "`i32` is not a fn" about a name the
// reader was not talking about -- and a container declaring `len` beside a
// `len()` is the ordinary case, not a clever one.
#[test]
fn a_field_that_is_not_a_fn_does_not_hide_a_method() {
    let ttir = clean(
        "struct Buf {\n    pub len: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.len() }\n",
    );
    let found = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Method { item, .. } => Some(*item),
        _ => None,
    }).expect("the method, not the field");
    let TTIRItemKind::Fn(f) = &ttir.items[found].kind else { panic!() };
    assert_eq!(f.name, "len");
    // And the field is still reachable by reading it, which is the reading the
    // method did not take: only the call it could not have answered.
    clean(
        "struct Buf {\n    pub len: i32,\n}\n\
         impl Buf {\n    fn len(&self): i32 { 0 }\n}\n\
         fn f(b: Buf): i32 { b.len }\n",
    );
}

// A field whose type is a parameter is not a fn either. What it stands for is
// the caller's to say, and one with no bound is a thing nothing can call
// whatever it turns out to be -- so the method is the answer that has one.
#[test]
fn a_field_of_parameter_type_does_not_hide_a_method() {
    let ttir = clean(
        "struct Box<T> {\n    pub v: T,\n}\n\
         impl<T> Box<T> {\n    fn v(&self): i32 { 0 }\n}\n\
         fn f(b: Box<i32>): i32 { b.v() }\n",
    );
    assert!(
        ttir.exprs.iter().any(|e| matches!(e.kind, TTIRExprKind::Method { .. })),
        "a `T` is not something a call could have meant",
    );
}

// ---- An impl's own parameters ------------------------------------------------

// "`<impl_decl>` takes its own `<generic_params_opt>`, so `impl<T> Stack<T>`"
// (§8). What that costs is that the parameter has to be in scope in three
// places that are three separate passes: the impl's own subject, every member's
// signature, and every member's body. None of them had it, so a generic impl
// was `no type is called `T`` twice over and the whole standard library is
// free functions because of it.
#[test]
fn an_impl_may_take_its_own_parameters() {
    clean(
        "struct Box<T> {\n    pub v: T,\n}\n\
         impl<T> Box<T> {\n    fn get(&self): T { self.v }\n}\n",
    );
}

// The impl's parameters and the member's own are one list, the impl's first.
// That is what lets every pass after this one know nothing about impl
// generics: a `Ty::Param` is a name and an index into one list, and there is
// one list.
#[test]
fn an_impls_parameters_stand_in_front_of_a_members_own() {
    let ttir = clean(
        "struct Box<T> {\n    pub v: T,\n}\n\
         impl<T> Box<T> {\n\
         \x20   fn mapped<U>(self, f: fn(T): U): U { f(self.v) }\n}\n",
    );
    let found = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "mapped" => Some(f.generics.clone()),
        _ => None,
    }).expect("the member");
    let names: Vec<&str> = found
        .iter()
        .filter_map(|g| match g {
            TTIRGeneric::Type { name, .. } => Some(name.as_str()),
            TTIRGeneric::Life { .. } => None,
        })
        .collect();
    assert_eq!(names, vec!["T", "U"], "the impl's, and then the member's own");
}

// And what the receiver settles. A method call writes no type arguments --
// there is nowhere to write them -- so every one of the impl's parameters is a
// hole that the receiver fills: `Box<i32>` against the declared `Box<T>` is the
// whole of what says the answer is an `i32`.
#[test]
fn the_receiver_says_what_an_impls_parameters_are() {
    let with = "struct Box<T> {\n    pub v: T,\n}\n\
                impl<T> Box<T> {\n    fn get(&self): T { self.v }\n}\n";
    clean(&format!("{}fn f(b: Box<i32>): i32 {{ b.get() }}\n", with));
    // And is held to it: the same method on the same type answers one thing.
    let out = refused(&format!("{}fn f(b: Box<i32>): str {{ b.get() }}\n", with));
    assert!(out.contains("i32"), "{}", out);
}

// A bound written on the impl's parameter is a bound its members may lean on.
#[test]
fn an_impls_parameter_carries_its_bounds() {
    clean(
        "trait Show {\n    fn show(&self): i32\n}\n\
         struct Box<T> {\n    pub v: T,\n}\n\
         impl<T: Show> Box<T> {\n    fn shown(&self): i32 { self.v.show() }\n}\n",
    );
}

// And may not be re-declared by a member. A parameter is found by name and the
// first of that name answers, so the member's own would be one nothing could
// write -- which came out as a type the checker never settled and a program
// that would not link.
#[test]
fn a_member_may_not_re_declare_the_impls_parameter() {
    let out = refused(
        "struct Box<T> {\n    pub v: T,\n}\n\
         impl<T> Box<T> {\n    fn odd<T>(&self, x: T): T { x }\n}\n",
    );
    assert!(out.contains("`T` is already a parameter of this impl"), "{}", out);
}

// ---- Trait objects -------------------------------------------------------------

// `dyn` takes the name of a trait and of nothing else. A `dyn` over a struct
// would be a `dyn` over something with no impls to choose between, which is a
// mistake and not a shorthand.
#[test]
fn dyn_stands_in_front_of_a_trait() {
    clean("trait Shape {\n    fn area(&self): i32\n}\n\
           fn f(s: &dyn Shape): i32 { s.area() }\n");
    let out = refused("struct Sq {\n    pub s: i32,\n}\n\
                       fn f(s: &dyn Sq): i32 { 0 }\n");
    assert!(out.contains("`Sq` is not a trait"), "{}", out);
    let out = refused("fn f(s: &dyn Nowhere): i32 { 0 }\n");
    assert!(out.contains("no trait is called `Nowhere`"), "{}", out);
}

// A reference to something that answers the trait stands where a reference to
// the object was wanted, and nothing goes the other way: an object has
// forgotten which type it was.
#[test]
fn a_reference_becomes_an_object_where_the_type_answers() {
    let with = "trait Shape {\n    fn area(&self): i32\n}\n\
                struct Sq {\n    pub s: i32,\n}\n\
                impl Shape for Sq {\n    fn area(&self): i32 { 0 }\n}\n\
                struct Bare {\n    pub n: i32,\n}\n\
                fn take(s: &dyn Shape): i32 { s.area() }\n";
    clean(&format!("{}fn f(q: &Sq): i32 {{ take(q) }}\n", with));
    // One that answers nothing has no table to be given, so it is not one.
    let out = refused(&format!("{}fn f(b: &Bare): i32 {{ take(b) }}\n", with));
    assert!(out.contains("&Bare"), "{}", out);
    assert!(out.contains("dyn Shape"), "{}", out);
}

// Nothing holds a bare one: how wide it is is not a question with an answer,
// which is what makes it dynamic. The same rule a `T[]` is held to, and the
// same message shape.
#[test]
fn nothing_holds_a_bare_trait_object() {
    let out = refused(
        "trait Shape {\n    fn area(&self): i32\n}\n\
         struct Sq {\n    pub s: i32,\n}\n\
         impl Shape for Sq {\n    fn area(&self): i32 { 0 }\n}\n\
         fn f() {\n    let q = Sq { s: 1 }\n    let s: dyn Shape = q\n}\n",
    );
    assert!(out.contains("is a trait object and nothing holds one"), "{}", out);
}

// A method reached through an object is the *trait's* member: which impl
// answers is what the table says, and it says it while the program runs.
#[test]
fn a_method_on_an_object_names_the_traits_member() {
    let ttir = clean(
        "trait Shape {\n    fn area(&self): i32\n}\n\
         fn f(s: &dyn Shape): i32 { s.area() }\n",
    );
    let found = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Method { item, .. } => Some(*item),
        _ => None,
    }).expect("a method call");
    // The trait declares it, so the trait is what holds it.
    assert!(
        ttir.items.iter().any(|i| matches!(&i.kind,
            TTIRItemKind::Trait { members, .. } if members.contains(&found))),
        "the member is the trait's",
    );
}

// ---- What the collector holds ---------------------------------------------------

// `gc T` is a type and not only a word on a binding, which is the question §8
// left open answered: a `gc` value handed to a function is still one, and the
// signature can say so.
#[test]
fn gc_is_a_type_a_signature_can_say() {
    clean("struct Buf {\n    pub n: i32,\n}\n\
           fn held(b: gc Buf): i32 { b.n }\n");
    // And a field, which is what a collected structure wants.
    clean("struct Inner {\n    pub v: i32,\n}\n\
           struct Outer {\n    pub inner: gc Inner,\n}\n\
           fn f(o: &Outer): i32 { o.inner.v }\n");
}

// A `let gc` makes one of that type, whether or not the type was written: the
// word on the binding and the word in the type say the same thing, or the word
// would mean one thing on a `let` and another in a signature.
#[test]
fn a_gc_binding_has_the_type_the_word_makes() {
    let ttir = clean(
        "struct Buf {\n    pub n: i32,\n}\n\
         fn f() {\n    let gc b = Buf { n: 1 }\n}\n",
    );
    let held = ttir.bodies.iter().find_map(|b| {
        b.locals.iter().find(|l| matches!(&l.name, TIRBinding::Name(n) if n == "b")).map(|l| l.ty)
    }).expect("the binding");
    assert!(matches!(ttir.types[held], Ty::GC(_)), "{:?}", ttir.types[held]);
}

// Reached through like a reference: the word is spent where the binding is
// written and nowhere else.
#[test]
fn a_gc_value_is_reached_through() {
    clean("struct Buf {\n    pub n: i32,\n}\n\
           fn f(b: gc Buf): i32 { b.n }\n");
    // Including into a `gc` behind a `gc`, which is two reads and no words.
    clean("struct Inner {\n    pub v: i32,\n}\n\
           struct Outer {\n    pub inner: gc Inner,\n}\n\
           fn f(o: gc Outer): i32 { o.inner.v }\n");
}

// One way only. A `T` becomes a `gc T` where one is wanted -- that is the
// allocation -- and nothing goes back, because taking the value out of the
// collector's room is giving away something the collector still holds.
#[test]
fn a_collected_value_does_not_become_an_ordinary_one() {
    let with = "struct Buf {\n    pub n: i32,\n}\n\
                fn plain(b: Buf): i32 { b.n }\n";
    let out = refused(&format!(
        "{}fn f(b: gc Buf): i32 {{ plain(b) }}\n", with));
    assert!(out.contains("gc Buf"), "{}", out);
}

// ---- What a value is expected to be ---------------------------------------------

// A conversion happens where a type is expected of a value, and the four
// places that expect one are a body, a branch, an arm and a block's tail.
#[test]
fn a_body_converts_to_what_its_signature_says() {
    let with = "trait Shape {\n    fn area(&self): i32\n}\n\
                struct Sq {\n    pub s: i32,\n}\n\
                impl Shape for Sq {\n    fn area(&self): i32 { 0 }\n}\n";
    clean(&format!("{}fn f(q: &Sq): &dyn Shape {{ q }}\n", with));
    // And the view, which had the same gap and is not a `dyn` at all -- the
    // machinery is one, so it was missing in all three or in none.
    clean("fn f(a: &i32[4]): &i32[] { a }\n");
}

#[test]
fn every_way_out_of_a_branch_converts() {
    let with = "trait Shape {\n    fn area(&self): i32\n}\n\
                struct Sq {\n    pub s: i32,\n}\n\
                struct Ci {\n    pub r: i32,\n}\n\
                impl Shape for Sq {\n    fn area(&self): i32 { 0 }\n}\n\
                impl Shape for Ci {\n    fn area(&self): i32 { 0 }\n}\n";
    clean(&format!(
        "{}fn f(c: bool, x: &Sq, y: &Ci): i32 {{\n\
         \x20   let s: &dyn Shape = if c {{ x }} else {{ y }}\n    s.area()\n}}\n",
        with));
    clean(&format!(
        "{}fn f(k: i32, x: &Sq, y: &Ci): i32 {{\n\
         \x20   let s: &dyn Shape = match k {{ 0 => x, _ => y }}\n    s.area()\n}}\n",
        with));
}

// And it reaches one expression and no further: an `if` handed to a call is
// the call's business, and the numbers inside the `if` are the `if`'s. What
// passes an expectation on is the three that are transparent to a value.
#[test]
fn an_expectation_reaches_one_expression() {
    // The parameter is an `i32`, the branches are numbers, and nothing here
    // tries to make either into the other.
    clean("fn g(n: i32): i32 { n }\n\
           fn f(c: bool): i32 { g(if c { 1 } else { 2 }) }\n");
    // A branch that disagrees with what was wanted is still a branch that
    // disagrees: an expectation converts where it can and reports where it
    // cannot.
    let out = refused(
        "struct Sq {\n    pub s: i32,\n}\n\
         fn f(c: bool, q: Sq): i32 {\n    let n: i32 = if c { q } else { 1 }\n    n\n}\n",
    );
    assert!(out.contains("Sq"), "{}", out);
}

// ---- A release and a collector --------------------------------------------------

// A `gc` of something with a release is refused: the compiler places a release
// where a reader can point at it, and a sweep is not such a place. What
// happened before was that neither placed one and nothing was said.
#[test]
fn a_gc_of_something_with_a_release_is_refused() {
    let with = "trait Drop {\n    fn drop(*self)\n}\n\
                struct Buf {\n    pub n: i32,\n}\n\
                impl Drop for Buf {\n    fn drop(*self) {}\n}\n";
    // On a binding,
    let out = refused(&format!("{}fn f() {{\n    let gc b = Buf {{ n: 1 }}\n}}\n", with));
    assert!(out.contains("`Buf` has a release"), "{}", out);
    // in a signature,
    let out = refused(&format!("{}fn f(b: gc Buf): i32 {{ b.n }}\n", with));
    assert!(out.contains("`Buf` has a release"), "{}", out);
    // and in a field, which is where one would otherwise be smuggled in.
    let out = refused(&format!("{}struct Held {{\n    pub b: gc Buf,\n}}\n", with));
    assert!(out.contains("`Buf` has a release"), "{}", out);
}

// And something holding one has a release too, so it is refused for the same
// reason -- what `Copies::drops` answers is asked and not the declaration.
#[test]
fn a_gc_of_something_holding_a_release_is_refused_too() {
    let out = refused(
        "trait Drop {\n    fn drop(*self)\n}\n\
         struct Buf {\n    pub n: i32,\n}\n\
         impl Drop for Buf {\n    fn drop(*self) {}\n}\n\
         struct Wrap {\n    pub b: Buf,\n}\n\
         fn f() {\n    let gc w = Wrap { b: Buf { n: 1 } }\n}\n",
    );
    assert!(out.contains("has a release"), "{}", out);
}

// Everything without one is untouched, which is most of it.
#[test]
fn a_gc_of_something_with_no_release_is_written() {
    clean("struct Buf {\n    pub n: i32,\n}\n\
           fn f(b: gc Buf): i32 { b.n }\n\
           fn g() {\n    let gc b = Buf { n: 1 }\n}\n");
}
