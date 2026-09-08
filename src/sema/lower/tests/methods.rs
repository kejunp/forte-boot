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

// And everywhere else a type is written, which is where it was *not* said. A
// local was the only position asked about, so a signature, a field, a payload
// and a type argument each resolved a type nothing can hold and let it
// through -- and what the reader got was a message at the call, "argument 1 is
// `Sq` and it takes `dyn Shape`", blaming a caller for a signature nobody
// could have satisfied.
#[test]
fn a_type_nothing_holds_is_refused_where_it_is_written() {
    let with = "trait Shape {\n    fn area(&self): i32\n}\n";
    for (source, said) in [
        // A parameter and a return.
        ("fn f(s: dyn Shape): i32 { 0 }\n", "trait object"),
        ("fn f(a: &i32[]): i32[] { a }\n", "is a run"),
        // A field and a payload.
        ("struct B {\n    pub s: dyn Shape,\n}\n", "trait object"),
        ("struct B {\n    pub r: i32[],\n}\n", "is a run"),
        ("enum E {\n    One(dyn Shape),\n}\n", "trait object"),
        // A type argument, which is the one a `&` in front does not save:
        // `&Vec<dyn Shape>` is a reference to the `Vec`.
        ("struct V<T> {\n    pub t: T,\n}\nfn f(v: &V<dyn Shape>): i32 { 0 }\n", "trait object"),
        // And an element, since "an element must have a size" (§2). This is
        // the array *of* runs: the `[3]` is written first and is the outer of
        // the two, so what is inside it is a run.
        ("fn f(a: &i32[3][]): i32 { 0 }\n", "is a run"),
    ] {
        let out = refused(&format!("{}{}", with, source));
        assert!(out.contains(said), "{}\n{}", source, out);
        assert!(out.contains("nothing holds one"), "{}\n{}", source, out);
    }
}

// What one stands behind. A reference is the borrowed form and a `gc` the
// owned; a pointer counts too, promising nothing about what it addresses,
// which is the whole of what a `ptr` is (§2).
//
// A run is the one a `gc` does not carry: its second word is a *length*, and a
// length is not something the collector hands out.
#[test]
fn a_reference_a_pointer_and_a_gc_are_what_one_stands_behind() {
    let with = "trait Shape {\n    fn area(&self): i32\n}\n";
    clean(&format!(
        "{}fn f(a: &i32[], s: &dyn Shape): i32 {{ a[0] + s.area() }}\n\
         fn g(a: *i32[], s: *dyn Shape): i32 {{ 0 }}\n\
         fn h(p: ptr u8[], q: ptr dyn Shape): i32 {{ 0 }}\n\
         fn k(s: gc dyn Shape): i32 {{ s.area() }}\n",
        with));
    let out = refused(&format!("{}fn f(a: gc i32[]): i32 {{ 0 }}\n", with));
    assert!(out.contains("is a run and nothing holds one"), "{}", out);
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

// ---- A number with nothing said about it -----------------------------------------

// `&5` becomes a `&dyn Show` the way `&q` becomes a `&dyn Shape`. It did not:
// an unsuffixed number is a hole, an impl is never written for a hole, and so
// the lookup found nothing and the conversion was refused. What is asked
// instead is the type the hole would settle as -- `i32` for a whole number and
// `f64` for a fraction, which is the guess `Types::finish` makes for every one
// that is still standing at the end.
#[test]
fn a_literal_becomes_an_object() {
    let with = "trait Show {\n    fn show(&self): i32\n}\n\
                impl Show for i32 {\n    fn show(&self): i32 { 1 }\n}\n\
                impl Show for f64 {\n    fn show(&self): i32 { 2 }\n}\n";
    clean(&format!("{}fn f(): i32 {{\n    let s: &dyn Show = &5\n    s.show()\n}}\n", with));
    clean(&format!("{}fn f(): i32 {{\n    let s: &dyn Show = &2.5\n    s.show()\n}}\n", with));
    // And in an array of them, which is what a print's arguments are.
    clean(&format!(
        "{}fn f(a: &(&dyn Show)[]): i32 {{ 0 }}\n\
         fn g(): i32 {{ f(&[&5, &2.5]) }}\n",
        with));
}

// The guess is asked for and not taken: the hole is left standing, so a line
// below the object fills it like any other. Which order the two are written in
// does not change what the number is -- it would if the object settled it.
#[test]
fn a_line_below_the_object_still_says_what_the_number_is() {
    let with = "trait Show {\n    fn show(&self): i32\n}\n\
                impl Show for i32 {\n    fn show(&self): i32 { 1 }\n}\n\
                impl Show for i64 {\n    fn show(&self): i32 { 2 }\n}\n";
    clean(&format!(
        "{}fn f(): i32 {{\n    let n = 5\n    let s: &dyn Show = &n\n\
         \x20   let m: i64 = n\n    s.show()\n}}\n",
        with));
    // The other way round, which worked before this and has to keep working.
    clean(&format!(
        "{}fn f(): i32 {{\n    let n = 5\n    let m: i64 = n\n\
         \x20   let s: &dyn Show = &n\n    s.show()\n}}\n",
        with));
}

// Which means the answer given while the checker is working is provisional,
// and the tree is asked once more at the end: a hole that took the guess and
// was then filled with something the trait has no impl for is caught there
// rather than reaching a back end with no table to build.
#[test]
fn what_the_number_turned_out_to_be_is_held_to_the_trait() {
    let with = "trait Show {\n    fn show(&self): i32\n}\n\
                impl Show for i32 {\n    fn show(&self): i32 { 1 }\n}\n";
    let out = refused(&format!(
        "{}fn f(): i32 {{\n    let n = 5\n    let s: &dyn Show = &n\n\
         \x20   let m: i64 = n\n    s.show()\n}}\n",
        with));
    assert!(out.contains("`i64` does not answer `Show`"), "{}", out);
}

// And a number whose guess answers nothing is refused where it is written,
// which is what it always was.
#[test]
fn a_number_the_trait_has_no_impl_for_is_refused() {
    let out = refused(
        "trait Show {\n    fn show(&self): i32\n}\n\
         impl Show for bool {\n    fn show(&self): i32 { 1 }\n}\n\
         fn f(): i32 {\n    let s: &dyn Show = &5\n    s.show()\n}\n",
    );
    assert!(out.contains("dyn Show"), "{}", out);
}

// ---- A method on a place is a method on its address --------------------------------

// A body that declares `&self` is handed the address of the receiver, and a
// value receiver has its taken. What is asserted here is the shape of the tree,
// the answer itself being a thing only running can tell (`src/tests.rs`): a
// `Unary::Ref` stands over the receiver where the declaration takes a reference
// and the receiver is not one.
#[test]
fn a_value_receiver_is_addressed() {
    let with = "trait Held {\n    fn held(&self): i32\n}\n\
                struct Sq {\n    pub s: i32,\n}\n\
                impl Held for Sq {\n    fn held(&self): i32 { self.s }\n}\n";
    let ttir = clean(&format!("{}fn f(q: Sq): i32 {{ q.held() }}\n", with));
    let addressed = ttir.exprs.iter().any(|e| match &e.kind {
        TTIRExprKind::Unary { op: crate::tir::tir_nodes::TIRUnaryOp::Ref(_), operand } => {
            matches!(ttir.exprs[*operand].kind, TTIRExprKind::Local(_))
        }
        _ => false,
    });
    assert!(addressed, "the receiver was meant to be addressed\n{:#?}", ttir.exprs);
    // And one that is an address already is left as it stands.
    let ttir = clean(&format!("{}fn f(q: &Sq): i32 {{ q.held() }}\n", with));
    let addressed = ttir.exprs.iter().any(|e| {
        matches!(&e.kind, TTIRExprKind::Unary { op: crate::tir::tir_nodes::TIRUnaryOp::Ref(_), .. })
    });
    assert!(!addressed, "a reference was meant to be left alone\n{:#?}", ttir.exprs);
}

// ---- A method named through what declared it ---------------------------------------

// `T::f(&q)`, with the receiver written first where a `.` would have put it in
// front. A method was reachable through a `.` and through nothing else, which
// left three things with no spelling at all.
#[test]
fn a_method_is_named_through_the_declaration_it_belongs_to() {
    let with = "trait T {\n    fn f(&self): i32\n}\n\
                struct Q {\n    pub n: i32,\n}\n\
                impl T for Q {\n    fn f(&self): i32 { self.n }\n}\n\
                impl Q {\n    fn own(&self): i32 { self.n }\n}\n";
    // Through the trait that declared it,
    clean(&format!("{}fn g(q: &Q): i32 {{ T::f(q) }}\n", with));
    // through the type an impl wrote it in,
    clean(&format!("{}fn g(q: &Q): i32 {{ Q::f(q) }}\n", with));
    // including an impl that answers no trait,
    clean(&format!("{}fn g(q: &Q): i32 {{ Q::own(q) }}\n", with));
    // and on a receiver that is the value rather than a reference to it.
    clean(&format!("{}fn g(q: Q): i32 {{ Q::f(q) }}\n", with));
}

// The first of the three: a field of the same name wins with a `.` where it
// could be the thing called (§5), which made the method unreachable and left
// nothing to write instead. This is what to write instead.
#[test]
fn a_method_a_field_hides_is_reachable() {
    let with = "trait T {\n    fn f(&self): i32\n}\n\
                struct Q {\n    pub f: fn(): i32,\n}\n\
                impl T for Q {\n    fn f(&self): i32 { 1 }\n}\n";
    clean(&format!("{}fn g(q: &Q): i32 {{ T::f(q) }}\n", with));
    // And the `.` still reads the field, nothing having been taken away.
    clean(&format!("{}fn g(q: &Q): i32 {{ q.f() }}\n", with));
}

// The second: a parameter held to two traits that each declare a name. There is
// no rule for choosing between them and none is invented -- what settles it is
// the reader saying which they meant.
#[test]
fn a_bound_naming_two_of_one_name_is_settled_by_saying_which() {
    let with = "trait A {\n    fn f(&self): i32\n}\n\
                trait B {\n    fn f(&self): i32\n}\n";
    clean(&format!("{}fn g<P: A + B>(p: &P): i32 {{ A::f(p) }}\n", with));
    clean(&format!("{}fn g<P: A + B>(p: &P): i32 {{ B::f(p) }}\n", with));
    // And with neither said it is refused, which is what it always was.
    let out = refused(&format!("{}fn g<P: A + B>(p: &P): i32 {{ p.f() }}\n", with));
    assert!(out.contains("has more than one `f`"), "{}", out);
}

// The name in front is checked and not merely parsed. Without that,
// `Other::f(&q)` would run `Q`'s `f` and name something with nothing to do
// with it.
#[test]
fn the_declaration_named_in_front_has_to_be_the_one_it_came_from() {
    let with = "trait T {\n    fn f(&self): i32\n}\n\
                struct Q {\n    pub n: i32,\n}\n\
                struct R {\n    pub m: i32,\n}\n\
                impl T for Q {\n    fn f(&self): i32 { self.n }\n}\n";
    let out = refused(&format!("{}fn g(q: &Q): i32 {{ R::f(q) }}\n", with));
    assert!(out.contains("`R` has no method `f`"), "{}", out);
    // A receiver with no such method at all is the message it always was.
    let out = refused(&format!("{}fn g(r: &R): i32 {{ T::f(r) }}\n", with));
    assert!(out.contains("nothing is called `T::f`"), "{}", out);
}

// A path that names no method is a call like any other, which is what keeps a
// fn in a namespace working: `held::f(x)` is this shape exactly, and what tells
// them apart is whether the name in front is a declaration methods go on.
#[test]
fn a_path_that_names_no_method_is_a_call_like_any_other() {
    clean("namespace held {\n    pub fn f(x: i32): i32 { x }\n}\n\
           fn g(): i32 { held::f(1) }\n");
}

// ---- A bound is enough to make an object of --------------------------------------

// `fn f<T: Show>(x: &T)` has already said that whatever `T` turns out to be
// answers `Show`. So an object may be made of it, and which table gets built is
// a question for the instance -- where `T` is a type and not a name. Without
// this a bound bought a method call and nothing else: handing the `&T` on to
// something taking a `&dyn Show` was "argument 1 is `&T` and it takes
// `&dyn Show`", and the way round it was to take the bound off and lose the
// dispatch it was there for.
#[test]
fn a_bounded_parameter_becomes_an_object() {
    let with = "trait Show {\n    fn show(&self): i32\n}\n\
                fn by_table(s: &dyn Show): i32 { s.show() }\n";
    clean(&format!("{}fn f<T: Show>(x: &T): i32 {{ by_table(x) }}\n", with));
    // And at a name that says so, which is the other place an expectation
    // reaches.
    clean(&format!(
        "{}fn f<T: Show>(x: &T): i32 {{\n    let s: &dyn Show = x\n    s.show()\n}}\n",
        with));
}

// A parameter with no such bound is refused, which is what makes the bound the
// thing that bought it.
#[test]
fn a_parameter_with_no_bound_makes_no_object() {
    let with = "trait Show {\n    fn show(&self): i32\n}\n\
                trait Other {\n    fn other(&self): i32\n}\n\
                fn by_table(s: &dyn Show): i32 { s.show() }\n";
    let out = refused(&format!("{}fn f<T>(x: &T): i32 {{ by_table(x) }}\n", with));
    assert!(out.contains("dyn Show"), "{}", out);
    // And one bounded by a different trait, so it is the trait that answers
    // and not the fact of there being a bound at all.
    let out = refused(&format!("{}fn f<T: Other>(x: &T): i32 {{ by_table(x) }}\n", with));
    assert!(out.contains("dyn Show"), "{}", out);
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

// ---- Every member a trait declares ------------------------------------------------

// An impl of a trait writes all of them. Nothing asked: an impl of a trait with
// two members that wrote one *was* an impl, so the type answered the trait, a
// `&dyn T` was made of it, and the table built for it had an entry for a member
// nobody had written a body for. That compiled, linked, and took the process
// down.
#[test]
fn an_impl_writes_every_member_the_trait_declares() {
    let with = "trait T {\n    fn f(&self): i32\n    fn g(&self): i32\n}\n\
                struct Q {\n    pub n: i32,\n}\n";
    clean(&format!(
        "{}impl T for Q {{\n    fn f(&self): i32 {{ self.n }}\n\
         \x20   fn g(&self): i32 {{ 0 }}\n}}\n",
        with));
    let out = refused(&format!("{}impl T for Q {{\n    fn f(&self): i32 {{ self.n }}\n}}\n", with));
    assert!(out.contains("this impl of `T` is missing g"), "{}", out);
    // And one that writes none at all, which was an impl too.
    let out = refused(&format!("{}impl T for Q {{}}\n", with));
    assert!(out.contains("missing f, g"), "{}", out);
}

// And a trait declares a *signature*: a member written with a body is refused
// rather than accepted and ignored, which is what it was.
//
// What a body there would be is the one every impl that wrote none falls back
// to, and writing it wants a `Self` to write it about -- a parameter this
// language has no spelling for.
#[test]
fn a_trait_member_is_a_signature_and_not_a_body() {
    let out = refused("trait T {\n    fn f(&self): i32 { 0 }\n}\n");
    assert!(out.contains("`f` is declared with a body"), "{}", out);
    assert!(out.contains("a trait declares a signature"), "{}", out);
    // And one written the other way is what a trait is made of.
    clean("trait T {\n    fn f(&self): i32\n}\n");
}

// ---- A collected value where a reference is wanted ---------------------------------

// "It is one word -- the address the collector handed back -- and it is reached
// through exactly as a reference is" (§2), so a `gc T` stands where a `&T`
// does. It did not: a collected value could only be handed to something written
// to take one, so an `fn sum(l: &List)` could not be called on a list the
// collector held -- and a recursive structure is the reason there is a
// collector at all.
#[test]
fn a_collected_value_stands_where_a_reference_does() {
    let with = "struct P {\n    pub n: i32,\n}\nfn read(p: &P): i32 { p.n }\n";
    clean(&format!("{}fn f(): i32 {{\n    let gc g = P {{ n: 5 }}\n    read(g)\n}}\n", with));
    // And a reference to one, which is what matching through a reference
    // binds: the `r` of an `L::Cons(n, r)` is a `&gc L`.
    clean(&format!(
        "{}fn f(g: &gc P): i32 {{ read(g) }}\n", with));
}

// Only a `&`, never a `*`. A `gc` copies, so two names may hold one handle, and
// handing out something that may be written through would be handing out one of
// two exclusive references to one value.
#[test]
fn a_collected_value_does_not_stand_where_a_write_is_wanted() {
    let out = refused(
        "struct P {\n    pub n: i32,\n}\n\
         fn write(p: *P) { p.n = 1 }\n\
         fn f() {\n    let gc g = P { n: 5 }\n    write(g)\n}\n",
    );
    assert!(out.contains("`gc P` and it takes `*P`"), "{}", out);
}

// The right of an assignment is a place an expectation reaches (§5), and was
// the one that did not: the conversions a `let` makes were refused where the
// value was reached by an `=`.
#[test]
fn the_right_of_an_assignment_converts_as_a_let_does() {
    // A value becoming one the collector holds, which is the case that found
    // it: a list built a turn at a time is `held = Cons(.., held)`.
    clean("struct P {\n    pub n: i32,\n}\n\
           fn f() {\n    var g: gc P = P { n: 1 }\n    g = P { n: 2 }\n}\n");
    // And an array becoming a view, which is the same rule said of the other
    // conversion.
    clean("fn f() {\n    let a: i32[3] = [1, 2, 3]\n    var v: &i32[] = &a\n    v = &a\n}\n");
}
