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
