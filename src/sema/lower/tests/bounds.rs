// Trait bounds: what a declaration asks of a caller, and which types answer.

use super::*;

// ---- Trait bounds ---------------------------------------------------------

// A parameter is held to what it was declared with, and an impl is how a type
// says it answers: "an impl makes methods for its type".
#[test]
fn a_parameter_is_held_to_its_bound() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Buf {\n    pub n: i32,\n}\n\
                struct Raw {\n    pub n: i32,\n}\n\
                impl Show for Buf {\n    fn show(&self): str { \"buf\" }\n}\n\
                fn tell<T: Show>(x: T): str { \"x\" }\n";
    clean(&format!("{}fn f(b: Buf): str {{ tell(b) }}\n", with));

    let out = refused(&format!("{}fn f(r: Raw): str {{ tell(r) }}\n", with));
    assert!(out.contains("`Raw` does not answer `Show`"), "{}", out);
    assert!(out.contains("`T` is held to it here"), "{}", out);
    assert!(out.contains("`impl Show for Raw` is how a type says it does"), "{}", out);
}

// "`fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing", so a
// predicate about a parameter is folded into that parameter's bounds and the
// two spellings come out as one.
#[test]
fn a_where_about_a_parameter_is_folded_into_it() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Raw {\n    pub n: i32,\n}\n";
    let inline = refused(&format!(
        "{}fn tell<T: Show>(x: T): str {{ \"x\" }}\nfn f(r: Raw): str {{ tell(r) }}\n",
        with
    ));
    let written = refused(&format!(
        "{}fn tell<T>(x: T): str where T: Show {{ \"x\" }}\nfn f(r: Raw): str {{ tell(r) }}\n",
        with
    ));
    assert!(inline.contains("does not answer `Show`"), "{}", inline);
    assert_eq!(inline, written, "the two spellings say the same thing");
}

// Written arguments are held to the bounds as worked-out ones are.
#[test]
fn a_written_type_argument_is_held_to_the_bound() {
    let with = "trait Show {\n    fn show(&self): str;\n}\n\
                struct Raw {\n    pub n: i32,\n}\n\
                fn tell<T: Show>(x: T): str { \"x\" }\n";
    let out = refused(&format!("{}fn f(r: Raw): str {{ tell<Raw>(r) }}\n", with));
    assert!(out.contains("`Raw` does not answer `Show`"), "{}", out);
}

// A generic holding another generic to a trait is answered by whoever calls it
// and not here: `T` says it answers `Show`, so passing it on is fine.
#[test]
fn a_parameter_answers_a_bound_it_was_declared_with() {
    clean(
        "trait Show {\n    fn show(&self): str;\n}\n\
         fn tell<T: Show>(x: T): str { \"x\" }\n\
         fn pass<U: Show>(y: U): str { tell(y) }\n",
    );
}

// The bounds are on the tree for whatever reads it: `is_copy` in
// `sema::borrows` asks exactly this.
#[test]
fn the_bounds_are_kept_on_the_declaration() {
    let ttir = clean(
        "trait Ord {\n    fn cmp(&self): i32;\n}\n\
         fn sort<T: Ord>(x: T): T { x }\n",
    );
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "sort" => Some(f),
        _ => None,
    }).expect("sort");
    let TTIRGeneric::Type { name, bounds } = &f.generics[0] else { panic!() };
    assert_eq!(name, "T");
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0], TTIRBound::Trait(_)));
}

// A `where` about something that is not a parameter has no parameter to fold
// into, and is kept as the predicate it is.
#[test]
fn a_where_about_a_built_type_is_kept() {
    let ttir = clean(
        "trait Show {\n    fn show(&self): str;\n}\n\
         struct Vec<T> {\n    pub n: i32,\n}\n\
         fn f<T>(x: T): i32 where Vec<T>: Show { 1 }\n",
    );
    let held = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "f" => Some(f),
        _ => None,
    }).expect("f");
    assert_eq!(held.wheres.len(), 1, "{:?}", held.wheres);
    assert!(matches!(held.wheres[0].subject, TTIRSubject::Type(_)));
    // And the parameter it is not about kept none of it.
    let TTIRGeneric::Type { bounds, .. } = &held.generics[0] else { panic!() };
    assert!(bounds.is_empty());
}

// ---- What an impl answers ---------------------------------------------------

// An `impl ... for` names a trait, and a name that is not one is refused. It
// matters most for the two the compiler knows by name: an `impl Drop for Buf`
// with no `trait Drop` in scope would otherwise look like a type with a
// destructor and be one without.
#[test]
fn an_impl_answers_a_trait_and_not_a_name() {
    let out = refused("struct Buf {\n    pub n: i32,\n}\nimpl Nope for Buf {\n}\n");
    assert!(out.contains("no trait is called `Nope`"), "{}", out);

    let out = refused(
        "struct Buf {\n    pub n: i32,\n}\nstruct Other {\n    pub n: i32,\n}\n\
         impl Other for Buf {\n}\n",
    );
    assert!(out.contains("`Other` is not a trait"), "{}", out);

    // And the help says the thing worth saying for the two by name.
    let out = refused("struct Buf {\n    pub n: i32,\n}\nimpl Drop for Buf {\n}\n");
    assert!(out.contains("`Copy` and `Drop` are traits like any other"), "{}", out);

    // Declared, and it stands.
    clean(
        "trait Drop {\n    fn drop(*self);\n}\n\
         struct Buf {\n    pub n: i32,\n}\n\
         impl Drop for Buf {\n    pub fn drop(*self) {\n    }\n}\n",
    );
}


// ---- Calling through a bound -----------------------------------------------

// What the bound is *for*. Every test above asks whether a type answers a
// trait; none of them called the method the trait declares, which is the thing
// a bound exists to let a generic do.
//
// The member found is the trait's. Which impl answers it is not a question
// `sema` can settle -- what the parameter stands for is the caller's to say --
// so it is settled where the caller's type is known, in `mir::mono`.
#[test]
fn a_method_of_a_bound_is_found_on_the_parameter() {
    let with = "trait Show {\n    fn show(&self): i64;\n}\n\
                struct Buf {\n    pub n: i32,\n}\n\
                impl Show for Buf {\n    fn show(&self): i64 { 1 }\n}\n";
    clean(&format!("{}fn tell<T: Show>(x: &T): i64 {{ x.show() }}\n", with));
}

// And a parameter held to nothing has no methods at all: the message is the
// ordinary one, because there is no bound to have looked in.
#[test]
fn a_parameter_with_no_bound_has_no_methods() {
    let out = refused("fn tell<T>(x: &T): i64 { x.show() }\n");
    assert!(out.contains("has no field `show`"), "{}", out);
}

// Two bounds each declaring the name is a mistake said out loud rather than one
// of them quietly winning: there is no rule for choosing, and none is invented.
#[test]
fn a_name_two_bounds_both_declare_is_refused() {
    let out = refused(
        "trait Show {\n    fn tell(&self): i64;\n}\n\
         trait Say {\n    fn tell(&self): i64;\n}\n\
         fn both<T: Show + Say>(x: &T): i64 { x.tell() }\n",
    );
    assert!(out.contains("more than one `tell`"), "{}", out);
    assert!(out.contains("`Show`") && out.contains("`Say`"), "{}", out);
}

// ---- `Self` ----------------------------------------------------------------

// "`Self` is the type an impl is about, and the type that answers a trait."
// A trait's is a parameter -- its first -- so a signature written about it is
// one the checker can hold an impl to, and a call through a bound fills it
// from the receiver by the same unification that fills an `impl<T>`'s `T`.
#[test]
fn self_in_a_trait_is_the_type_that_answers_it() {
    clean(
        "trait Key {\n\
         \x20   fn same(&self, other: &Self): bool;\n\
         }\n\
         impl Key for i64 {\n\
         \x20   fn same(&self, other: &i64): bool { self == other }\n\
         }\n\
         fn holds<K: Key>(a: &K, b: &K): bool { a.same(b) }\n",
    );
}

// And `&self` is that same parameter, not a second one beside it. It used to
// be made afresh at the end of the member's own, so a body's receiver and a
// written `&Self` were two parameters that never met.
#[test]
fn a_receiver_and_a_written_self_are_one_type() {
    let out = clean(
        "trait Key {\n\
         \x20   fn same(&self, other: &Self): bool;\n\
         }\n",
    );
    let held = out
        .items
        .iter()
        .find_map(|item| match &item.kind {
            TTIRItemKind::Fn(f) if f.name == "same" => Some(f.ty),
            _ => None,
        })
        .expect("the member");
    let Ty::Fn { params, .. } = &out.types[held] else { panic!("{:?}", out.types[held]) };
    let inner = |ty: TyId| match &out.types[ty] {
        Ty::Ref { inner, .. } => out.types[*inner].clone(),
        other => other.clone(),
    };
    assert_eq!(inner(params[0]), inner(params[1]), "{:#?}", out.types);
    assert!(matches!(inner(params[0]), Ty::Param { index: 0, .. }), "{:?}", inner(params[0]));
}

// Inside an impl it is the type written in the header, which is a type and not
// a parameter: there is nothing left to work out. It stands where a type does
// and at the head of a struct literal.
#[test]
fn self_in_an_impl_is_the_type_it_is_about() {
    clean(
        "struct P { pub x: i64 }\n\
         impl P {\n\
         \x20   pub fn twin(&self): Self { Self { x: self.x } }\n\
         }\n",
    );
}

// And nowhere else. A `Self` with no impl and no trait around it names
// nothing, and used to come out as "no type is called `Self`" -- which is true
// and says nothing about why.
#[test]
fn self_outside_a_trait_or_an_impl_names_nothing() {
    let out = refused("fn f(): Self { 0 }\n");
    assert!(out.contains("`Self` is written outside a trait or an impl"), "{}", out);
}

// A trait whose members write `Self` past the receiver is not one an object is
// made of: a table is one address per member and the object holds one type, so
// a member wanting a *second* `Self` is asking for a type the object threw
// away.
#[test]
fn no_object_is_made_of_a_trait_that_writes_self_past_its_receiver() {
    let out = refused(
        "trait Key {\n\
         \x20   fn same(&self, other: &Self): bool;\n\
         }\n\
         impl Key for i64 {\n\
         \x20   fn same(&self, other: &i64): bool { self == other }\n\
         }\n\
         fn f(n: &i64) {\n\
         \x20   let d: &dyn Key = n\n\
         }\n",
    );
    assert!(out.contains("no object is made of `Key`"), "{}", out);
    assert!(out.contains("writes `Self` past its receiver"), "{}", out);
}

// The receiver is the exception and the reason the whole thing works: it is the
// word beside the table. So a trait that writes `Self` there and nowhere else
// is an object as it always was.
#[test]
fn a_trait_that_writes_self_only_as_its_receiver_is_still_an_object() {
    clean(
        "trait Key {\n\
         \x20   fn hash(&self): i64;\n\
         }\n\
         impl Key for i64 {\n\
         \x20   fn hash(&self): i64 { self }\n\
         }\n\
         fn f(n: &i64) {\n\
         \x20   let d: &dyn Key = n\n\
         }\n",
    );
}
