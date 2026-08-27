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
