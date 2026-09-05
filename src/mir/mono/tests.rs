// A generic made once for each set of types it is used with, and not twice for
// the same set.
//
// These go through the whole compiler rather than through a hand-built SIR, for
// the reason `fixture::compiled` gives: what is being tested is what happens to
// a type parameter, and a type parameter reaching the SIR at all is several
// passes agreeing about what one is. Writing that by hand would be writing down
// what those passes are believed to do.

use super::super::fixture::compiled;
use super::*;

fn made(source: &str) -> Made {
    let (ttir, sir) = compiled(source);
    monomorphise(&ttir, &sir, false)
}

// Whether any body still has a type parameter standing in it, which is the one
// thing this pass exists to make untrue.
fn parameters_left(m: &Made) -> bool {
    m.sir.bodies.iter().any(|body| {
        body.values
            .iter()
            .map(|held| held.ty)
            .chain(body.slots.iter().map(|slot| slot.ty))
            .any(|ty| matches!(m.ttir.types.get(ty), Some(Ty::Param { .. })))
    })
}

// ---- What a program starts at ----------------------------------------------

// A fn nothing reaches is a fn nothing compiles.
//
// The roots are where the program begins and nothing else -- `main`, or the
// `%test`s of a test build -- so everything else arrives by being called.
#[test]
fn a_fn_nothing_calls_is_not_compiled() {
    let source = "fn used(): i32 { 1 }\n\
                  fn never_called(): i32 { 2 }\n\
                  fn main(): i32 { used() }\n";
    let (ttir, sir) = compiled(source);
    let m = monomorphise(&ttir, &sir, false);
    assert!(said(&m, "main"), "{:#?}", m.symbols);
    assert!(said(&m, "used"), "{:#?}", m.symbols);
    assert!(!said(&m, "never_called"), "{:#?}", m.symbols);
}

// A suite with nowhere to begin is not being run: a library on its own, or a
// `--emit` of one to look at. Pruning it to nothing would answer a question
// nobody asked, so where there is no beginning every fn is one.
#[test]
fn a_suite_with_no_beginning_keeps_every_fn() {
    let source = "pub fn one(): i32 { 1 }\npub fn two(): i32 { 2 }\n";
    let (ttir, sir) = compiled(source);
    let m = monomorphise(&ttir, &sir, false);
    assert!(said(&m, "one"), "{:#?}", m.symbols);
    assert!(said(&m, "two"), "{:#?}", m.symbols);
}

// "Collected and run on its own rather than compiled into an ordinary build"
// (section 2), which is now both halves: a test is no root of an ordinary
// build, and an ordinary build's `main` is no root of a test one.
#[test]
fn a_test_and_a_main_are_each_the_others_dead_code() {
    let source = "fn only_a_test_calls_this(): i32 { 2 }\n\
                  fn only_main_calls_this(): i32 { 3 }\n\
                  %test\n\
                  fn a_test() {\n    only_a_test_calls_this();\n}\n\
                  fn main(): i32 { only_main_calls_this() }\n";
    let (ttir, sir) = compiled(source);

    let ordinary = monomorphise(&ttir, &sir, false);
    assert!(!said(&ordinary, "a_test"), "{:#?}", ordinary.symbols);
    assert!(!said(&ordinary, "only_a_test_calls_this"), "{:#?}", ordinary.symbols);
    assert!(said(&ordinary, "only_main_calls_this"), "{:#?}", ordinary.symbols);

    let tests = monomorphise(&ttir, &sir, true);
    assert!(said(&tests, "a_test"), "{:#?}", tests.symbols);
    assert!(said(&tests, "only_a_test_calls_this"), "{:#?}", tests.symbols);
    assert!(!said(&tests, "only_main_calls_this"), "{:#?}", tests.symbols);
}

// A release is not called by anything in the SIR -- `mir::lower::glue` writes
// the call long after this pass and writes it by name -- so a `drop` this pass
// never made is a symbol nothing defines. They are kept whatever reaches them.
#[test]
fn a_written_drop_is_kept_though_nothing_calls_it() {
    let source = "trait Drop {\n    fn drop(self)\n}\n\
                  struct H {\n    pub n: i32,\n}\n\
                  impl Drop for H {\n    fn drop(self) {\n    }\n}\n\
                  fn main(): i32 { 0 }\n";
    let (ttir, sir) = compiled(source);
    let m = monomorphise(&ttir, &sir, false);
    // `said` reads the last name of a symbol, and a method's does not end
    // there: the impl's type follows it. So this one looks for the name where
    // it stands, which is in the middle.
    assert!(m.symbols.iter().any(|held| held.contains("4drop")), "{:#?}", m.symbols);
}

// Whether a fn of this name compiled to anything. The written name is matched
// with the length the mangler puts in front of it, so that `a_test` is not
// found inside `only_a_test_calls_this`.
fn said(m: &Made, name: &str) -> bool {
    let held = format!("{}{}", name.len(), name);
    m.symbols.iter().any(|symbol| symbol.ends_with(&held))
}

// ---- Nothing generic -------------------------------------------------------

#[test]
fn a_program_with_no_generics_is_one_body_per_fn() {
    let m = made("fn g(): i32 { 1 }\nfn f(): i32 { g() }\n");
    assert_eq!(m.instances, 0, "nothing was instantiated");
    assert!(m.refused.is_empty(), "{:#?}", m.refused);
    assert_eq!(m.sir.bodies.len(), 2, "{:#?}", m.symbols);
    assert_eq!(m.symbols.len(), m.sir.bodies.len(), "one name each");
}

#[test]
fn every_body_is_named_by_the_mangling() {
    let m = made("fn f(): i32 { 1 }\n");
    assert!(
        m.symbols.iter().all(|name| name.starts_with("__F")),
        "{:#?}",
        m.symbols
    );
}

// ---- One instance per set of types -----------------------------------------

#[test]
fn a_generic_used_once_is_made_once() {
    let m = made("fn id<T>(x: T): T { x }\nfn f(): i32 { id(1) }\n");
    assert!(m.refused.is_empty(), "{:#?}", m.refused);
    assert_eq!(m.instances, 1, "{:#?}", m.symbols);
    assert!(!parameters_left(&m), "a `T` is still standing");
}

// §8: "each instance wants its own and the arguments have to reach the name."
// So two instances are two symbols, and what tells them apart is the type.
#[test]
fn two_types_are_two_instances_with_two_names() {
    let m = made(
        "fn id<T>(x: T): T { x }\n\
         fn f(): i32 { id<i32>(1) }\n\
         fn g(): i64 { id<i64>(1) }\n",
    );
    assert!(m.refused.is_empty(), "{:#?}", m.refused);
    assert_eq!(m.instances, 2, "{:#?}", m.symbols);
    let mut held: Vec<&String> = m.symbols.iter().filter(|name| name.contains("id")).collect();
    held.sort();
    held.dedup();
    assert_eq!(held.len(), 2, "two names, not one: {:#?}", m.symbols);
    assert!(!parameters_left(&m));
}

// The bound that stops a recursive declaration: an instance already made is
// found rather than made again.
#[test]
fn one_type_used_twice_is_one_instance() {
    let m = made(
        "fn id<T>(x: T): T { x }\n\
         fn f(): i32 { id<i32>(1) }\n\
         fn g(): i32 { id<i32>(2) }\n",
    );
    assert_eq!(m.instances, 1, "made once for both: {:#?}", m.symbols);
}

// A generic nothing reaches is not compiled at all. There is nothing to
// compile: what its parameters stand for is never said.
#[test]
fn a_generic_nothing_uses_is_never_made() {
    let m = made("fn id<T>(x: T): T { x }\nfn f(): i32 { 1 }\n");
    assert_eq!(m.instances, 0);
    assert_eq!(m.sir.bodies.len(), 1, "only `f`: {:#?}", m.symbols);
}

// A fn generic only over lifetimes is compiled once, like anything else: a
// region has no width, so nothing about the machine turns on which one it is.
#[test]
fn a_lifetime_is_not_a_type_parameter() {
    let m = made("fn first<'a>(x: &'a i32): i32 { 1 }\nfn f(): i32 { 1 }\n");
    assert_eq!(m.instances, 0, "{:#?}", m.symbols);
    assert_eq!(m.sir.bodies.len(), 2, "and it is still compiled: {:#?}", m.symbols);
}

// ---- What the instances are named ------------------------------------------

// The instruction that names a declaration is what a lowering has to turn into
// a symbol, and after this pass the instruction alone no longer says which
// instance it meant -- so the answer is kept beside it.
#[test]
fn the_instruction_that_names_a_declaration_is_given_its_symbol() {
    let m = made("fn g(): i32 { 1 }\nfn f(): i32 { g() }\n");
    assert!(
        m.symbol_of.values().any(|name| name.contains("1g")),
        "nothing named `g`: {:#?}",
        m.symbol_of
    );
}

#[test]
fn a_generic_instruction_is_given_the_instance_and_not_the_declaration() {
    let m = made(
        "fn id<T>(x: T): T { x }\n\
         fn f(): i32 { id<i32>(1) }\n",
    );
    let named: Vec<&String> = m.symbol_of.values().filter(|name| name.contains("2id")).collect();
    assert!(!named.is_empty(), "nothing named `id`: {:#?}", m.symbol_of);
    assert!(
        named.iter().all(|name| m.symbols.contains(name)),
        "a name that is no body: {:#?} against {:#?}",
        named,
        m.symbols
    );
}

// ---- The one thing that is refused -----------------------------------------

// `f<T>` calling `f<(T, T)>` asks for a new type every time, so no instance is
// ever the one already made and the queue never empties. Nothing else in this
// compiler after `sema` turns a program down; this does, because the other
// answer is to run until the memory is gone.
#[test]
fn a_chain_of_instances_that_never_ends_is_refused() {
    let m = made(
        "fn f<T>(x: T): i32 { f((x, 1)) }\n\
         fn g(): i32 { f(1) }\n",
    );
    assert!(!m.refused.is_empty(), "it should not have finished: {:#?}", m.symbols);
    assert!(
        m.refused.iter().any(|said| said.contains("no end")),
        "{:#?}",
        m.refused
    );
}

// And a fn that calls itself with the same types is not that: the instance is
// already made, so it is found and the walk stops.
#[test]
fn a_generic_that_calls_itself_with_its_own_types_is_made_once() {
    let m = made(
        "fn f<T>(x: T, n: i32): i32 { if n > 0 { f(x, n - 1) } else { 0 } }\n\
         fn g(): i32 { f(1, 3) }\n",
    );
    assert!(m.refused.is_empty(), "{:#?}", m.refused);
    assert_eq!(m.instances, 1, "{:#?}", m.symbols);
}

// ---- What the arena has to still be ----------------------------------------

// Interning looks for the type before it adds one, so a type an instance needed
// that was already there is the one that was already there. The arena reaching
// this pass is not itself free of duplicates -- `sema` leaves a few -- so what
// is checked is that this pass adds none, which is what "one id per type" needs
// from it.
fn duplicates(types: &[Ty]) -> usize {
    (0..types.len()).filter(|&at| types[at + 1..].contains(&types[at])).count()
}

#[test]
fn no_type_is_added_that_was_already_there() {
    let source = "fn id<T>(x: T): T { x }\n\
                  fn f(): i32 { id<i32>(1) }\n\
                  fn g(): i64 { id<i64>(1) }\n";
    let (ttir, _) = compiled(source);
    let m = made(source);
    assert_eq!(
        duplicates(&m.ttir.types),
        duplicates(&ttir.types),
        "this pass added a type the arena already held"
    );
}

// Nothing is added but types. An instance is a body, and a body is not a
// declaration -- so the items are the ones the source wrote.
#[test]
fn no_declaration_is_added() {
    let source = "fn id<T>(x: T): T { x }\nfn f(): i32 { id<i32>(1) }\n";
    let (ttir, _) = compiled(source);
    let m = made(source);
    assert_eq!(m.ttir.items.len(), ttir.items.len());
    assert!(m.ttir.types.len() >= ttir.types.len(), "and types may be added");
}


