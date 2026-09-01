// The names, and the two rules about them that a link error would otherwise
// teach the hard way: they are all different, and the ones built from a type
// are built the way every other name is.

use super::*;

fn every_fixed_name() -> Vec<&'static str> {
    vec![
        INIT,
        ALLOC,
        GC_ALLOC,
        COLLECT,
        WRITE,
        COPY,
        MAP_NEW,
        HASHMAP_NEW,
        MAP_INSERT,
        HASHMAP_INSERT,
        SET_NEW,
        HASHSET_NEW,
        SET_INSERT,
        HASHSET_INSERT,
        ITER_VALID,
        ITER_ELEM,
        ITER_STEP,
    ]
}

// Two routines under one name is one routine, and which of the two it turned
// out to be would be settled by whatever was linked last.
#[test]
fn no_two_routines_share_a_name() {
    let held = every_fixed_name();
    for (at, name) in held.iter().enumerate() {
        assert!(!held[at + 1..].contains(name), "{} is used twice", name);
    }
}

// The prefix is what keeps them out of the way of anything a program declares.
// A mangled name begins with `__F`, `__S`, `__E` and the rest, and a written
// one cannot begin with two underscores and a lower-case letter by accident.
#[test]
fn every_routine_is_under_the_runtime_prefix() {
    for name in every_fixed_name() {
        assert!(name.starts_with("__rt_"), "{} is not marked as the runtime's", name);
    }
}

// Which one you named says how it behaves (§8), so the two kinds are two
// routines and not one routine told which it is.
#[test]
fn the_hashed_kind_is_a_different_routine() {
    assert_ne!(map_new(true), map_new(false));
    assert_ne!(map_insert(true), map_insert(false));
    assert_ne!(set_new(true), set_new(false));
    assert_ne!(set_insert(true), set_insert(false));
}

// There is no `start`. `IterStart` is a `Const(-1)` whatever is being walked,
// so the contract is that stepping from -1 lands on the first -- and a symbol
// nothing emits is a symbol that would be missing from the library or, worse,
// present and never called.
#[test]
fn the_cursor_has_three_routines_and_not_four() {
    let held = every_fixed_name();
    assert!(!held.iter().any(|name| name.ends_with("iter_start")));
    assert_eq!(held.iter().filter(|name| name.contains("iter_")).count(), 3);
}

// ---- The releases ----------------------------------------------------------

// One per type, named the way a fn is: the length of the part and then the
// part. Nothing here has to agree with `Mangler` by eye -- both call `part`.
#[test]
fn a_release_is_named_after_the_type_it_releases() {
    assert_eq!(glue("i32"), "__D3i32");
    assert_eq!(glue("t::Point"), "__D8t::Point");
}

#[test]
fn two_types_have_two_releases() {
    assert_ne!(glue("i32"), glue("i64"));
}

// The length in front is what keeps one part from running into the next, so two
// spellings that would otherwise read the same still do not.
#[test]
fn the_length_keeps_one_name_out_of_another() {
    assert_ne!(glue("ab"), glue("a"));
    assert_ne!(glue("a1"), glue("a"));
}

// ---- The strings -----------------------------------------------------------

#[test]
fn every_literal_in_the_pool_has_its_own_name() {
    assert_ne!(text(0), text(1));
    assert!(text(0).starts_with("__S"));
}
