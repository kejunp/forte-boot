// What agrees with what.

use super::*;
use crate::tir::tir_nodes::TIRRefOp;

fn spell(t: &Types, id: TyId) -> String {
    t.spell(id, &|item| format!("#{}", item))
}

// Interned: an equal type is an equal handle, which is what lets the checker
// compare two types without walking either.
#[test]
fn one_type_is_one_handle() {
    let mut t = Types::new();
    let a = t.prim(TIRPrim::I32);
    let b = t.prim(TIRPrim::I32);
    let c = t.prim(TIRPrim::Str);
    assert_eq!(a, b);
    assert_ne!(a, c);

    // And through a type that holds one: `Vec<i32>` twice is one entry.
    let one = t.intern(Ty::Named { item: 0, args: vec![a], regions: Vec::new() });
    let two = t.intern(Ty::Named { item: 0, args: vec![b], regions: Vec::new() });
    assert_eq!(one, two);
}

// A hole becomes whatever was put in it, and stays that afterwards. That is
// the whole of how a type is worked out rather than written.
#[test]
fn a_hole_is_filled_by_what_was_put_in_it() {
    let mut t = Types::new();
    let hole = t.fresh();
    let i32 = t.prim(TIRPrim::I32);
    assert_eq!(spell(&t, hole), "_");

    assert_eq!(t.unify(hole, i32), Ok(i32));
    assert_eq!(t.shallow(hole), i32);
    assert_eq!(spell(&t, hole), "i32");

    // Filled once, it disagrees like anything else.
    let str = t.prim(TIRPrim::Str);
    assert!(t.unify(hole, str).is_err());
}

// Two holes may agree before either is known, and filling one fills both.
#[test]
fn a_hole_may_be_filled_through_another() {
    let mut t = Types::new();
    let a = t.fresh();
    let b = t.fresh();
    assert!(t.unify(a, b).is_ok());
    let i32 = t.prim(TIRPrim::I32);
    assert!(t.unify(b, i32).is_ok());
    assert_eq!(t.shallow(a), i32);
}

// Inside a type, too: `Vec<_>` is settled by what is put in it.
#[test]
fn a_hole_inside_a_type_is_filled_from_outside() {
    let mut t = Types::new();
    let hole = t.fresh();
    let i32 = t.prim(TIRPrim::I32);
    let of_hole = t.intern(Ty::Named { item: 0, args: vec![hole], regions: Vec::new() });
    let of_i32 = t.intern(Ty::Named { item: 0, args: vec![i32], regions: Vec::new() });

    assert!(t.unify(of_hole, of_i32).is_ok());
    assert_eq!(t.shallow(hole), i32);
    let settled = t.deep(of_hole);
    assert_eq!(settled, of_i32);
}

// `never` has no values, so there is nothing it could disagree about: the
// `match` of section 3 types as an i32 because the arm that panics yields
// nothing at all.
#[test]
fn never_agrees_with_anything() {
    let mut t = Types::new();
    let never = t.never();
    let i32 = t.prim(TIRPrim::I32);
    let str = t.prim(TIRPrim::Str);
    assert_eq!(t.unify(never, i32), Ok(i32));
    assert_eq!(t.unify(str, never), Ok(str));
    // Two of them are still one of them.
    assert_eq!(t.unify(never, never), Ok(never));
}

// `null` belongs to every type (section 8): a loop nobody broke out of yields
// one, and it agrees with the `break x` that would have. This is the
// billion-dollar bet, and `NULL_BELONGS` is where it is taken.
#[test]
fn null_belongs_to_every_type() {
    let mut t = Types::new();
    let null = t.null();
    let i32 = t.prim(TIRPrim::I32);
    assert_eq!(NULL_BELONGS, true);
    assert_eq!(t.unify(null, i32), Ok(i32));
    assert_eq!(t.unify(i32, null), Ok(i32));
}

// Everything else has to be the same thing, all the way down.
#[test]
fn two_types_that_are_not_one_say_which_part_disagreed() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let str = t.prim(TIRPrim::Str);
    let of_i32 = t.intern(Ty::Named { item: 0, args: vec![i32], regions: Vec::new() });
    let of_str = t.intern(Ty::Named { item: 0, args: vec![str], regions: Vec::new() });

    // The report is the innermost disagreement and not the whole type: the
    // rest of `Vec<i32>` and `Vec<str>` is the same on both sides.
    assert_eq!(t.unify(of_i32, of_str), Err(Mismatch { found: i32, wanted: str }));
    // A different declaration is a different type however alike they read.
    let other = t.intern(Ty::Named { item: 1, args: vec![i32], regions: Vec::new() });
    assert!(t.unify(of_i32, other).is_err());
}

// The length is part of an array's type, which is what lets the checker hold
// anyone to a size.
#[test]
fn an_arrays_length_is_part_of_it() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let eight = t.intern(Ty::Array { elem: i32, len: 8 });
    let nine = t.intern(Ty::Array { elem: i32, len: 9 });
    let also_eight = t.intern(Ty::Array { elem: i32, len: 8 });
    assert!(t.unify(eight, also_eight).is_ok());
    assert!(t.unify(eight, nine).is_err());
}

// `&` and `*` decide whether writing through is allowed, so they are two
// types. The region is not compared: how long a reference is good for is a
// pass of its own, and a type that agrees but for its region agrees.
#[test]
fn a_reference_agrees_by_what_it_allows_and_not_by_how_long() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let read = t.intern(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: i32 });
    let write = t.intern(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: i32 });
    let read_longer = t.intern(Ty::Ref { op: TIRRefOp::Imm, life: 7, inner: i32 });
    assert!(t.unify(read, write).is_err());
    assert!(t.unify(read, read_longer).is_ok());
}

// A fn agrees by what it takes, what it gives back, and whether calling it
// needs a guard.
#[test]
fn a_fn_type_agrees_by_all_three() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let null = t.null();
    let safe = t.intern(Ty::Fn { params: vec![i32], ret: null, is_unsafe: false });
    let same = t.intern(Ty::Fn { params: vec![i32], ret: null, is_unsafe: false });
    let guarded = t.intern(Ty::Fn { params: vec![i32], ret: null, is_unsafe: true });
    let longer = t.intern(Ty::Fn { params: vec![i32, i32], ret: null, is_unsafe: false });
    assert!(t.unify(safe, same).is_ok());
    assert!(t.unify(safe, guarded).is_err());
    assert!(t.unify(safe, longer).is_err());
}

// A hole filled with a type that holds it is a type with no bottom, and every
// walk of it afterwards runs forever. So it is refused instead.
#[test]
fn a_hole_may_not_be_filled_with_itself() {
    let mut t = Types::new();
    let hole = t.fresh();
    let of_hole = t.intern(Ty::Named { item: 0, args: vec![hole], regions: Vec::new() });
    assert!(t.unify(hole, of_hole).is_err());
    // And it is still a hole afterwards, not half-filled.
    assert_eq!(t.shallow(hole), hole);
}

// One mistake is one message: an `Error` agrees with anything, so what was
// already reported does not report again further out.
#[test]
fn an_error_does_not_report_twice() {
    let mut t = Types::new();
    let error = t.error();
    let i32 = t.prim(TIRPrim::I32);
    let of_error = t.intern(Ty::Named { item: 0, args: vec![error], regions: Vec::new() });
    let of_i32 = t.intern(Ty::Named { item: 0, args: vec![i32], regions: Vec::new() });
    assert!(t.unify(error, i32).is_ok());
    assert!(t.unify(of_error, of_i32).is_ok());
}

// Asking without committing: what an overload has to do to try each candidate
// and keep the one that fits.
#[test]
fn agreeing_fills_nothing_in() {
    let mut t = Types::new();
    let hole = t.fresh();
    let i32 = t.prim(TIRPrim::I32);
    let str = t.prim(TIRPrim::Str);
    assert!(t.agrees(hole, i32));
    assert!(t.agrees(hole, str));
    // Neither try left a mark, so it is still open for the one that is taken.
    assert_eq!(t.shallow(hole), hole);
    assert!(t.unify(hole, str).is_ok());
    assert_eq!(t.shallow(hole), str);
}

// A call to a generic puts arguments where the parameters stood.
#[test]
fn substituting_puts_the_arguments_in() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let str = t.prim(TIRPrim::Str);
    let first = t.intern(Ty::Param { name: "T".to_string(), index: 0 });
    let second = t.intern(Ty::Param { name: "U".to_string(), index: 1 });
    let pair = t.intern(Ty::Tuple(vec![first, second]));

    let put = t.substitute(pair, &[i32, str]);
    assert_eq!(spell(&t, put), "(i32, str)");
    // The original is untouched: a signature is instantiated many times.
    assert_eq!(spell(&t, pair), "(T, U)");
    // An index with no argument stands, so a half-applied signature still
    // walks rather than panicking.
    let half = t.substitute(pair, &[i32]);
    assert_eq!(spell(&t, half), "(i32, U)");
}

// Two parameters are the same one where they stand in the same place: `f<T>`
// and `g<U>` each have a first, and a name is not what tells them apart.
#[test]
fn two_parameters_agree_by_their_place() {
    let mut t = Types::new();
    let t0 = t.intern(Ty::Param { name: "T".to_string(), index: 0 });
    let u0 = t.intern(Ty::Param { name: "U".to_string(), index: 0 });
    let u1 = t.intern(Ty::Param { name: "U".to_string(), index: 1 });
    assert!(t.unify(t0, u0).is_ok());
    assert!(t.unify(t0, u1).is_err());
}

// What the typed tree gets: every hole followed, and the ones that were never
// filled handed back so the caller -- which has the spans -- can say where.
#[test]
fn finishing_settles_every_hole_and_names_the_rest() {
    let mut t = Types::new();
    let filled = t.fresh();
    let open = t.fresh();
    let i32 = t.prim(TIRPrim::I32);
    let of_filled = t.intern(Ty::Named { item: 0, args: vec![filled], regions: Vec::new() });
    t.unify(filled, i32).expect("a hole takes what is put in it");
    let of_open = t.intern(Ty::Named { item: 0, args: vec![open], regions: Vec::new() });

    let (arena, unsettled) = t.finish();
    // The one nobody filled is reported, by the handle a caller keyed its span
    // by.
    assert_eq!(unsettled.len(), 1);
    // The one that was filled is the type it was filled with, all the way down.
    assert_eq!(arena[of_filled], Ty::Named { item: 0, args: vec![i32], regions: Vec::new() });
    // And the one that was not is an `Error`, so nothing below carries a case
    // for a type that was never settled.
    let Ty::Named { args, .. } = &arena[of_open] else { panic!() };
    assert_eq!(arena[args[0]], Ty::Error);
}

// A type as a reader wrote it, for a message.
#[test]
fn a_type_is_spelled_the_way_it_was_written() {
    let mut t = Types::new();
    let i32 = t.prim(TIRPrim::I32);
    let u8 = t.prim(TIRPrim::U8);
    let str = t.prim(TIRPrim::Str);
    let null = t.null();
    let cases: Vec<(Ty, &str)> = vec![
        (Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: i32 }, "&i32"),
        (Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: i32 }, "*i32"),
        (Ty::Ptr(u8), "ptr u8"),
        (Ty::GC(str), "gc str"),
        (Ty::Array { elem: i32, len: 8 }, "i32[8]"),
        (Ty::Run(i32), "i32[]"),
        (Ty::Tuple(vec![i32, str]), "(i32, str)"),
        (Ty::Fn { params: vec![i32], ret: null, is_unsafe: false }, "fn(i32): null"),
        (Ty::Fn { params: vec![i32], ret: null, is_unsafe: true }, "unsafe fn(i32): null"),
        // By the name a reader wrote, not by its place: a message about `T`
        // should say `T`.
        (Ty::Param { name: "T".to_string(), index: 3 }, "T"),
        (Ty::Error, "?"),
    ];
    for (ty, want) in cases {
        let id = t.intern(ty.clone());
        assert_eq!(spell(&t, id), want, "{:?}", ty);
    }
    // A named type is asked what it is called, this module holding no items.
    let vec_of = t.intern(Ty::Named { item: 4, args: vec![i32, str], regions: Vec::new() });
    assert_eq!(
        t.spell(vec_of, &|item| if item == 4 { "Map".to_string() } else { "?".into() }),
        "Map<i32, str>"
    );
}
