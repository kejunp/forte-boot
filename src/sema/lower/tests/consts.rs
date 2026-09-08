// What a `const` is worth, and what a global starts as.
//
// The property is one thing said two ways. A const folds, so nothing downstream
// ever sees its name; a global does not fold -- it is a place -- so what is
// worked out for it is the value it begins with, and it is put on the item for
// the back end to make a segment out of.
//
// A const that folds is observed by what is left in the tree: `paths::const_lit`
// puts the literal where the name was, so a folded const leaves a `Literal` and
// no `Item` naming it.

use super::*;

// What `main` was compiled to holds this literal somewhere.
fn folds_to(source: &str, want: TIRLit) {
    let ttir = clean(source);
    let found = ttir.exprs.iter().any(|e| match &e.kind {
        TTIRExprKind::Literal(held) => *held == want,
        _ => false,
    });
    assert!(found, "no {:?} in\n{}\n{:#?}", want, source, ttir.exprs);
}

fn using(value: &str) -> String {
    format!("const N: i64 = {}\nfn main(): i64 {{ N }}\n", value)
}

// ---- A const folds whatever it was written as -------------------------------

// The case §8 asked about: a bare literal folded and nothing else did.
#[test]
fn arithmetic_folds() {
    folds_to(&using("6 * 7"), TIRLit::Int(42));
    folds_to(&using("100 - 58"), TIRLit::Int(42));
    folds_to(&using("(2 + 3) * (10 - 4)"), TIRLit::Int(30));
    folds_to(&using("100 / 7"), TIRLit::Int(14));
    folds_to(&using("100 % 7"), TIRLit::Int(2));
}

#[test]
fn shifts_and_bits_fold() {
    folds_to(&using("1 << 10"), TIRLit::Int(1024));
    folds_to(&using("1024 >> 4"), TIRLit::Int(64));
    folds_to(&using("255 & 15"), TIRLit::Int(15));
    folds_to(&using("240 | 15"), TIRLit::Int(255));
    folds_to(&using("255 ^ 15"), TIRLit::Int(240));
}

#[test]
fn a_sign_is_folded_and_is_not_a_subtraction() {
    folds_to(&using("-5 + 100"), TIRLit::Int(95));
    folds_to(&using("-(3 * 4)"), TIRLit::Int(-12));
}

// A const may be written in terms of one already declared, which is the whole
// of what makes a table of them worth writing.
#[test]
fn a_const_may_name_another_declared_before_it() {
    folds_to(
        "const A: i64 = 6\nconst B: i64 = A * 7\nfn main(): i64 { B }\n",
        TIRLit::Int(42),
    );
}

// A cast is arithmetic here too: it is how a character becomes a number.
#[test]
fn a_cast_between_numbers_folds() {
    folds_to("const N: i64 = 'a' as i64\nfn main(): i64 { N }\n", TIRLit::Int(97));
    folds_to("const N: i64 = 3.9 as i64\nfn main(): i64 { N }\n", TIRLit::Int(3));
}

// ---- And what does not fold --------------------------------------------------

// A division by zero is a program with a mistake in it, and folding it would be
// inventing the answer. It is said out loud where it is written, which it was
// not: the evaluator declines it by giving nothing back, the same answer it
// gives for a shape it cannot read, and what a use of the const then got was an
// undefined symbol at the link step.
#[test]
fn a_division_by_zero_is_said_and_not_folded() {
    let out = refused(&using("7 / 0"));
    assert!(out.contains("this divides by nought"), "{}", out);
    // And a remainder, which traps on the same machines for the same reason.
    let out = refused(&using("7 % 0"));
    assert!(out.contains("this divides by nought"), "{}", out);
    // Not a float, which is an infinity here and not a trap -- so it folds and
    // there is nothing to say about it.
    clean("const N: f64 = 1.0 / 0.0\nfn main(): i64 { 0 }\n");
}

// And a shape the evaluator merely cannot read is not a mistake, so nothing is
// said about it: what it gets is what it always got.
#[test]
fn something_the_evaluator_cannot_read_is_not_reported() {
    // A divide by something that is not nought folds, and one by a name the
    // evaluator cannot follow says nothing rather than guessing at it.
    clean(&using("7 / 1"));
}

// ---- What a global starts as -------------------------------------------------

// The initialiser is worked out and put on the item, which is where the back
// end reads it to make a segment. It was `None` for every global until now.
#[test]
fn a_global_carries_the_value_it_starts_as() {
    let ttir = clean("var counter: i64 = 6 * 7\nfn main(): i64 { counter }\n");
    let init = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Global { init, .. } => Some(*init),
        _ => None,
    }).expect("a global");
    let at = init.expect("a global with an initialiser knows what it starts as");
    assert!(
        matches!(&ttir.exprs[at].kind, TTIRExprKind::Literal(TIRLit::Int(42))),
        "{:#?}",
        ttir.exprs[at]
    );
}

// And one written without an initialiser has nothing to say, which the back end
// reads as nought rather than as a reason to leave it out.
#[test]
fn a_global_with_no_initialiser_says_nothing() {
    let ttir = clean("var counter: i64\nfn main(): i64 { counter }\n");
    let init = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Global { init, .. } => Some(*init),
        _ => None,
    }).expect("a global");
    assert!(init.is_none(), "{:?}", init);
}

// ---- And what does not fit ---------------------------------------------------

// A value is held to the type it took on, which §8 asked for of a const --
// "nothing checks a constant for range, so a value too big for the type it was
// declared as is neither folded away nor complained about".
//
// Of every literal and not of a const only, which is the objection `consts.rs`
// itself raised against doing it there: "asking it here alone would be
// answering it in one place out of two". Both places, and a global is a third.
#[test]
fn a_value_is_held_to_the_type_it_took_on() {
    // A const, at its declaration.
    let out = refused("const N: u8 = 300\nfn main(): i64 { 0 }\n");
    assert!(out.contains("300 does not fit in `u8`"), "{}", out);
    // Worked out and then held, so what is asked about is the value and not
    // how it was written.
    let out = refused("const N: u8 = 0 - 1\nfn main(): i64 { 0 }\n");
    assert!(out.contains("-1 does not fit in `u8`"), "{}", out);
    // A plain literal in a body.
    let out = refused("fn main(): i64 {\n    let x: u8 = 300\n    0\n}\n");
    assert!(out.contains("300 does not fit in `u8`"), "{}", out);
    // And a global, whose image used to keep the low byte and say nothing.
    let out = refused("var g: u8 = 300\nfn main(): i64 { 0 }\n");
    assert!(out.contains("300 does not fit in `u8`"), "{}", out);
}

// Each width holds what it holds, and a signed one holds negatives where an
// unsigned one holds none.
#[test]
fn each_width_holds_what_it_holds() {
    clean("const A: u8 = 255\nconst B: i8 = 127\nconst C: i8 = -128\n\
           const D: i16 = 32767\nconst E: u32 = 4294967295\n\
           fn main(): i64 { 0 }\n");
    for (source, said) in [
        ("const N: u8 = 256\n", "256 does not fit in `u8`"),
        ("const N: i8 = 128\n", "128 does not fit in `i8`"),
        ("const N: i8 = -129\n", "-129 does not fit in `i8`"),
        ("const N: u16 = -1\n", "-1 does not fit in `u16`"),
    ] {
        let out = refused(&format!("{}fn main(): i64 {{ 0 }}\n", source));
        assert!(out.contains(said), "{}\n{}", source, out);
    }
}

// ---- And what a global's initialiser is held to ------------------------------

// It is walked like any other expression, which it was not: only the folding
// evaluator ever looked at it, so nothing about a global's initialiser was
// checked at all.
#[test]
fn a_globals_initialiser_is_type_checked() {
    let out = refused("var q: i64 = \"not a number\"\nfn main(): i64 { 0 }\n");
    assert!(out.contains("`str`"), "{}", out);
    // Into the initialiser and not only at the top of it: a field that is the
    // wrong type, and a field that is not there.
    let with = "struct Point {\n    pub x: i64,\n    pub y: i64,\n}\n";
    let out = refused(&format!(
        "{}var p: Point = Point {{ x: \"no\", y: 4 }}\nfn main(): i64 {{ 0 }}\n", with));
    assert!(out.contains("`x` is `str` and the field is `i64`"), "{}", out);
    let out = refused(&format!(
        "{}var p: Point = Point {{ x: 1, y: 2, z: 3 }}\nfn main(): i64 {{ 0 }}\n", with));
    assert!(out.contains("has no field `z`"), "{}", out);
}

// And what it comes to is kept, so the back end has something to make a segment
// out of. A folded literal still wins where the evaluator folded one: the image
// can hold a 42 and cannot hold an arithmetic tree.
#[test]
fn an_aggregate_initialiser_is_kept_and_a_folded_one_still_wins() {
    let ttir = clean(
        "struct Point {\n    pub x: i64,\n    pub y: i64,\n}\n\
         var p: Point = Point { x: 3, y: 4 }\n\
         fn main(): i64 { 0 }\n",
    );
    let init = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Global { init, .. } => Some(*init),
        _ => None,
    }).expect("a global").expect("an initialiser");
    assert!(
        matches!(&ttir.exprs[init].kind, TTIRExprKind::StructLit { .. }),
        "{:#?}",
        ttir.exprs[init]
    );
}

// ---- What a variant is numbered ----------------------------------------------

// "A variant with no payload may fix its discriminant instead, which is what
// makes an enum of plain constants" (§2). It could not: what a written `D = 4`
// came to wanted a const evaluator and there was none, so every variant was
// counted and the written number was refused out loud. There is one now, and it
// is the same one a `const` is folded by -- so a discriminant is arithmetic, a
// shift, a cast, or a const already declared above it, exactly as a `const` is.
fn numbered(source: &str) -> Vec<i64> {
    let ttir = clean(source);
    ttir.items
        .iter()
        .find_map(|i| match &i.kind {
            TTIRItemKind::Enum { variants, .. } => {
                Some(variants.iter().map(|v| v.value).collect())
            }
            _ => None,
        })
        .expect("an enum")
}

fn holding(body: &str) -> String {
    format!("enum E {{\n{}\n}}\nfn main(): i64 {{ 0 }}\n", body)
}

#[test]
fn a_written_discriminant_is_worked_out() {
    assert_eq!(numbered(&holding("    A = 4,\n    B = 7,")), vec![4, 7]);
    // The same arithmetic a `const` folds, and nothing narrower.
    assert_eq!(numbered(&holding("    A = 1 << 5,\n    B = 6 * 7,")), vec![32, 42]);
    assert_eq!(numbered(&holding("    A = 'a' as i64,")), vec![97]);
    // A const declared above it, which is the only direction anything the
    // evaluator reads goes.
    assert_eq!(
        numbered("const N: i64 = 9\nenum E {\n    A = N + 1,\n}\nfn main(): i64 { 0 }\n"),
        vec![10]
    );
}

// Counting carries on from whatever was last written, which is the only rule
// that makes `A = 4, B, C` mean what it looks like.
#[test]
fn counting_carries_on_from_the_last_one_written() {
    assert_eq!(numbered(&holding("    A,\n    B,\n    C,")), vec![0, 1, 2]);
    assert_eq!(numbered(&holding("    A = 4,\n    B,\n    C,")), vec![4, 5, 6]);
    assert_eq!(numbered(&holding("    A,\n    B = 10,\n    C,")), vec![0, 10, 11]);
    // And a negative one counts up from where it was put.
    assert_eq!(numbered(&holding("    A = 0 - 3,\n    B,")), vec![-3, -2]);
}

// Two variants of one number are two names for one value, and the tag is what a
// `match` reads -- so nothing could tell them apart and nothing would have said
// so.
#[test]
fn two_variants_of_one_number_are_refused() {
    let out = refused(&holding("    A = 1,\n    B = 1,"));
    assert!(out.contains("`A` and `B` are both 1"), "{}", out);
    // Including where one of them was counted into the other.
    let out = refused(&holding("    A,\n    B = 0,"));
    assert!(out.contains("are both 0"), "{}", out);
}

// And one the evaluator cannot make a whole number of, which is the same thing
// to say however it failed: a tag is an integer and this is not one yet.
#[test]
fn a_discriminant_that_is_not_a_whole_number_is_refused() {
    let out = refused(&holding("    A = \"x\","));
    assert!(out.contains("`A` is not given a whole number"), "{}", out);
    let out = refused(&holding("    A = 1.5,"));
    assert!(out.contains("not given a whole number"), "{}", out);
    // A const declared below it does not fold, so it is not one either.
    let out = refused("enum E {\n    A = LATER,\n}\nconst LATER: i64 = 2\n\
                       fn main(): i64 { 0 }\n");
    assert!(out.contains("not given a whole number"), "{}", out);
}

// ---- What a `%repr` is held to ---------------------------------------------------

// A width fixes the tag, so a number that does not fit in it is refused --
// keeping the low bytes of one quietly would be a variant that reads back as
// another.
#[test]
fn a_number_is_held_to_the_width_a_repr_fixed() {
    let out = refused("%repr(1)\nenum E {\n    A = 0,\n    B = 200,\n}\n\
                       fn main(): i64 { 0 }\n");
    assert!(out.contains("200 does not fit in a tag of 1 bytes"), "{}", out);
    // Signed, the tag being a signed integer whatever the numbers are.
    clean("%repr(1)\nenum E {\n    A = 0,\n    B = 100,\n}\nfn main(): i64 { 0 }\n");
    // `C` is a C `int`, which is four bytes on every machine here.
    let out = refused("%repr(C)\nenum E {\n    A = 0,\n    B = 3000000000,\n}\n\
                       fn main(): i64 { 0 }\n");
    assert!(out.contains("does not fit in a tag of 4 bytes"), "{}", out);
    // And eight bytes is every number there is.
    clean("%repr(8)\nenum E {\n    A = 0,\n    B = 3000000000,\n}\nfn main(): i64 { 0 }\n");
}

// `%repr(C)` says a value is laid out the way the platform's C lays one out,
// and C has no name for an enum that carries something.
#[test]
fn a_c_layout_is_refused_on_an_enum_that_carries() {
    let out = refused("%repr(C)\nenum E {\n    A,\n    B(i32),\n}\nfn main(): i64 { 0 }\n");
    assert!(out.contains("carries nothing"), "{}", out);
    assert!(out.contains("`%repr(4)`"), "{}", out);
    // Which is what to write instead, and it is a promise about this compiler
    // rather than one about C.
    clean("%repr(4)\nenum E {\n    A,\n    B(i32),\n}\nfn main(): i64 { 0 }\n");
}
