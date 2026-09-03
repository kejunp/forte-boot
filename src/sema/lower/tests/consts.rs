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
// inventing the answer. Nothing here reports it -- there is no pass that checks
// a constant for range or for zero -- so what it must do is leave it alone
// rather than pick a value.
#[test]
fn a_division_by_zero_is_not_folded_to_anything() {
    let ttir = clean(&using("7 / 0"));
    let folded = ttir.exprs.iter().any(|e| matches!(
        &e.kind,
        TTIRExprKind::Literal(TIRLit::Int(n)) if *n != 7 && *n != 0
    ));
    assert!(!folded, "a value was invented for 7 / 0:\n{:#?}", ttir.exprs);
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
