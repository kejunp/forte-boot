// What each machine says it can do.
//
// These are not tests of a rewrite: nothing here compiles anything. They are
// tests of the description, which is worth having written down because every
// number in it is a claim about hardware that somebody will one day want to
// check or change.

use crate::sir::sir_nodes::SIRInstKind;
use crate::sir::target::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRPrim, TIRUnaryOp};

fn binary(op: TIRBinOp) -> SIRInstKind {
    SIRInstKind::Binary { op, lhs: 0, rhs: 0 }
}

// How many fit is the register divided by the thing, so a wider machine holds
// more of the same and one machine holds more of a narrower thing.
#[test]
fn how_many_fit_is_the_register_over_the_thing() {
    assert_eq!(X86_64.lanes(4), 4, "four i32s in sixteen bytes");
    assert_eq!(X86_64.lanes(8), 2, "and two i64s");
    assert_eq!(X86_64.lanes(1), 16, "and sixteen bytes' worth of bytes");
    assert_eq!(X86_64_V3.lanes(4), 8, "twice as wide holds twice as many");
    assert_eq!(X86_64_V4.lanes(4), 16);
    // A thing as wide as the register is one thing, and a machine with no
    // vectors holds one of everything.
    assert_eq!(X86_64.lanes(16), 1);
    assert_eq!(X86_64.lanes(32), 1);
    assert_eq!(NONE.lanes(4), 1);
}

// A machine with no vectors can do nothing to several at once, which is what
// makes "do not widen anything" a target rather than a flag.
#[test]
fn a_machine_with_no_vectors_does_nothing_at_once() {
    assert!(!NONE.does(&binary(TIRBinOp::Add), TIRPrim::I32, 4));
    assert!(!NONE.does(&binary(TIRBinOp::Add), TIRPrim::F64, 2));
}

// One lane is not several, whatever the machine.
#[test]
fn one_lane_is_not_a_group() {
    assert!(!X86_64.does(&binary(TIRBinOp::Add), TIRPrim::I32, 1));
    assert!(X86_64.does(&binary(TIRBinOp::Add), TIRPrim::I32, 4));
}

// The arithmetic that exists, and the arithmetic that does not. An integer
// divide is the one everybody expects and nobody has.
#[test]
fn there_is_no_integer_divide_on_any_of_them() {
    for held in [X86_64, AARCH64, X86_64_V3, X86_64_V4] {
        assert!(
            !held.does(&binary(TIRBinOp::Div), TIRPrim::I32, 4),
            "{} claims an integer divide",
            held.name
        );
        assert!(
            !held.does(&binary(TIRBinOp::Rem), TIRPrim::I32, 4),
            "{} claims an integer remainder",
            held.name
        );
        // Floats have one everywhere.
        assert!(held.does(&binary(TIRBinOp::Div), TIRPrim::F32, 4), "{}", held.name);
    }
}

// The wide multiply arrived late, so the baseline does the narrow ones and not
// the eight-byte one.
#[test]
fn the_wide_multiply_is_not_on_the_older_machines() {
    assert!(X86_64.does(&binary(TIRBinOp::Mul), TIRPrim::I32, 4));
    assert!(!X86_64.does(&binary(TIRBinOp::Mul), TIRPrim::I64, 2));
    assert!(X86_64_V4.does(&binary(TIRBinOp::Mul), TIRPrim::I64, 8));
}

// And shifts that differ by lane are newer than shifts.
#[test]
fn shifts_that_differ_by_lane_are_not_on_the_oldest() {
    assert!(!X86_64.does(&binary(TIRBinOp::Shl), TIRPrim::I32, 4));
    assert!(X86_64_V3.does(&binary(TIRBinOp::Shl), TIRPrim::I32, 8));
    assert!(AARCH64.does(&binary(TIRBinOp::Shl), TIRPrim::I32, 4));
}

// Nothing that is a shape rather than an operation is one instruction over
// several values, whatever the machine.
#[test]
fn a_shape_is_not_an_operation() {
    let field = SIRInstKind::Field { base: 0, index: 0 };
    let call = SIRInstKind::Call { callee: 0, args: Vec::new() };
    for held in [X86_64, X86_64_V4, AARCH64] {
        assert!(!held.does(&field, TIRPrim::I32, 4), "{}", held.name);
        assert!(!held.does(&call, TIRPrim::I32, 4), "{}", held.name);
    }
    // Taking a reference is an address, and there is no address of four
    // things at once.
    let addr = SIRInstKind::Unary { op: TIRUnaryOp::Addr, operand: 0 };
    assert!(!X86_64.does(&addr, TIRPrim::I32, 4));
    let not = SIRInstKind::Unary { op: TIRUnaryOp::Not, operand: 0 };
    assert!(X86_64.does(&not, TIRPrim::I32, 4));
}

// A primitive's width is the language's, and everything else has none here.
#[test]
fn a_primitive_is_as_wide_as_its_name_says() {
    assert_eq!(size_of(TIRPrim::I8), Some(1));
    assert_eq!(size_of(TIRPrim::I32), Some(4));
    assert_eq!(size_of(TIRPrim::F64), Some(8));
    assert_eq!(size_of(TIRPrim::I128), Some(16));
    assert_eq!(size_of(TIRPrim::Bool), Some(1));
    assert_eq!(size_of(TIRPrim::Char), Some(4), "one Unicode scalar value");
    // What a `str` takes is a layout question nothing has answered.
    assert_eq!(size_of(TIRPrim::Str), None);
    assert_eq!(size_of(TIRPrim::Null), None);
}

// Every name the flag takes is a machine, and the list a message would print
// is the same list.
#[test]
fn every_name_that_is_offered_is_one_that_answers() {
    for name in NAMES {
        assert!(of(name).is_some(), "{} is offered and not answered", name);
    }
    assert_eq!(of("none"), Some(NONE));
    assert_eq!(of("x86-64-v3"), Some(X86_64_V3));
    assert_eq!(of("host"), Some(host()));
    assert_eq!(of("nothing-like-that"), None);
}
