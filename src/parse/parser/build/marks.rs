//! The word a `Mark` carried, read back as the operator it stands for.
//!
//! BNF spells `<additive_op> -> +` as a rule of its own, so the word reaches
//! the rule that wants it as a node rather than as an operator. These take it
//! back out.

use super::*;

/// The operator an `ASTMark` carried, and the same for the rest of the words.
/// Each panics where the mark is not the one the rule above it asked for: the
/// grammar settles which mark reaches which rule, so anything else is these
/// arms disagreeing with the tables, not a source being wrong.
pub(super) fn bin_of(mark: ASTMark) -> ASTBinOp {
    match mark {
        ASTMark::Bin(op) => op,
        other => panic!("a binary rule was given {:?}", other),
    }
}

pub(super) fn assign_of(mark: ASTMark) -> ASTAssignOp {
    match mark {
        ASTMark::Assign(op) => op,
        other => panic!("an assignment was given {:?}", other),
    }
}

pub(super) fn unary_of(mark: ASTMark) -> ASTUnaryOp {
    match mark {
        ASTMark::Unary(op) => op,
        other => panic!("a unary rule was given {:?}", other),
    }
}

pub(super) fn range_of(mark: ASTMark) -> ASTRangeOp {
    match mark {
        ASTMark::Range(op) => op,
        other => panic!("a range was given {:?}", other),
    }
}

pub(super) fn ref_of(mark: ASTMark) -> ASTRefOp {
    match mark {
        ASTMark::Ref(op) => op,
        other => panic!("a reference was given {:?}", other),
    }
}

pub(super) fn intro_of(mark: ASTMark) -> ASTVariableIntro {
    match mark {
        ASTMark::Intro(intro) => intro,
        other => panic!("a variable was introduced by {:?}", other),
    }
}

