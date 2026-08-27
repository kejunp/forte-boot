// Working out here what the program would have worked out there.
//
// The rewrite is the oldest one there is and the licence for it is new: this
// is the first pass in the compiler where the types are settled, so `1 + 2`
// has a type and folding it cannot give the answer a different one. `gir::opt`
// folds too and is held to what needs no types at all, and the difference
// between the two files is almost entirely that one of them can check the
// answer fits and the other cannot.
//
// Three kinds of thing fold. An operator over operands that are already
// literals. An operator over one literal where the other side cannot matter --
// `n + 0` is `n` for every `n` there is. And a field read out of something
// built a few instructions above, which is not arithmetic at all but is the
// same idea: the answer is already written down further up.

use std::collections::HashMap;

use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRLit, TIRPrim,
                            TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRProgram, TyId};

use super::facts::*;
use super::Stats;

// What an operator came to. Either a literal, which the instruction becomes,
// or a value that was already there, which the instruction is replaced by.
enum Folded {
    Lit(TIRLit),
    Same(SIRValueId),
}

// Every operator whose operands are already worked out.
//
// The type is the difference between this and the same rewrite in `gir::opt`.
// There, `let x = 5` written into its uses would have given each use its own
// type where the binding gave them one between them, so folding stopped at
// what needed no types. Here `body.values[def].ty` is the answer the checker
// settled, and the fold is checked against it: a sum that does not fit the
// type it was going to be held in is not folded, because the literal that came
// out would be a different program.
pub(super) fn fold(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut held = made(body);
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut changed = false;

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let mut gone = vec![false; body.blocks[at].insts.len()];
        for index in 0..body.blocks[at].insts.len() {
            let Some(def) = body.blocks[at].insts[index].def else { continue };
            let want = prim(ttir, body.values[def].ty);
            // Operands first: an operand this pass has already replaced is
            // read under the name it had, and what it holds is under the name
            // it came to.
            let folded = {
                let mut kind = body.blocks[at].insts[index].kind.clone();
                for value in SIRBody::uses_mut(&mut kind) {
                    *value = settle(&subst, *value);
                }
                match kind {
                    SIRInstKind::Unary { op, operand } => unary(&held, op, operand, want),
                    SIRInstKind::Binary { op, lhs, rhs } => binary(&held, op, lhs, rhs, want),
                    SIRInstKind::Cast(of) => cast(&held, of, want),
                    other => built(&held, ttir, &other, body.values[def].ty),
                }
            };
            match folded {
                None => {}
                Some(Folded::Lit(value)) => {
                    held[def] = Some(SIRInstKind::Literal(value.clone()));
                    body.blocks[at].insts[index].kind = SIRInstKind::Literal(value);
                    stats.folded += 1;
                    changed = true;
                }
                Some(Folded::Same(value)) => {
                    let value = settle(&subst, value);
                    // Whatever the operand was made by is what this is made by
                    // now, so a chain of identities settles in one walk.
                    held[def] = held.get(value).cloned().flatten();
                    subst.insert(def, value);
                    gone[index] = true;
                    stats.folded += 1;
                    changed = true;
                }
            }
        }
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[index - 1]
        });
    }
    replace(body, &subst);
    changed
}

fn unary(
    made: &[Option<SIRInstKind>],
    op: TIRUnaryOp,
    operand: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    let value = lit_of(made, operand)?;
    let folded = match (op, value) {
        (TIRUnaryOp::Not, TIRLit::Bool(b)) => TIRLit::Bool(!b),
        (TIRUnaryOp::Not, TIRLit::Int(n)) => TIRLit::Int(fits(want?, !(*n as i128))?),
        (TIRUnaryOp::Neg, TIRLit::Int(n)) => TIRLit::Int(fits(want?, -(*n as i128))?),
        (TIRUnaryOp::Neg, TIRLit::Float(x)) => real(want?, -*x)?,
        // Taking a reference to a literal is not the literal.
        _ => return None,
    };
    Some(Folded::Lit(folded))
}

fn binary(
    made: &[Option<SIRInstKind>],
    op: TIRBinOp,
    lhs: SIRValueId,
    rhs: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    match (lit_of(made, lhs), lit_of(made, rhs)) {
        (Some(a), Some(b)) => both(op, a, b, want).map(Folded::Lit),
        _ => idem(made, op, lhs, rhs, want),
    }
}

fn both(op: TIRBinOp, a: &TIRLit, b: &TIRLit, want: Option<TIRPrim>) -> Option<TIRLit> {
    match (a, b) {
        (TIRLit::Int(x), TIRLit::Int(y)) => int(op, *x, *y, want),
        (TIRLit::Float(x), TIRLit::Float(y)) => real_op(op, *x, *y, want),
        (TIRLit::Bool(x), TIRLit::Bool(y)) => match op {
            TIRBinOp::And | TIRBinOp::BitAnd => Some(TIRLit::Bool(*x && *y)),
            TIRBinOp::Or | TIRBinOp::BitOr => Some(TIRLit::Bool(*x || *y)),
            TIRBinOp::Xor | TIRBinOp::BitXor => Some(TIRLit::Bool(x != y)),
            _ => compare(op, x, y),
        },
        (TIRLit::Char(x), TIRLit::Char(y)) => compare(op, x, y),
        (TIRLit::Str(x), TIRLit::Str(y)) => compare(op, x, y),
        (TIRLit::Null, TIRLit::Null) => compare(op, &(), &()),
        _ => None,
    }
}

// Integers fold in i128 and are then held to the type the checker gave the
// result. i128 is wide enough that nothing an i64 pair can do to it overflows,
// so the only question left is the one `fits` asks.
fn int(op: TIRBinOp, x: i64, y: i64, want: Option<TIRPrim>) -> Option<TIRLit> {
    let (x, y) = (x as i128, y as i128);
    let worked = match op {
        TIRBinOp::Add => x + y,
        TIRBinOp::Sub => x - y,
        TIRBinOp::Mul => x * y,
        // Dividing by zero is the program's mistake to make, not this pass's
        // to commit on its behalf.
        TIRBinOp::Div => x.checked_div(y)?,
        TIRBinOp::Rem => x.checked_rem(y)?,
        // A shift as wide as the value is a shift this pass has no answer for:
        // what an i64 does at 64 is not what the narrower type would do, and
        // the type is not always one of them.
        TIRBinOp::Shl => x.checked_shl(width(y)?)?,
        TIRBinOp::Shr => x.checked_shr(width(y)?)?,
        TIRBinOp::BitAnd => x & y,
        TIRBinOp::BitOr => x | y,
        TIRBinOp::BitXor => x ^ y,
        _ => return compare(op, &x, &y),
    };
    Some(TIRLit::Int(fits(want?, worked)?))
}

fn width(y: i128) -> Option<u32> {
    let shift = u32::try_from(y).ok()?;
    (shift < 64).then_some(shift)
}

// Whether the answer can be held in the type it is going to be held in, and
// the answer itself if it can. A `TIRLit::Int` is an i64 whatever the type is,
// so that is a second ceiling and not only the type's.
pub(super) fn fits(p: TIRPrim, n: i128) -> Option<i64> {
    use TIRPrim::*;
    let ok = match p {
        I8 => (i8::MIN as i128..=i8::MAX as i128).contains(&n),
        I16 => (i16::MIN as i128..=i16::MAX as i128).contains(&n),
        I32 => (i32::MIN as i128..=i32::MAX as i128).contains(&n),
        I64 | I128 => (i64::MIN as i128..=i64::MAX as i128).contains(&n),
        U8 => (0..=u8::MAX as i128).contains(&n),
        U16 => (0..=u16::MAX as i128).contains(&n),
        U32 => (0..=u32::MAX as i128).contains(&n),
        // A literal is an i64, so what a u64 can hold past that is not
        // something a folded one could be written as anyway.
        U64 | U128 => (0..=i64::MAX as i128).contains(&n),
        _ => false,
    };
    ok.then(|| n as i64)
}

// Floats fold now that which one they are is settled -- `gir::opt` would not,
// and said why: f32 and f64 round differently and the choice had not been
// made. It is made here, so an f32 folds in f32.
//
// Only where the answer stays finite. An overflow to an infinity or a zero
// divided by a zero is a fold that has left the range the operands were in,
// and a literal infinity is not what the source wrote.
fn real_op(op: TIRBinOp, x: f64, y: f64, want: Option<TIRPrim>) -> Option<TIRLit> {
    if let Some(held) = compare(op, &x, &y) {
        return Some(held);
    }
    let p = want?;
    if p == TIRPrim::F32 {
        let (x, y) = (x as f32, y as f32);
        let worked = match op {
            TIRBinOp::Add => x + y,
            TIRBinOp::Sub => x - y,
            TIRBinOp::Mul => x * y,
            TIRBinOp::Div => x / y,
            TIRBinOp::Rem => x % y,
            _ => return None,
        };
        return worked.is_finite().then(|| TIRLit::Float(worked as f64));
    }
    let worked = match op {
        TIRBinOp::Add => x + y,
        TIRBinOp::Sub => x - y,
        TIRBinOp::Mul => x * y,
        TIRBinOp::Div => x / y,
        TIRBinOp::Rem => x % y,
        _ => return None,
    };
    (p == TIRPrim::F64 && worked.is_finite()).then(|| TIRLit::Float(worked))
}

fn real(p: TIRPrim, x: f64) -> Option<TIRLit> {
    match p {
        TIRPrim::F32 => (x as f32).is_finite().then(|| TIRLit::Float(x as f32 as f64)),
        TIRPrim::F64 => x.is_finite().then_some(TIRLit::Float(x)),
        _ => None,
    }
}

fn compare<T: PartialOrd + PartialEq>(op: TIRBinOp, x: &T, y: &T) -> Option<TIRLit> {
    Some(TIRLit::Bool(match op {
        TIRBinOp::Eq => x == y,
        TIRBinOp::Ne => x != y,
        TIRBinOp::Lt => x < y,
        TIRBinOp::Gt => x > y,
        TIRBinOp::Le => x <= y,
        TIRBinOp::Ge => x >= y,
        _ => return None,
    }))
}

// A cast of a literal to a type that can hold it is that literal. Only between
// integers: what `as` does to a float that will not fit, or to a char, is not
// written down anywhere yet, and a fold is not the place to decide it.
fn cast(made: &[Option<SIRInstKind>], of: SIRValueId, want: Option<TIRPrim>) -> Option<Folded> {
    let p = want?;
    if !integer(p) {
        return None;
    }
    let TIRLit::Int(n) = lit_of(made, of)? else { return None };
    Some(Folded::Lit(TIRLit::Int(fits(p, *n as i128)?)))
}

// Reading out of something this body has just built. `Point { x: 1, y: 2 }.x`
// is `1` twice over -- once because the field is there in the literal, and
// once because reading it made a copy of what was put there -- and after a
// call has been written out that is most of what an argument passed as a
// struct turns into.
//
// The type is what says whether the copy may go. A field that is something to
// release is a field whose copy is a second thing to release, and naming the
// one that was put in would leave two releases of it; `shareable` is the same
// rule `share` is held to, and for the same reason.
//
// The discriminant is the one of these that answers with a literal rather than
// with a value that was already there: what a variant's tag *is* is written in
// the declaration, which is where `sir::lower` reads it from as well.
fn built(
    made: &[Option<SIRInstKind>],
    ttir: &TTIRProgram,
    kind: &SIRInstKind,
    ty: TyId,
) -> Option<Folded> {
    match kind {
        SIRInstKind::Discriminant(of) => {
            let Some(SIRInstKind::VariantLit { item, variant, .. }) = made.get(*of)? else {
                return None;
            };
            let TTIRItemKind::Enum { variants, .. } = &ttir.items.get(*item)?.kind else {
                return None;
            };
            let tag = variants.get(*variant).map(|v| v.value).unwrap_or(*variant as i64);
            Some(Folded::Lit(TIRLit::Int(tag)))
        }
        _ if !shareable(ttir, ty) => None,
        SIRInstKind::Field { base, index } => {
            let Some(SIRInstKind::StructLit { fields, .. }) = made.get(*base)? else {
                return None;
            };
            fields.get(*index).map(|held| Folded::Same(*held))
        }
        SIRInstKind::TupleIndex { base, index } => {
            let Some(SIRInstKind::TupleLit(fields)) = made.get(*base)? else { return None };
            fields.get(*index as usize).map(|held| Folded::Same(*held))
        }
        SIRInstKind::Payload { of, variant, index } => {
            let Some(SIRInstKind::VariantLit { variant: made_as, fields, .. }) = made.get(*of)?
            else {
                return None;
            };
            // Reading the payload of a variant the value is not is reading
            // what is not there. `sir::lower` only ever puts one under a test
            // that has already settled which variant it is, so this is a
            // shape that should not arise -- and answering it wrongly would be
            // worse than leaving it alone.
            (made_as == variant).then(|| fields.get(*index).map(|held| Folded::Same(*held)))?
        }
        _ => None,
    }
}

// The identities that need one side to be a literal and say nothing about the
// other. Integers only: `x + 0.0` is `x` for every float but one, and the one
// is a negative zero.
//
// `x * 0` is the odd one out -- it answers without the other side at all --
// and it is still sound, because the instruction that worked the other side
// out is left standing. If nothing else reads it, `sweep` is what decides
// whether it may go, and `sweep` knows about traps.
fn idem(
    made: &[Option<SIRInstKind>],
    op: TIRBinOp,
    lhs: SIRValueId,
    rhs: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    let p = want?;
    if !integer(p) {
        return None;
    }
    let whole = |value| match lit_of(made, value) {
        Some(TIRLit::Int(n)) => Some(*n),
        _ => None,
    };
    let (a, b) = (whole(lhs), whole(rhs));
    let folded = match (op, a, b) {
        (TIRBinOp::Add, Some(0), _) | (TIRBinOp::Mul, Some(1), _) => Folded::Same(rhs),
        (TIRBinOp::BitOr, Some(0), _) | (TIRBinOp::BitXor, Some(0), _) => Folded::Same(rhs),
        (TIRBinOp::Add, _, Some(0))
        | (TIRBinOp::Sub, _, Some(0))
        | (TIRBinOp::Mul, _, Some(1))
        | (TIRBinOp::Div, _, Some(1))
        | (TIRBinOp::Shl, _, Some(0))
        | (TIRBinOp::Shr, _, Some(0))
        | (TIRBinOp::BitOr, _, Some(0))
        | (TIRBinOp::BitXor, _, Some(0)) => Folded::Same(lhs),
        (TIRBinOp::Mul, Some(0), _) | (TIRBinOp::Mul, _, Some(0)) => {
            Folded::Lit(TIRLit::Int(0))
        }
        (TIRBinOp::BitAnd, Some(0), _) | (TIRBinOp::BitAnd, _, Some(0)) => {
            Folded::Lit(TIRLit::Int(0))
        }
        _ => return None,
    };
    Some(folded)
}
