// Making the SIR smaller: the same program, with what it does not have to do
// taken out of it.
//
//     TTIR -> lower -> GIR -> opt -> lower -> SIR -> promote -> opt
//
// `gir::opt` runs before the checker and is held to what a declaration can
// answer on its own: no copy propagation, no inlining, and no folding that
// would change which programs compile. This pass is on the other side of all
// three. The types are settled, so `1 + 2` has a type and folding it cannot
// give the answer a different one. Every value is made once, so what a name
// holds is a lookup rather than a walk. And nothing after this refuses a
// program -- there is no diagnostic left to get wrong -- so a rewrite here is
// only ever wrong about what the program *does*.
//
// Six rewrites, run round and round until none of them has anything left:
//
//   `fold`      an operator over values that are already literals, the handful
//               of identities that need only one side to be one, and a field
//               read out of something built a few instructions above.
//   `phis`      a phi whose edges all name one value, which is a join that
//               joined nothing.
//   `share`     two instructions that make the same value from the same
//               operands, where the first stands before the second.
//   `branches`  a branch whose condition is already known, and one whose two
//               edges go to one block.
//   `merge`     a block whose only way in is a `Goto`, folded into the block
//               that goes there.
//   `sweep`     everything nothing reads and nothing else needs run.
//
// And one that is the program's rather than a body's:
//
//   `inline`    a call to a declaration written out where it was called, with
//               the arguments standing in for the parameters.
//
// Inlining is what makes the rest of them worth running: a call carries its
// arguments into a body that cannot see where they came from, and writing the
// body out is what puts a literal argument next to the operator that would
// fold it.
//
// It is also the one rewrite that can make a program bigger, so it is bounded
// twice over: by how big a callee may be, and by how many calls one body may
// take in a round. And it is refused outright wherever the callee can reach
// itself, which stops a recursive fn being written into itself forever and
// equally into anybody else, where it would be a loop unrolled by accident
// rather than a call written out.
//
// The source has the last word both ways. `%noinline` "is a promise about what
// a stack trace will show" (§1), so it is obeyed and nothing here weighs it
// against anything; `%inline` is "a hint, and the one thing here a backend may
// ignore", so it waives the size bound and none of the rules that make the
// rewrite sound.
//
// The order the six are written in is the order they are run in, and it is not
// arbitrary: folding makes conditions literal, which makes branches into
// gotos, which leaves blocks with one way in for `merge`, which puts an
// instruction next to the one it duplicates for `share`. Nothing depends on
// that order being right, though -- the loop runs until nothing changes, so a
// rewrite that only becomes possible after another one just happens a round
// later.
//
// What is *not* here is vectorization. It is asked for in the same breath as
// the rest and it does not belong in the same pass, or yet in this compiler:
// it needs a target to say how wide a vector is, a type for one to be held in
// -- the SIR has neither -- and, before either, an answer to whether two turns
// of a loop touch the same memory, which is the alias analysis nothing here
// has. Writing something that reshaped loops without those would be a rewrite
// that is right by luck. See the note at the foot of this file for what would
// have to come first.

use std::collections::HashMap;

use crate::tir::tir_nodes::{TIRBinOp, TIRFnUses, TIRInline, TIRLit, TIRPrim, TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRItemId, TTIRItemKind, TTIRProgram, Ty, TyId};

use super::dom::Dominators;
use super::promote::promote;
use super::sir_nodes::*;

// Rounds before the loop gives up. A body settles in two or three; the cap is
// for a rewrite that undoes another, which would be a bug here rather than
// anything a program can do.
const MAX_ROUNDS: usize = 8;
// How many instructions a callee may hold and still be written out. A call is
// a handful of instructions itself, so this is roughly "a body worth less than
// the call to it, or not much more".
const INLINE_MAX: usize = 32;
// And how many calls one body may take in one round. The rounds compose --
// what was written into a callee last round is written into its caller this
// round -- so this bounds the growth per round and not the depth.
const INLINE_EACH: usize = 8;

// What the pass did, for the driver to print. Nothing reads it but the message.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub rounds:   usize,
    pub inlined:  usize,
    pub folded:   usize,
    // Values that turned out to be a value there already: a phi that joined
    // one answer, or an instruction that repeated one.
    pub shared:   usize,
    pub dead:     usize,
    // Blocks emptied, merged away, or left with one edge where they had two.
    pub blocks:   usize,
    // Slots the re-run of `promote` took out, which are the callee's locals
    // now that they are the caller's.
    pub promoted: usize,
}

pub fn optimize(program: &mut SIRProgram, ttir: &TTIRProgram) -> Stats {
    let mut stats = Stats::default();
    let graph = Calls::of(program, ttir);
    for round in 1..=MAX_ROUNDS {
        let mut changed = false;
        // The program first: writing a call out is what gives the body
        // rewrites something new to work on, and the slots it brings with it
        // are the caller's now, so the promotion is asked again.
        if inline(program, &graph, &mut stats) {
            stats.promoted += promote(program);
            changed = true;
        }
        for body in &mut program.bodies {
            changed |= clean(body, ttir, &mut stats);
        }
        stats.rounds = round;
        if !changed {
            break;
        }
    }
    stats
}

// One body, until the six have nothing left. The inner loop is here rather
// than only in `optimize` so that a body settles without waiting on the whole
// program to go round again.
fn clean(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let mut ever = false;
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        changed |= fold(body, ttir, stats);
        changed |= phis(body, stats);
        changed |= share(body, ttir, stats);
        changed |= branches(body, stats);
        changed |= merge(body, stats);
        changed |= sweep(body, stats);
        ever |= changed;
        if !changed {
            break;
        }
    }
    ever
}

// ---- Reading the body -----------------------------------------------------

// What made each value, by the value's id. SSA is what makes this a table
// rather than a walk, and every rewrite below is written against it: "what
// does this operand hold" is `made[operand]`, and there is no second answer.
//
// A phi is not in it. What a phi made depends on the edge, which is the one
// question this table cannot be asked -- `operands` below is what covers both.
fn made(body: &SIRBody) -> Vec<Option<SIRInstKind>> {
    let mut out = vec![None; body.values.len()];
    for block in &body.blocks {
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = Some(inst.kind.clone());
                }
            }
        }
    }
    out
}

// What whatever made each value reads, phis included. `sweep` walks this
// backwards from the values that have to be worked out to the ones that
// therefore do.
fn operands(body: &SIRBody) -> Vec<Vec<SIRValueId>> {
    let mut out = vec![Vec::new(); body.values.len()];
    for block in &body.blocks {
        for phi in &block.phis {
            if phi.def < out.len() {
                out[phi.def] = phi.edges.iter().map(|(_, value)| *value).collect();
            }
        }
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = SIRBody::uses(&inst.kind);
                }
            }
        }
    }
    out
}

fn lit_of(made: &[Option<SIRInstKind>], value: SIRValueId) -> Option<&TIRLit> {
    match made.get(value)? {
        Some(SIRInstKind::Literal(held)) => Some(held),
        _ => None,
    }
}

fn prim(ttir: &TTIRProgram, ty: TyId) -> Option<TIRPrim> {
    match ttir.types.get(ty)? {
        Ty::Prim(p) => Some(*p),
        _ => None,
    }
}

fn integer(p: TIRPrim) -> bool {
    use TIRPrim::*;
    matches!(p, I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128)
}

// Whether the value has to stay even where nothing reads it.
//
// Three kinds of reason. A call or a store or a release is what the program is
// *for*, and dropping one drops what it did. An index may be past the end, and
// whether that is a trap is not settled anywhere yet (docs/prose.txt says
// nothing about it), so taking one out would be this pass answering a question
// that is not its own. And a division whose divisor is not a literal that is
// plainly not zero is the same: the trap, if there is one, is the thing being
// removed.
fn effects(made: &[Option<SIRInstKind>], kind: &SIRInstKind) -> bool {
    match kind {
        SIRInstKind::Call { .. }
        | SIRInstKind::Method { .. }
        | SIRInstKind::Store { .. }
        | SIRInstKind::Drop(_)
        | SIRInstKind::DropSlot(_) => true,
        SIRInstKind::Index { .. } | SIRInstKind::IndexAddr { .. } => true,
        SIRInstKind::Binary { op: TIRBinOp::Div | TIRBinOp::Rem, rhs, .. } => {
            match lit_of(made, *rhs) {
                Some(TIRLit::Int(n)) => *n == 0,
                // A float division by zero is an infinity and not a trap, so
                // there is nothing being kept for.
                Some(TIRLit::Float(_)) => false,
                _ => true,
            }
        }
        _ => false,
    }
}

// Whether two of them with the same operands make the same value.
//
// Not the same question as `effects`. A load has no effects and may still find
// something different the second time, because a store between them is exactly
// the effect the load has not got. A division may trap and is still the same
// answer twice: if the first one trapped there is no second one.
fn known(kind: &SIRInstKind) -> bool {
    matches!(
        kind,
        SIRInstKind::Literal(_)
            | SIRInstKind::Item(_)
            | SIRInstKind::SelfValue
            | SIRInstKind::Unary { .. }
            | SIRInstKind::Binary { .. }
            | SIRInstKind::Cast(_)
            | SIRInstKind::Discriminant(_)
            | SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::FieldAddr { .. }
            | SIRInstKind::TupleAddr { .. }
    )
}

// And whether naming one value twice is naming one *thing* twice. It is not,
// wherever the value is something to release: two instructions that each made
// one become one instruction and two releases of it. So sharing is held to the
// types nobody releases, which is the part of `sema::borrows`' answer a `TyId`
// can give on its own -- see `Copies::drops`, which this agrees with and does
// not call, having neither the table nor the body's generics to hand.
fn shareable(ttir: &TTIRProgram, ty: TyId) -> bool {
    match ttir.types.get(ty) {
        Some(Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Run(_)) => true,
        Some(Ty::Fn { uses, .. }) => *uses != TIRFnUses::Takes,
        _ => false,
    }
}

// ---- Putting one value where another was ----------------------------------

// What a value came to, following the chain as far as it goes: a value
// replaced by one that is itself replaced later in the same round. Bounded by
// the length of the map, which is what makes a cycle stop rather than spin.
fn settle(subst: &HashMap<SIRValueId, SIRValueId>, mut value: SIRValueId) -> SIRValueId {
    for _ in 0..=subst.len() {
        match subst.get(&value) {
            Some(&next) if next != value => value = next,
            _ => return value,
        }
    }
    value
}

// Every operand of the body, rewritten at once. Every rewrite that takes an
// instruction out ends here: what it made is read somewhere, and what it made
// is now something else's.
fn replace(body: &mut SIRBody, subst: &HashMap<SIRValueId, SIRValueId>) {
    if subst.is_empty() {
        return;
    }
    for block in &mut body.blocks {
        for phi in &mut block.phis {
            for (_, value) in &mut phi.edges {
                *value = settle(subst, *value);
            }
        }
        for inst in &mut block.insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(subst, *value);
            }
        }
        match &mut block.term {
            SIRTerm::Branch { cond, .. } => *cond = settle(subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(subst, *value),
            _ => {}
        }
    }
}

// ---- Constant folding -----------------------------------------------------

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
fn fold(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
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
fn fits(p: TIRPrim, n: i128) -> Option<i64> {
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

// ---- Phis that joined one answer ------------------------------------------

// A phi whose edges all name one value is a join where nothing was decided:
// every way in brought the same thing, so the phi *is* that thing. Its own
// name among the edges does not count -- a loop's phi naming itself along the
// back edge still has one answer, which is what came in the first time round.
fn phis(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        body.blocks[at].phis.retain(|phi| {
            let mut one: Option<SIRValueId> = None;
            for (_, value) in &phi.edges {
                if *value == phi.def {
                    continue;
                }
                match one {
                    None => one = Some(*value),
                    Some(held) if held == *value => {}
                    // Two answers, so the phi is what says which.
                    Some(_) => return true,
                }
            }
            match one {
                Some(value) => {
                    subst.insert(phi.def, value);
                    false
                }
                // Every edge named the phi itself, which is a value with no
                // first answer at all. Nothing here can invent one.
                None => true,
            }
        });
    }
    stats.shared += subst.len();
    let changed = !subst.is_empty();
    replace(body, &subst);
    changed
}

// ---- One value for two instructions ---------------------------------------

// Two instructions that read the same values and do the same thing to them
// make the same value, so the second can be the first -- but only where the
// first stands before it on every path, which is dominance and nothing weaker.
// So the walk is down the dominator tree: what a block adds is visible to
// everything below it and taken back off on the way out, which is exactly the
// set of instructions that stand before the block being walked.
fn share(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let doms = Dominators::of(body);
    let children = doms.children();
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    // What is in hand, deepest last, and how much of it each block added. A
    // list and not a map: `SIRInstKind` holds an f64 and so cannot be hashed,
    // and the lists a block's worth of instructions makes are short.
    let mut seen: Vec<(SIRInstKind, TyId, SIRValueId)> = Vec::new();
    let mut added = vec![0usize; body.blocks.len()];

    let mut work = vec![(body.entry, false)];
    while let Some((at, leaving)) = work.pop() {
        if leaving {
            seen.truncate(added[at]);
            continue;
        }
        added[at] = seen.len();
        work.push((at, true));

        for index in 0..body.blocks[at].insts.len() {
            let Some(def) = body.blocks[at].insts[index].def else { continue };
            let mut kind = body.blocks[at].insts[index].kind.clone();
            for value in SIRBody::uses_mut(&mut kind) {
                *value = settle(&subst, *value);
            }
            if !known(&kind) {
                continue;
            }
            let ty = body.values[def].ty;
            // An address is a place and not a thing: two names for one place
            // are one name whatever is kept there, which is why the addresses
            // do not go through `shareable` and everything else does.
            let place = matches!(
                kind,
                SIRInstKind::Addr(_)
                    | SIRInstKind::ItemAddr(_)
                    | SIRInstKind::SelfAddr
                    | SIRInstKind::FieldAddr { .. }
                    | SIRInstKind::TupleAddr { .. }
            );
            if !place && !shareable(ttir, ty) {
                continue;
            }
            match seen.iter().find(|(held, of, _)| *of == ty && *held == kind) {
                Some((_, _, held)) => {
                    subst.insert(def, *held);
                    gone[at][index] = true;
                    stats.shared += 1;
                }
                None => seen.push((kind, ty, def)),
            }
        }

        for &child in &children[at] {
            if live[child] {
                work.push((child, false));
            }
        }
    }

    if subst.is_empty() {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    replace(body, &subst);
    true
}

// ---- Branches with one edge -----------------------------------------------

// A branch on a literal goes one way, and a branch whose two edges go to one
// block was never a branch. Either way the block that stops being reached has
// to be told: a phi has one entry per way in, and a way in that has gone is an
// entry that has to go with it.
fn branches(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let held = made(body);
    let mut changed = false;
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let SIRTerm::Branch { cond, then, els } = body.blocks[at].term else { continue };
        let to = match lit_of(&held, cond) {
            Some(TIRLit::Bool(true)) => then,
            Some(TIRLit::Bool(false)) => els,
            _ if then == els => then,
            _ => continue,
        };
        body.blocks[at].term = SIRTerm::Goto(to);
        stats.blocks += 1;
        changed = true;
    }
    if changed {
        repair(body);
    }
    changed
}

// Phis held to the ways in the block actually has. Only ever fewer: nothing in
// this pass gives a block a way in it had not got, and `merge` renames the one
// edge it moves rather than adding one.
fn repair(body: &mut SIRBody) {
    let live = body.live();
    let preds = body.preds();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let ways: Vec<SIRBlockId> =
            preds[at].iter().copied().filter(|&p| live[p]).collect();
        for phi in &mut body.blocks[at].phis {
            let mut kept: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
            for &(from, value) in phi.edges.iter() {
                if ways.contains(&from) && !kept.iter().any(|(held, _)| *held == from) {
                    kept.push((from, value));
                }
            }
            phi.edges = kept;
        }
    }
}

// ---- Blocks folded into the block above them ------------------------------

// A block with one way in, and that way a `Goto`, is the tail of the block
// that goes there. Joining the two is what leaves an instruction next to the
// one it repeats, which is most of what `share` and `fold` need to see.
//
// Only where the block has no phis. A phi with one way in is a phi with one
// answer, which `phis` takes out a round earlier -- so this waits rather than
// working out what a phi means in a block that no longer begins anywhere.
fn merge(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let mut changed = false;
    loop {
        let live = body.live();
        let preds = body.preds();
        let mut joined = None;
        for at in 0..body.blocks.len() {
            if !live[at] {
                continue;
            }
            let SIRTerm::Goto(to) = body.blocks[at].term else { continue };
            if to == at || to == body.entry || !body.blocks[to].phis.is_empty() {
                continue;
            }
            if preds[to].iter().filter(|&&p| live[p]).count() != 1 {
                continue;
            }
            joined = Some((at, to));
            break;
        }
        let Some((at, to)) = joined else { return changed };

        let mut moved = std::mem::take(&mut body.blocks[to].insts);
        let term = std::mem::replace(&mut body.blocks[to].term, SIRTerm::Unreachable);
        body.blocks[at].insts.append(&mut moved);
        // Whoever heard from the block that has gone hears from this one now.
        for next in term.targets() {
            for phi in &mut body.blocks[next].phis {
                for (from, _) in &mut phi.edges {
                    if *from == to {
                        *from = at;
                    }
                }
            }
        }
        body.blocks[at].term = term;
        stats.blocks += 1;
        changed = true;
    }
}

// ---- What nothing reads ---------------------------------------------------

// A value nothing reads and nothing needs run is a value that was never worth
// working out. Marked and then swept: an instruction is wanted if what it
// makes is wanted, and what it reads is wanted if it is -- so the walk starts
// at the instructions that have to run whatever else happens, and everything
// it does not reach goes.
//
// Blocks nothing reaches go the same way, and first: an instruction standing
// in one is not run either, and leaving it there would keep alive whatever it
// reads.
fn sweep(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut changed = false;
    for at in 0..body.blocks.len() {
        let emptied = body.blocks[at].term == SIRTerm::Unreachable
            && body.blocks[at].insts.is_empty()
            && body.blocks[at].phis.is_empty();
        if live[at] || emptied {
            continue;
        }
        stats.dead += body.blocks[at].insts.len();
        stats.blocks += 1;
        body.blocks[at].phis.clear();
        body.blocks[at].insts.clear();
        body.blocks[at].term = SIRTerm::Unreachable;
        changed = true;
    }

    let held = made(body);
    let reads = operands(body);
    let mut wanted = vec![false; body.values.len()];
    let mut work: Vec<SIRValueId> = Vec::new();
    let want = |value: SIRValueId, wanted: &mut Vec<bool>, work: &mut Vec<SIRValueId>| {
        if value < wanted.len() && !wanted[value] {
            wanted[value] = true;
            work.push(value);
        }
    };

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for inst in &body.blocks[at].insts {
            if effects(&held, &inst.kind) {
                for value in SIRBody::uses(&inst.kind) {
                    want(value, &mut wanted, &mut work);
                }
            }
        }
        match &body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => want(*cond, &mut wanted, &mut work),
            SIRTerm::Return(Some(value)) => want(*value, &mut wanted, &mut work),
            _ => {}
        }
    }
    while let Some(value) = work.pop() {
        for &read in &reads[value] {
            want(read, &mut wanted, &mut work);
        }
    }

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let before = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        body.blocks[at].phis.retain(|phi| wanted[phi.def]);
        body.blocks[at].insts.retain(|inst| match inst.def {
            Some(def) => wanted[def] || effects(&held, &inst.kind),
            // An instruction that makes nothing is there for what it does, and
            // one that does nothing either is one nothing put there.
            None => effects(&held, &inst.kind),
        });
        let after = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        if after != before {
            stats.dead += before - after;
            changed = true;
        }
    }
    changed
}

// ---- Writing a call out ---------------------------------------------------

// Which body each declaration is, and which bodies each body can reach. The
// first is what a call has to be looked up in -- a `Call` names a value, the
// value is an `Item`, and the item is where the body is written -- and the
// second is what says whether writing one out would ever stop.
struct Calls {
    // By item, the body it is the body of. Only the fns that have one and take
    // no generic parameters: a generic body is one body for every type it is
    // called at, and nothing has monomorphised it, so the body written out
    // would be the wrong one for all but one caller.
    of:    HashMap<TTIRItemId, (SIRBodyId, TIRInline)>,
    // By body, the bodies it can reach through a call or a closure. Reachable
    // and not just called: a body that makes a closure may call it, and
    // whether it does is not a question this has to answer to be safe.
    reach: Vec<Vec<SIRBodyId>>,
}

impl Calls {
    fn of(program: &SIRProgram, ttir: &TTIRProgram) -> Calls {
        let mut of = HashMap::new();
        for (id, item) in ttir.items.iter().enumerate() {
            let TTIRItemKind::Fn(f) = &item.kind else { continue };
            let Some(body) = f.body else { continue };
            if !f.generics.is_empty() || body >= program.bodies.len() {
                continue;
            }
            of.insert(id, (body, f.attrs.inline));
        }

        // One step first, then closed over: reaching is the transitive
        // closure, and a body that can reach the body it stands in is one
        // nothing may be written into.
        let mut reach: Vec<Vec<SIRBodyId>> = vec![Vec::new(); program.bodies.len()];
        for (id, body) in program.bodies.iter().enumerate() {
            for block in &body.blocks {
                for inst in &block.insts {
                    let to = match &inst.kind {
                        SIRInstKind::Item(item) => of.get(item).map(|(body, _)| *body),
                        SIRInstKind::Closure { body, .. } => Some(*body),
                        _ => None,
                    };
                    if let Some(to) = to {
                        if to < reach.len() && !reach[id].contains(&to) {
                            reach[id].push(to);
                        }
                    }
                }
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for id in 0..reach.len() {
                let held = reach[id].clone();
                for to in held {
                    for &far in &reach[to].clone() {
                        if !reach[id].contains(&far) {
                            reach[id].push(far);
                            changed = true;
                        }
                    }
                }
            }
        }
        Calls { of, reach }
    }

    // Whether writing this callee into this caller is a rewrite there would
    // be no end to. Three ways, and the third is the one that is easy to miss:
    // a body written into itself, a body that can reach the one it would be
    // written into -- and a body that can reach *itself*, which is bounded
    // only by how many times this pass is willing to go round, and is a loop
    // unrolled by accident rather than a call written out.
    fn cycles(&self, callee: SIRBodyId, caller: SIRBodyId) -> bool {
        callee == caller
            || self.reach[callee].contains(&caller)
            || self.reach[callee].contains(&callee)
    }
}

// Where one call stands and what it was handed.
struct Site {
    at:     SIRBlockId,
    index:  usize,
    callee: SIRBodyId,
    args:   Vec<SIRValueId>,
    def:    Option<SIRValueId>,
}

fn inline(program: &mut SIRProgram, graph: &Calls, stats: &mut Stats) -> bool {
    let mut changed = false;
    for caller in 0..program.bodies.len() {
        for _ in 0..INLINE_EACH {
            let Some(site) = pick(program, graph, caller) else { break };
            let callee = program.bodies[site.callee].clone();
            written_out(&mut program.bodies[caller], &callee, &site);
            stats.inlined += 1;
            changed = true;
        }
    }
    changed
}

// The first call in the body worth writing out. First and not best: the ones
// refused are refused on a rule, and among the rest one call is much like
// another at this size.
fn pick(program: &SIRProgram, graph: &Calls, caller: SIRBodyId) -> Option<Site> {
    let body = &program.bodies[caller];
    let held = made(body);
    let live = body.live();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for (index, inst) in body.blocks[at].insts.iter().enumerate() {
            let SIRInstKind::Call { callee, args } = &inst.kind else { continue };
            let Some(Some(SIRInstKind::Item(item))) = held.get(*callee) else { continue };
            let Some(&(callee, asked)) = graph.of.get(item) else { continue };
            // `%noinline` is a promise and not a preference (§1): whatever
            // this pass would have made of the size, it has been answered.
            if asked == TIRInline::Never || graph.cycles(callee, caller) {
                continue;
            }
            if !worth(&program.bodies[callee], inst, args, asked) {
                continue;
            }
            return Some(Site {
                at,
                index,
                callee,
                args: args.clone(),
                def: inst.def,
            });
        }
    }
    None
}

// Whether this body may stand where this call did.
fn worth(callee: &SIRBody, call: &SIRInst, args: &[SIRValueId], asked: TIRInline) -> bool {
    if callee.params.len() != args.len() {
        return false;
    }
    let live = callee.live();
    let mut size = 0;
    for (at, block) in callee.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        size += block.insts.len();
        for inst in &block.insts {
            // A receiver is a value the caller has not got. A method is
            // called through `Method` rather than `Call` and so is not
            // reached here at all, but a fn body that names `self` would
            // be one written out with nothing to put in its place.
            if matches!(inst.kind, SIRInstKind::SelfValue | SIRInstKind::SelfAddr) {
                return false;
            }
        }
        // What the call makes has to come from somewhere on every path that
        // gets back, so a body that returns without a value cannot stand where
        // a call that makes one did.
        if call.def.is_some() && matches!(block.term, SIRTerm::Return(None)) {
            return false;
        }
    }
    // The size is this pass's guess at what a call is worth, and `%inline` is
    // the source saying it has a better one. Everything above this line is a
    // rule about whether the rewrite is *sound*, and a hint waives none of it.
    asked == TIRInline::Always || size <= INLINE_MAX
}

// The callee written into the caller at the call.
//
// Four things move, and the ids of all four are the caller's now: the values,
// the slots, the blocks, and the edges between them. The parameters are the
// exception -- they are made by no instruction, being what the caller handed
// over, so they are not copied at all and every read of one reads the argument
// instead.
//
// The call's own block is cut in two at the call. What stood above it stays;
// what stood below it, and the terminator, become a block the callee's returns
// go to. That block is where the call's value is made, by a phi over the
// blocks that returned one -- which is the one place the value can be made,
// there being as many answers as there are ways back.
fn written_out(caller: &mut SIRBody, callee: &SIRBody, site: &Site) {
    let vbase = caller.values.len();
    let sbase = caller.slots.len();
    let bbase = caller.blocks.len();
    let back = bbase + callee.blocks.len();

    caller.values.extend(callee.values.iter().cloned());
    caller.slots.extend(callee.slots.iter().cloned());

    // A parameter is the argument; everything else is itself, one arena
    // further along.
    let value = |v: SIRValueId| match callee.params.iter().position(|&p| p == v) {
        Some(index) => site.args[index],
        None => v + vbase,
    };

    let live = callee.live();
    let mut edges: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
    for (at, block) in callee.blocks.iter().enumerate() {
        let mut moved = block.clone();
        for phi in &mut moved.phis {
            phi.def += vbase;
            for (from, held) in &mut phi.edges {
                *from += bbase;
                *held = value(*held);
            }
        }
        for inst in &mut moved.insts {
            if let Some(def) = &mut inst.def {
                *def += vbase;
            }
            for held in SIRBody::uses_mut(&mut inst.kind) {
                *held = value(*held);
            }
            match &mut inst.kind {
                SIRInstKind::Addr(slot) | SIRInstKind::DropSlot(slot) => *slot += sbase,
                _ => {}
            }
        }
        match &mut moved.term {
            SIRTerm::Return(held) => {
                if live[at] {
                    if let Some(held) = held {
                        edges.push((at + bbase, value(*held)));
                    }
                }
                moved.term = SIRTerm::Goto(back);
            }
            term => {
                for to in term.targets_mut() {
                    *to += bbase;
                }
                if let SIRTerm::Branch { cond, .. } = term {
                    *cond = value(*cond);
                }
            }
        }
        caller.blocks.push(moved);
    }

    // The call's block, cut. The call itself goes: what it made is made by the
    // phi below instead.
    let tail = caller.blocks[site.at].insts.split_off(site.index + 1);
    caller.blocks[site.at].insts.pop();
    let term = std::mem::replace(
        &mut caller.blocks[site.at].term,
        SIRTerm::Goto(bbase + callee.entry),
    );
    let (line, col) = (caller.blocks[site.at].line, caller.blocks[site.at].col);

    // And whoever heard from that block hears from the block below the call.
    for to in term.targets() {
        for phi in &mut caller.blocks[to].phis {
            for (from, _) in &mut phi.edges {
                if *from == site.at {
                    *from = back;
                }
            }
        }
    }

    let mut phis = Vec::new();
    if let Some(def) = site.def {
        if !edges.is_empty() {
            phis.push(SIRPhi { def, edges });
        }
    }
    caller.blocks.push(SIRBlock { phis, insts: tail, term, line, col });
}

// ---- What would have to come before vectorization -------------------------
//
// Not written, and this is what it would take, so that the next pass over this
// file starts from the question rather than from the gap.
//
// A vector is a type before it is a rewrite. `Ty` has no vector and the SIR
// has no instruction that takes one, so the first move is not in this file at
// all: `<n x T>` in the type arena, and the loads, stores and operators over
// it in `sir_nodes.rs`. Without them there is nothing for a vectorized loop to
// be written *as*, and a pass that reshaped the loop and left it in scalars
// would have done nothing but make it longer.
//
// Then a target. How wide a vector may be, which operations the machine has
// over one, and what the two cost against the scalar loop are all facts about
// where the program is going to run, and this compiler has no back end to have
// an opinion. Guessing four would be a guess.
//
// Then the analysis, which is the real work and the reason it is not a small
// change. Two turns of a loop may be run at once only where neither writes
// what the other reads -- so it needs to know when two addresses are the same
// address, which is an alias analysis nothing here has, and when a loop's turn
// count is known before it starts, which the `Iter*` protocol answers for a
// range and not for a set. `sema::borrows` already knows a great deal about
// what may alias what, and the honest route is to carry that answer forward
// into the SIR rather than to work it out again here from the graph.
//
// What can be done first, and is worth more per line: unrolling a `for` over a
// range whose bounds are literals, which needs none of the above -- the cursor
// is a value the pass can work out, and the body is copied the number of times
// it will run. That is the same rewrite `written_out` above already does, over
// a loop instead of a call.

#[cfg(test)]
mod tests;
