// Simplifying the GIR before `sema` reads it: fewer nodes, and none of them
// shapes a later pass has to carry a case for.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> GIR -> opt -> sema
//
// Every rewrite here is one that needs nothing a declaration cannot answer on
// its own, which is the same line lowering draws. That is a narrower licence
// than an optimiser usually has, and nothing here moves a value from one place
// to another: no copy propagation and no inlining.
//
// Putting a value where a name was is the rewrite that looks safest and is not.
// `let x = 5` written into every use makes each 5 a literal typed on its own,
// where the binding gave them one type between them -- so `f(x)` and `h(x)`
// wanting different integers is an error with the binding and no error without
// it. An optimiser that changes which programs compile is a bug, and the only
// thing that would make it sound is the type information this pass has not got.
//
// What every rewrite does keep is where it came from. A folded constant no
// longer holds the `+` it replaced and an eliminated branch is no longer
// reachable at all, so each is written down in a `GIRSourceMap` as it happens
// -- see `source_map.rs`. That is what leaves a later message able to name the
// source, and what an "unreachable code" warning would be built on.

use super::source_map::{Reason, Rewrite, GIRSourceMap};
use super::gir_nodes::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRLit, TIRUnaryOp};

// Rounds before the loop gives up. A fixpoint is reached in two or three on
// anything written by hand; the cap is for a rewrite that undoes another, which
// would be a bug here rather than a program's doing.
const MAX_ROUNDS: usize = 16;

// Simplifies until nothing changes, and gives back what it did. Each pass is
// run over the whole arena rather than down the tree: every expression is in
// it, so a scan reaches what a walk would and needs no walker of its own.
pub fn optimize(gir: &mut GIRProgram) -> GIRSourceMap {
    let mut map = GIRSourceMap::new();
    for round in 1..=MAX_ROUNDS {
        // Only what the items can still reach. The arena never shrinks -- a
        // rewrite points somewhere else rather than deleting -- so without this
        // a pass would go on simplifying subtrees it had already dropped, and
        // the handles the map kept would stop holding what was written.
        let mut changed = false;
        changed |= fold(gir, &mut map);
        changed |= branches(gir, &mut map);
        changed |= empty_blocks(gir, &mut map);
        changed |= unreachable(gir, &mut map);
        map.rounds = round;
        if !changed {
            return map;
        }
    }
    map
}

// ---- Constant folding -----------------------------------------------------

// What the operators do to literals, where the answer is the same whatever the
// type turns out to be.
//
// Integers fold in i64 and only where the arithmetic does not overflow it: a
// `<decimal_int>` fits i64 by section 6, so that is the widest an operand can
// be. A narrower declared type is still `sema`'s to range-check, and it checks
// the folded literal exactly as it would have checked the sum.
//
// Floats do not fold at all. `f32` and `f64` round differently and which one a
// literal is has not been decided yet, so folding in the wider of the two would
// be answering a question with the wrong type in hand.
fn fold(gir: &mut GIRProgram, map: &mut GIRSourceMap) -> bool {
    let mut changed = false;
    for id in 0..gir.exprs.len() {
        let folded = match &gir.exprs[id].kind {
            GIRExprKind::Unary { op, operand } => {
                unary(gir, *op, *operand).map(|k| (k, "a unary operator", Rewrite::Folded))
            }
            GIRExprKind::Binary { op, lhs, rhs } => binary(gir, id, *op, *lhs, *rhs),
            _ => None,
        };
        if let Some((kind, was, why)) = folded {
            let (line, col) = (gir.exprs[id].line, gir.exprs[id].col);
            map.record(id, line, col, was, why);
            gir.exprs[id].kind = kind;
            changed = true;
        }
    }
    changed
}

fn lit_of(gir: &GIRProgram, id: GIRExprId) -> Option<&TIRLit> {
    match &gir.exprs[id].kind {
        GIRExprKind::Literal(value) => Some(value),
        _ => None,
    }
}

fn unary(gir: &GIRProgram, op: TIRUnaryOp, operand: GIRExprId) -> Option<GIRExprKind> {
    let value = lit_of(gir, operand)?;
    let folded = match (op, value) {
        (TIRUnaryOp::Not, TIRLit::Bool(b)) => TIRLit::Bool(!b),
        // `-` on the widest integer there is has one value it cannot negate.
        (TIRUnaryOp::Neg, TIRLit::Int(n)) => TIRLit::Int(n.checked_neg()?),
        _ => return None,
    };
    Some(GIRExprKind::Literal(folded))
}

fn binary(
    gir: &GIRProgram,
    at: GIRExprId,
    op: TIRBinOp,
    lhs: GIRExprId,
    rhs: GIRExprId,
) -> Option<(GIRExprKind, &'static str, Rewrite)> {
    let _ = at;
    let (a, b) = (lit_of(gir, lhs)?, lit_of(gir, rhs)?);
    let folded = match (a, b) {
        (TIRLit::Int(x), TIRLit::Int(y)) => int(op, *x, *y)?,
        (TIRLit::Bool(x), TIRLit::Bool(y)) => match op {
            TIRBinOp::And => TIRLit::Bool(*x && *y),
            TIRBinOp::Or => TIRLit::Bool(*x || *y),
            TIRBinOp::Xor => TIRLit::Bool(x != y),
            TIRBinOp::Eq => TIRLit::Bool(x == y),
            TIRBinOp::Ne => TIRLit::Bool(x != y),
            _ => return None,
        },
        (TIRLit::Char(x), TIRLit::Char(y)) => compare(op, x, y)?,
        (TIRLit::Str(x), TIRLit::Str(y)) => compare(op, x, y)?,
        _ => return None,
    };
    Some((GIRExprKind::Literal(folded), "a binary operator", Rewrite::Folded))
}

fn int(op: TIRBinOp, x: i64, y: i64) -> Option<TIRLit> {
    let arithmetic = match op {
        TIRBinOp::Add => x.checked_add(y),
        TIRBinOp::Sub => x.checked_sub(y),
        TIRBinOp::Mul => x.checked_mul(y),
        // Division by zero is the program's mistake to make, not this pass's to
        // commit on its behalf.
        TIRBinOp::Div => x.checked_div(y),
        TIRBinOp::Rem => x.checked_rem(y),
        TIRBinOp::Shl => u32::try_from(y).ok().and_then(|s| x.checked_shl(s)),
        TIRBinOp::Shr => u32::try_from(y).ok().and_then(|s| x.checked_shr(s)),
        TIRBinOp::BitAnd => Some(x & y),
        TIRBinOp::BitOr => Some(x | y),
        TIRBinOp::BitXor => Some(x ^ y),
        _ => None,
    };
    if let Some(n) = arithmetic {
        return Some(TIRLit::Int(n));
    }
    // A `<<` that moved every bit out of an i64 is not the answer for a narrower
    // type either, so it is left for `sema` to have an opinion about.
    if matches!(op, TIRBinOp::Add | TIRBinOp::Sub | TIRBinOp::Mul | TIRBinOp::Div
                  | TIRBinOp::Rem | TIRBinOp::Shl | TIRBinOp::Shr) {
        return None;
    }
    compare(op, &x, &y)
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

// ---- Branches that cannot be taken ----------------------------------------

// A `Branch` whose condition is already a literal has one edge and not two, so
// it becomes the `Goto` it always was. The block it stops pointing at goes on
// the record: it was written, and nothing will run it.
fn branches(gir: &mut GIRProgram, map: &mut GIRSourceMap) -> bool {
    let mut changed = false;
    for body in 0..gir.bodies.len() {
        for block in 0..gir.bodies[body].blocks.len() {
            let GIRTerm::Branch { cond, then, els } = gir.bodies[body].blocks[block].term else {
                continue;
            };
            let taken = match lit_of(gir, cond) {
                Some(TIRLit::Bool(true)) => (then, els),
                Some(TIRLit::Bool(false)) => (els, then),
                _ => continue,
            };
            let (line, col) = {
                let node = &gir.exprs[cond];
                (node.line, node.col)
            };
            map.record(cond, line, col, "a branch", Rewrite::BranchTaken);
            let gone = &gir.bodies[body].blocks[taken.1];
            map.drop_block(body, taken.1, gone.line, gone.col, Reason::BranchNotTaken);
            gir.bodies[body].blocks[block].term = GIRTerm::Goto(taken.0);
            changed = true;
        }
    }
    changed
}

// ---- Blocks with nothing in them ------------------------------------------

// A block holding no statements and going straight on somewhere is an edge
// written twice. Whoever pointed at it points where it pointed instead.
//
// The entry stays put whatever is in it: a body's graph starts somewhere, and
// moving that is a change to what `entry` names rather than to the graph.
fn empty_blocks(gir: &mut GIRProgram, map: &mut GIRSourceMap) -> bool {
    let mut changed = false;
    for body in 0..gir.bodies.len() {
        let entry = gir.bodies[body].entry;
        // Where each empty forwarding block sends what reaches it.
        let mut forward: Vec<Option<GIRBlockId>> = vec![None; gir.bodies[body].blocks.len()];
        for id in 0..gir.bodies[body].blocks.len() {
            if id == entry {
                continue;
            }
            let b = &gir.bodies[body].blocks[id];
            if let (true, GIRTerm::Goto(to)) = (b.stmts.is_empty(), &b.term) {
                if *to != id {
                    forward[id] = Some(*to);
                }
            }
        }
        // A chain of them collapses to where the chain ends.
        let settle = |mut at: GIRBlockId, forward: &[Option<GIRBlockId>]| {
            let mut seen = 0;
            while let Some(next) = forward[at] {
                at = next;
                seen += 1;
                if seen > forward.len() {
                    break;
                }
            }
            at
        };
        for id in 0..gir.bodies[body].blocks.len() {
            let mut term = gir.bodies[body].blocks[id].term.clone();
            let before = term.clone();
            for target in targets_mut(&mut term) {
                *target = settle(*target, &forward);
            }
            if term != before {
                let b = &gir.bodies[body].blocks[id];
                map.record_block(body, id, b.line, b.col, "a block", Rewrite::Collapsed);
                gir.bodies[body].blocks[id].term = term;
                changed = true;
            }
        }
    }
    changed
}

// ---- Blocks nothing reaches -----------------------------------------------

// What the entry cannot get to is not run. The blocks stay in the arena --
// nothing here shrinks one -- and are recorded so a message can still point at
// what was written.
fn unreachable(gir: &mut GIRProgram, map: &mut GIRSourceMap) -> bool {
    let mut changed = false;
    for body in 0..gir.bodies.len() {
        let live = live_blocks(&gir.bodies[body]);
        for id in 0..gir.bodies[body].blocks.len() {
            if live[id] || gir.bodies[body].blocks[id].term == GIRTerm::Unreachable {
                continue;
            }
            let b = &gir.bodies[body].blocks[id];
            map.drop_block(body, id, b.line, b.col, Reason::AfterDiverging);
            gir.bodies[body].blocks[id].stmts.clear();
            gir.bodies[body].blocks[id].term = GIRTerm::Unreachable;
            changed = true;
        }
    }
    changed
}

// Which blocks the entry can reach.
fn live_blocks(body: &GIRBody) -> Vec<bool> {
    let mut seen = vec![false; body.blocks.len()];
    let mut stack = vec![body.entry];
    while let Some(id) = stack.pop() {
        if seen[id] {
            continue;
        }
        seen[id] = true;
        stack.extend(targets(&body.blocks[id].term));
    }
    seen
}

// The blocks a terminator can go to.
fn targets(term: &GIRTerm) -> Vec<GIRBlockId> {
    match term {
        GIRTerm::Goto(to) => vec![*to],
        GIRTerm::Branch { then, els, .. } => vec![*then, *els],
        GIRTerm::Match { arms, otherwise, .. } => {
            let mut out: Vec<GIRBlockId> = arms.iter().map(|a| a.block).collect();
            out.extend(otherwise.iter());
            out
        }
        GIRTerm::ForEach { body, exit, .. } => vec![*body, *exit],
        GIRTerm::Return(_) | GIRTerm::Unreachable => Vec::new(),
    }
}

fn targets_mut(term: &mut GIRTerm) -> Vec<&mut GIRBlockId> {
    match term {
        GIRTerm::Goto(to) => vec![to],
        GIRTerm::Branch { then, els, .. } => vec![then, els],
        GIRTerm::Match { arms, otherwise, .. } => {
            let mut out: Vec<&mut GIRBlockId> = arms.iter_mut().map(|a| &mut a.block).collect();
            out.extend(otherwise.iter_mut());
            out
        }
        GIRTerm::ForEach { body, exit, .. } => vec![body, exit],
        GIRTerm::Return(_) | GIRTerm::Unreachable => Vec::new(),
    }
}

// How many blocks the bodies can still reach, which is what the passes change.
pub fn reachable(gir: &GIRProgram) -> usize {
    gir.bodies
        .iter()
        .map(|b| live_blocks(b).iter().filter(|&&on| on).count())
        .sum()
}

#[cfg(test)]
mod tests;
