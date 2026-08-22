// Which of the releases the lowering placed actually run.
//
//     A value that moves has one owner at a time, so the end of that owner is
//     the one place a release belongs: a local at the end of its block, a
//     temporary at the end of its statement, a field when the value holding it
//     goes, and nothing at all where the value was moved away first.
//                                                        (docs/prose.txt, §2)
//
// `cfg::lower` places one at the end of every block for every slot the block
// declared that has something to release. Three of the four clauses are settled
// there, by where the statement is put. The fourth is this: a slot the source
// moved away from holds nothing by the time its block ends, and releasing it
// twice is worse than not releasing it at all.
//
// It is a forward dataflow over the graph, which is what a graph is for -- the
// same question asked on the tree needs a join written by hand at every branch,
// and `sema::borrows` is where that was done because moves have to be *refused*
// where they are written and a refusal wants the line. Here nothing is refused
// and the answer is wanted per program point, so the graph answers it.
//
// A slot starts holding nothing: a `let x: T;` with no initialiser is a slot
// nobody filled, and so is every temporary before the statement that fills it.
// A `Set` fills one, a move empties it, and a parameter is filled by the caller
// before the entry block is reached.

use std::collections::HashMap;

use crate::sema::borrows::Copies;
use crate::tir::tir_nodes::TIRUnaryOp;
use crate::tir::ttir_nodes::{TTIRGeneric, TTIRProgram};

use super::cfg_nodes::*;

// What is in a slot. `Maybe` is the join of the other two: filled on one path
// and emptied on another, which is neither "release it" nor "leave it".
#[derive(Clone, Copy, PartialEq, Eq)]
enum Held {
    Nothing,
    Value,
    Maybe,
}

impl Held {
    fn join(self, other: Held) -> Held {
        if self == other {
            self
        } else {
            Held::Maybe
        }
    }
}

pub struct Drops<'a> {
    p:       &'a TTIRProgram,
    copies:  &'a Copies,
    generic: Vec<TTIRGeneric>,
}

impl<'a> Drops<'a> {
    pub fn new(p: &'a TTIRProgram, copies: &'a Copies) -> Drops<'a> {
        Drops { p, copies, generic: Vec::new() }
    }

    // Every body of the graph, each with the generics of the declaration it
    // stands in -- a `Ty::Param` is answered by those and by nothing here.
    pub fn place(&mut self, cfg: &mut CFGProgram, generics: &[Vec<TTIRGeneric>]) {
        for id in 0..cfg.bodies.len() {
            self.generic = generics.get(id).cloned().unwrap_or_default();
            self.one(cfg, id);
        }
    }

    fn one(&mut self, cfg: &mut CFGProgram, id: CFGBodyId) {
        let entry = {
            let body = &cfg.bodies[id];
            let mut state = vec![Held::Nothing; body.locals.len()];
            // "a caller did": a parameter is filled before the entry block is.
            for &slot in &body.params {
                state[slot] = Held::Value;
            }
            state
        };

        // Round the graph until nothing changes. The lattice is three high and
        // the graph is finite, so it settles.
        let mut at: HashMap<CFGBlockId, Vec<Held>> = HashMap::new();
        at.insert(cfg.bodies[id].entry, entry);
        let mut again = true;
        while again {
            again = false;
            for block in 0..cfg.bodies[id].blocks.len() {
                let Some(before) = at.get(&block).cloned() else { continue };
                let after = self.through(cfg, id, block, before);
                for next in self.leaves(&cfg.bodies[id].blocks[block].term) {
                    match at.get_mut(&next) {
                        Some(held) => {
                            let joined: Vec<Held> = held
                                .iter()
                                .zip(after.iter())
                                .map(|(&a, &b)| a.join(b))
                                .collect();
                            if joined != *held {
                                *held = joined;
                                again = true;
                            }
                        }
                        None => {
                            at.insert(next, after.clone());
                            again = true;
                        }
                    }
                }
            }
        }

        // And once more with the answers, to say what each release comes to. A
        // block nothing reaches is left alone: `opt` is what deletes those, and
        // deleting them here would be a second pass's job done in the wrong one.
        for block in 0..cfg.bodies[id].blocks.len() {
            let Some(before) = at.get(&block).cloned() else { continue };
            self.settle(cfg, id, block, before);
        }
    }

    fn leaves(&self, term: &CFGTerm) -> Vec<CFGBlockId> {
        match term {
            CFGTerm::Goto(next) => vec![*next],
            CFGTerm::Branch { then, els, .. } => vec![*then, *els],
            CFGTerm::Match { arms, otherwise, .. } => arms
                .iter()
                .map(|a| a.block)
                .chain(otherwise.iter().copied())
                .collect(),
            CFGTerm::ForEach { body, exit, .. } => vec![*body, *exit],
            CFGTerm::Return(_) | CFGTerm::Unreachable => Vec::new(),
        }
    }

    // What one block does to the state, without changing anything.
    fn through(
        &self,
        cfg: &CFGProgram,
        id: CFGBodyId,
        block: CFGBlockId,
        mut state: Vec<Held>,
    ) -> Vec<Held> {
        for i in 0..cfg.bodies[id].blocks[block].stmts.len() {
            self.step(cfg, id, &cfg.bodies[id].blocks[block].stmts[i].kind, &mut state);
        }
        if let CFGTerm::Return(Some(value)) = cfg.bodies[id].blocks[block].term {
            self.moves(cfg, id, value, &mut state);
        }
        if let CFGTerm::ForEach { local, iter, .. } = cfg.bodies[id].blocks[block].term {
            self.moves(cfg, id, iter, &mut state);
            state[local] = Held::Value;
        }
        state
    }

    fn step(&self, cfg: &CFGProgram, id: CFGBodyId, kind: &CFGStmtKind, state: &mut Vec<Held>) {
        match kind {
            CFGStmtKind::Set { local, value } => {
                self.moves(cfg, id, *value, state);
                // Filled, whatever was in it before.
                state[*local] = Held::Value;
            }
            CFGStmtKind::Store { place, value, .. } => {
                self.moves(cfg, id, *value, state);
                self.moves(cfg, id, *place, state);
            }
            CFGStmtKind::Eval(value) => self.moves(cfg, id, *value, state),
            // A release empties what it releases, so two of them in a row is
            // one release and a slot holding nothing.
            CFGStmtKind::Drop { local, .. } => state[*local] = Held::Nothing,
        }
    }

    // Every slot an expression takes the value of. A name reached into is not
    // one -- `p.x` reads a field and leaves `p` where it is -- and neither is
    // one a `&` or an `addr` was taken of.
    fn moves(&self, cfg: &CFGProgram, id: CFGBodyId, expr: CFGExprId, state: &mut Vec<Held>) {
        match &cfg.exprs[expr].kind {
            CFGExprKind::Local(local) => {
                let ty = cfg.bodies[id].locals[*local].ty;
                if !self.copies.is_copy(ty, self.p, &self.generic) {
                    state[*local] = Held::Nothing;
                }
            }
            // Reaching into a place, and taking a reference to one, both leave
            // the place where it is.
            CFGExprKind::Field { base, .. } | CFGExprKind::TupleIndex { base, .. } => {
                let _ = base;
            }
            CFGExprKind::Index { index, .. } => self.moves(cfg, id, *index, state),
            CFGExprKind::Unary { op: TIRUnaryOp::Ref(_), .. }
            | CFGExprKind::Unary { op: TIRUnaryOp::Addr, .. } => {}
            CFGExprKind::Unary { operand, .. } | CFGExprKind::Cast(operand) => {
                self.moves(cfg, id, *operand, state)
            }
            CFGExprKind::Call { callee, args } => {
                self.moves(cfg, id, *callee, state);
                for &arg in args {
                    self.moves(cfg, id, arg, state);
                }
            }
            CFGExprKind::Method { recv, args, .. } => {
                self.moves(cfg, id, *recv, state);
                for &arg in args {
                    self.moves(cfg, id, arg, state);
                }
            }
            CFGExprKind::StructLit { fields, .. }
            | CFGExprKind::VariantLit { fields, .. }
            | CFGExprKind::ArrayLit(fields)
            | CFGExprKind::TupleLit(fields)
            | CFGExprKind::Set { elems: fields, .. } => {
                for &field in fields {
                    self.moves(cfg, id, field, state);
                }
            }
            CFGExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.moves(cfg, id, key, state);
                    self.moves(cfg, id, value, state);
                }
            }
            CFGExprKind::Binary { lhs, rhs, .. } => {
                self.moves(cfg, id, *lhs, state);
                self.moves(cfg, id, *rhs, state);
            }
            CFGExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.moves(cfg, id, *held, state);
                }
            }
            _ => {}
        }
    }

    // The same walk again, writing the answer onto each release: one over a
    // slot holding nothing goes, one over a slot that may hold something keeps
    // a flag, and one over a slot that certainly does runs as it stands.
    fn settle(
        &self,
        cfg: &mut CFGProgram,
        id: CFGBodyId,
        block: CFGBlockId,
        mut state: Vec<Held>,
    ) {
        let mut keep = Vec::new();
        for i in 0..cfg.bodies[id].blocks[block].stmts.len() {
            let kind = cfg.bodies[id].blocks[block].stmts[i].kind.clone();
            if let CFGStmtKind::Drop { local, .. } = kind {
                match state[local] {
                    Held::Nothing => {
                        state[local] = Held::Nothing;
                        continue;
                    }
                    held => {
                        cfg.bodies[id].blocks[block].stmts[i].kind = CFGStmtKind::Drop {
                            local,
                            guarded: held == Held::Maybe,
                        };
                        state[local] = Held::Nothing;
                        keep.push(i);
                        continue;
                    }
                }
            }
            self.step(cfg, id, &kind, &mut state);
            keep.push(i);
        }
        let mut at = 0;
        cfg.bodies[id].blocks[block].stmts.retain(|_| {
            let held = keep.contains(&at);
            at += 1;
            held
        });
    }
}


#[cfg(test)]
mod tests;
