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
use crate::tir::tir_nodes::{TIRBinding, TIRIntro, TIRLit, TIRPrim, TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRGeneric, TTIRProgram, Ty, TyId};

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
    // What a flag is typed. `sema` interns it whether a program mentions one or
    // not, so that this pass always has one to hand.
    bool:    TyId,
}

impl<'a> Drops<'a> {
    pub fn new(p: &'a TTIRProgram, copies: &'a Copies) -> Drops<'a> {
        let bool = p
            .types
            .iter()
            .position(|ty| *ty == Ty::Prim(TIRPrim::Bool))
            .unwrap_or(0);
        Drops { p, copies, generic: Vec::new(), bool }
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
        let mut asks: Vec<(CFGBlockId, usize)> = Vec::new();
        for block in 0..cfg.bodies[id].blocks.len() {
            let Some(before) = at.get(&block).cloned() else { continue };
            for held in self.settle(cfg, id, block, before) {
                asks.push((block, held));
            }
        }

        // And the ones that could not be settled get a flag and a branch.
        self.elaborate(cfg, id, asks);
    }

    // ---- Flags -----------------------------------------------------------
    //
    // A slot filled on one path and moved away on another is neither "release
    // it" nor "leave it", and there is no third answer to be had at compile
    // time -- which of the two paths ran is not known until it has run. So the
    // program carries the answer: a `bool` beside the slot, false where nothing
    // is in it and true where something is, and the release stands behind a
    // branch on it.
    //
    // This is why `Drop` is unconditional. A statement meaning "release this
    // if" would be the question left in the tree, and the tree is what this
    // whole pass is here to get past.
    fn elaborate(&mut self, cfg: &mut CFGProgram, id: CFGBodyId, asks: Vec<(CFGBlockId, usize)>) {
        if asks.is_empty() {
            return;
        }
        // One flag per slot, however many releases of it want one.
        let mut flags: HashMap<CFGLocalId, CFGLocalId> = HashMap::new();
        for &(block, at) in &asks {
            let CFGStmtKind::Drop { local } = cfg.bodies[id].blocks[block].stmts[at].kind else {
                continue;
            };
            if flags.contains_key(&local) {
                continue;
            }
            let name = self.name_of(cfg, id, local);
            cfg.bodies[id].locals.push(CFGLocal {
                name:      TIRBinding::Name(name),
                ty:        self.bool,
                intro:     TIRIntro::Var,
                synthetic: true,
                // A flag is a `bool`, and a `bool` has nothing to release.
                drops:     false,
            });
            flags.insert(local, cfg.bodies[id].locals.len() - 1);
        }

        // Every flag starts false and is written wherever what it stands for
        // is filled or emptied. Walked over the statements as they are, before
        // any block is split, so that no position moves under the walk.
        for block in 0..cfg.bodies[id].blocks.len() {
            let mut out: Vec<CFGStmt> = Vec::new();
            for stmt in cfg.bodies[id].blocks[block].stmts.clone() {
                let (line, col) = (stmt.line, stmt.col);
                let mut before: Vec<CFGStmt> = Vec::new();
                let mut after: Vec<CFGStmt> = Vec::new();
                match &stmt.kind {
                    // Filled: whatever it held before, it holds this now.
                    CFGStmtKind::Set { local, .. } => {
                        if let Some(&flag) = flags.get(local) {
                            after.push(self.write(cfg, flag, true, line, col));
                        }
                    }
                    // Released: emptied, and the branch below reads the flag
                    // before this runs.
                    CFGStmtKind::Drop { local } => {
                        if let Some(&flag) = flags.get(local) {
                            after.push(self.write(cfg, flag, false, line, col));
                        }
                    }
                    _ => {}
                }
                // And emptied wherever the source handed the value away.
                let mut state = vec![Held::Value; cfg.bodies[id].locals.len()];
                self.step(cfg, id, &stmt.kind, &mut state);
                for (&local, &flag) in &flags {
                    if state[local] == Held::Nothing
                        && !matches!(stmt.kind, CFGStmtKind::Drop { .. })
                    {
                        after.push(self.write(cfg, flag, false, line, col));
                    }
                }
                out.append(&mut before);
                out.push(stmt);
                out.append(&mut after);
            }
            cfg.bodies[id].blocks[block].stmts = out;
        }

        // The entry starts them all false: a slot nobody filled holds nothing.
        let entry = cfg.bodies[id].entry;
        let (line, col) = (cfg.bodies[id].blocks[entry].line, cfg.bodies[id].blocks[entry].col);
        let mut opening: Vec<CFGStmt> = flags
            .values()
            .map(|&flag| self.write(cfg, flag, false, line, col))
            .collect();
        opening.append(&mut cfg.bodies[id].blocks[entry].stmts);
        cfg.bodies[id].blocks[entry].stmts = opening;

        // And then the branches. Every block is walked again, since the flag
        // writes moved every position; a split makes two new blocks and the
        // walk reaches them, which is how several in one block are all drawn.
        //
        // `drawn` is the blocks a split made to hold a release, so that the
        // one release in each is not found again and drawn a second time.
        let mut drawn: Vec<CFGBlockId> = Vec::new();
        let mut block = 0;
        while block < cfg.bodies[id].blocks.len() {
            if drawn.contains(&block) {
                block += 1;
                continue;
            }
            let found = cfg.bodies[id].blocks[block].stmts.iter().position(|s| {
                matches!(&s.kind, CFGStmtKind::Drop { local } if flags.contains_key(local))
            });
            let Some(at) = found else {
                block += 1;
                continue;
            };
            let CFGStmtKind::Drop { local } = cfg.bodies[id].blocks[block].stmts[at].kind else {
                block += 1;
                continue;
            };
            let flag = flags[&local];
            drawn.push(self.split(cfg, id, block, at, flag));
            block += 1;
        }
    }

    // One release behind a branch on its flag. The statements after it become a
    // block of their own -- the join -- and the release becomes a block on the
    // way to it, reached only where the flag says there is something to
    // release.
    fn split(
        &mut self,
        cfg: &mut CFGProgram,
        id: CFGBodyId,
        block: CFGBlockId,
        at: usize,
        flag: CFGLocalId,
    ) -> CFGBlockId {
        let (line, col) = (
            cfg.bodies[id].blocks[block].stmts[at].line,
            cfg.bodies[id].blocks[block].stmts[at].col,
        );
        let mut rest = cfg.bodies[id].blocks[block].stmts.split_off(at);
        // The release itself, and the flag write that followed it.
        let mut run: Vec<CFGStmt> = vec![rest.remove(0)];
        if matches!(rest.first().map(|s| &s.kind), Some(CFGStmtKind::Set { local, .. }) if *local == flag)
        {
            run.push(rest.remove(0));
        }
        let term = std::mem::replace(&mut cfg.bodies[id].blocks[block].term, CFGTerm::Unreachable);

        cfg.bodies[id].blocks.push(CFGBlock { stmts: rest, term, line, col });
        let join = cfg.bodies[id].blocks.len() - 1;
        cfg.bodies[id].blocks.push(CFGBlock {
            stmts: run,
            term: CFGTerm::Goto(join),
            line,
            col,
        });
        let held = cfg.bodies[id].blocks.len() - 1;

        let ty = cfg.bodies[id].locals[flag].ty;
        cfg.exprs.push(CFGExpr { kind: CFGExprKind::Local(flag), ty, line, col });
        let cond = cfg.exprs.len() - 1;
        cfg.bodies[id].blocks[block].term =
            CFGTerm::Branch { cond, then: held, els: join };
        held
    }

    fn write(
        &self,
        cfg: &mut CFGProgram,
        flag: CFGLocalId,
        held: bool,
        line: usize,
        col: usize,
    ) -> CFGStmt {
        cfg.exprs.push(CFGExpr {
            kind: CFGExprKind::Literal(TIRLit::Bool(held)),
            ty: self.bool,
            line,
            col,
        });
        let value = cfg.exprs.len() - 1;
        CFGStmt {
            kind: CFGStmtKind::Set { local: flag, value },
            is_unsafe: false,
            line,
            col,
        }
    }

    // What to call a flag: the slot it stands for, with the `$` that says no
    // source wrote it.
    fn name_of(&self, cfg: &CFGProgram, id: CFGBodyId, local: CFGLocalId) -> String {
        let held = match &cfg.bodies[id].locals[local].name {
            TIRBinding::Name(name) => name.clone(),
            TIRBinding::Discard => "_".to_string(),
            TIRBinding::SelfRecv(..) => "self".to_string(),
        };
        format!("${}$held", held)
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

    // The same walk again, saying what each release comes to: one over a slot
    // holding nothing goes, one over a slot that certainly holds something runs
    // as it stands, and one over a slot that may is handed back for a flag.
    //
    // The positions are into the statements this leaves behind, so that what
    // comes next can find them.
    fn settle(
        &self,
        cfg: &mut CFGProgram,
        id: CFGBodyId,
        block: CFGBlockId,
        mut state: Vec<Held>,
    ) -> Vec<usize> {
        let mut kept: Vec<CFGStmt> = Vec::new();
        let mut asks = Vec::new();
        for i in 0..cfg.bodies[id].blocks[block].stmts.len() {
            let stmt = cfg.bodies[id].blocks[block].stmts[i].clone();
            if let CFGStmtKind::Drop { local } = stmt.kind {
                let held = state[local];
                // Released or not, the slot holds nothing after this line.
                state[local] = Held::Nothing;
                if held == Held::Nothing {
                    continue;
                }
                if held == Held::Maybe {
                    asks.push(kept.len());
                }
                kept.push(stmt);
                continue;
            }
            self.step(cfg, id, &stmt.kind, &mut state);
            kept.push(stmt);
        }
        cfg.bodies[id].blocks[block].stmts = kept;
        asks
    }
}


#[cfg(test)]
mod tests;
