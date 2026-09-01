// Which of the releases the lowering placed actually run.
//
//     A value that moves has one owner at a time, so the end of that owner is
//     the one place a release belongs: a local at the end of its block, a
//     temporary at the end of its statement, a field when the value holding it
//     goes, and nothing at all where the value was moved away first.
//                                                        (docs/prose.txt, §2)
//
// `gir::lower` places one at the end of every block for every slot the block
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
//
// With one exception, and it is the receiver of `Drop::drop`. That body is what
// releasing the type *is*, so a release of its own receiver at the end of it is
// the same release again -- a routine that calls itself for ever, the moment
// anything emits a body for `__D`. Nothing is left unreleased by leaving it
// out: whatever writes those bodies runs the receiver's fields after the call
// returns, which is where they were always going to be run.

use std::collections::HashMap;

use crate::sema::borrows::Copies;
use crate::tir::tir_nodes::{TIRBinding, TIRIntro, TIRLit, TIRPrim, TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRGeneric, TTIRProgram, Ty, TyId};

use super::gir_nodes::*;

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
    // The bodies that *are* a release: the `drop` of every `impl Drop`. Their
    // receiver is the one slot in the program a release is not placed for --
    // see the header.
    releasing: Vec<GIRBodyId>,
}

impl<'a> Drops<'a> {
    pub fn new(p: &'a TTIRProgram, copies: &'a Copies) -> Drops<'a> {
        let bool = p
            .types
            .iter()
            .position(|ty| *ty == Ty::Prim(TIRPrim::Bool))
            .unwrap_or(0);
        let releasing = Copies::drop_bodies(p);
        Drops { p, copies, generic: Vec::new(), bool, releasing }
    }

    // Every body of the graph, each with the generics of the declaration it
    // stands in -- a `Ty::Param` is answered by those and by nothing here.
    pub fn place(&mut self, gir: &mut GIRProgram, generics: &[Vec<TTIRGeneric>]) {
        for id in 0..gir.bodies.len() {
            self.generic = generics.get(id).cloned().unwrap_or_default();
            self.one(gir, id);
        }
    }

    fn one(&mut self, gir: &mut GIRProgram, id: GIRBodyId) {
        let entry = {
            let body = &gir.bodies[id];
            let mut state = vec![Held::Nothing; body.locals.len()];
            // "a caller did": a parameter is filled before the entry block is.
            for &slot in &body.params {
                state[slot] = Held::Value;
            }
            // Except the receiver of a release, which is left reading as a
            // slot nobody filled. That is not what is true of it -- the caller
            // did fill it -- it is how this pass is told not to place the one
            // release that would be this body again.
            if self.releasing.contains(&id) {
                if let Some(&held) = body.params.first() {
                    state[held] = Held::Nothing;
                }
            }
            state
        };

        // Round the graph until nothing changes. The lattice is three high and
        // the graph is finite, so it settles.
        let mut at: HashMap<GIRBlockId, Vec<Held>> = HashMap::new();
        at.insert(gir.bodies[id].entry, entry);
        let mut again = true;
        while again {
            again = false;
            for block in 0..gir.bodies[id].blocks.len() {
                let Some(before) = at.get(&block).cloned() else { continue };
                let after = self.through(gir, id, block, before);
                for next in self.leaves(&gir.bodies[id].blocks[block].term) {
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
        let mut asks: Vec<(GIRBlockId, usize)> = Vec::new();
        for block in 0..gir.bodies[id].blocks.len() {
            let Some(before) = at.get(&block).cloned() else { continue };
            for held in self.settle(gir, id, block, before) {
                asks.push((block, held));
            }
        }

        // And the ones that could not be settled get a flag and a branch.
        self.elaborate(gir, id, asks);
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
    fn elaborate(&mut self, gir: &mut GIRProgram, id: GIRBodyId, asks: Vec<(GIRBlockId, usize)>) {
        if asks.is_empty() {
            return;
        }
        // One flag per slot, however many releases of it want one.
        let mut flags: HashMap<GIRLocalId, GIRLocalId> = HashMap::new();
        for &(block, at) in &asks {
            let GIRStmtKind::Drop { local } = gir.bodies[id].blocks[block].stmts[at].kind else {
                continue;
            };
            if flags.contains_key(&local) {
                continue;
            }
            let name = self.name_of(gir, id, local);
            gir.bodies[id].locals.push(GIRLocal {
                name:      TIRBinding::Name(name),
                ty:        self.bool,
                intro:     TIRIntro::Var,
                synthetic: true,
                // A flag is a `bool`, and a `bool` has nothing to release.
                drops:     false,
            });
            flags.insert(local, gir.bodies[id].locals.len() - 1);
        }

        // Every flag starts false and is written wherever what it stands for
        // is filled or emptied. Walked over the statements as they are, before
        // any block is split, so that no position moves under the walk.
        for block in 0..gir.bodies[id].blocks.len() {
            let mut out: Vec<GIRStmt> = Vec::new();
            for stmt in gir.bodies[id].blocks[block].stmts.clone() {
                let (line, col) = (stmt.line, stmt.col);
                let mut before: Vec<GIRStmt> = Vec::new();
                let mut after: Vec<GIRStmt> = Vec::new();
                match &stmt.kind {
                    // Filled: whatever it held before, it holds this now.
                    GIRStmtKind::Set { local, .. } => {
                        if let Some(&flag) = flags.get(local) {
                            after.push(self.write(gir, flag, true, line, col));
                        }
                    }
                    // Released: emptied, and the branch below reads the flag
                    // before this runs.
                    GIRStmtKind::Drop { local } => {
                        if let Some(&flag) = flags.get(local) {
                            after.push(self.write(gir, flag, false, line, col));
                        }
                    }
                    _ => {}
                }
                // And emptied wherever the source handed the value away.
                let mut state = vec![Held::Value; gir.bodies[id].locals.len()];
                self.step(gir, id, &stmt.kind, &mut state);
                for (&local, &flag) in &flags {
                    if state[local] == Held::Nothing
                        && !matches!(stmt.kind, GIRStmtKind::Drop { .. })
                    {
                        after.push(self.write(gir, flag, false, line, col));
                    }
                }
                out.append(&mut before);
                out.push(stmt);
                out.append(&mut after);
            }
            gir.bodies[id].blocks[block].stmts = out;
        }

        // The entry starts them all false: a slot nobody filled holds nothing.
        let entry = gir.bodies[id].entry;
        let (line, col) = (gir.bodies[id].blocks[entry].line, gir.bodies[id].blocks[entry].col);
        let mut opening: Vec<GIRStmt> = flags
            .values()
            .map(|&flag| self.write(gir, flag, false, line, col))
            .collect();
        opening.append(&mut gir.bodies[id].blocks[entry].stmts);
        gir.bodies[id].blocks[entry].stmts = opening;

        // And then the branches. Every block is walked again, since the flag
        // writes moved every position; a split makes two new blocks and the
        // walk reaches them, which is how several in one block are all drawn.
        //
        // `drawn` is the blocks a split made to hold a release, so that the
        // one release in each is not found again and drawn a second time.
        let mut drawn: Vec<GIRBlockId> = Vec::new();
        let mut block = 0;
        while block < gir.bodies[id].blocks.len() {
            if drawn.contains(&block) {
                block += 1;
                continue;
            }
            let found = gir.bodies[id].blocks[block].stmts.iter().position(|s| {
                matches!(&s.kind, GIRStmtKind::Drop { local } if flags.contains_key(local))
            });
            let Some(at) = found else {
                block += 1;
                continue;
            };
            let GIRStmtKind::Drop { local } = gir.bodies[id].blocks[block].stmts[at].kind else {
                block += 1;
                continue;
            };
            let flag = flags[&local];
            drawn.push(self.split(gir, id, block, at, flag));
            block += 1;
        }
    }

    // One release behind a branch on its flag. The statements after it become a
    // block of their own -- the join -- and the release becomes a block on the
    // way to it, reached only where the flag says there is something to
    // release.
    fn split(
        &mut self,
        gir: &mut GIRProgram,
        id: GIRBodyId,
        block: GIRBlockId,
        at: usize,
        flag: GIRLocalId,
    ) -> GIRBlockId {
        let (line, col) = (
            gir.bodies[id].blocks[block].stmts[at].line,
            gir.bodies[id].blocks[block].stmts[at].col,
        );
        let mut rest = gir.bodies[id].blocks[block].stmts.split_off(at);
        // The release itself, and the flag write that followed it.
        let mut run: Vec<GIRStmt> = vec![rest.remove(0)];
        if matches!(rest.first().map(|s| &s.kind), Some(GIRStmtKind::Set { local, .. }) if *local == flag)
        {
            run.push(rest.remove(0));
        }
        let term = std::mem::replace(&mut gir.bodies[id].blocks[block].term, GIRTerm::Unreachable);

        gir.bodies[id].blocks.push(GIRBlock { stmts: rest, term, line, col });
        let join = gir.bodies[id].blocks.len() - 1;
        gir.bodies[id].blocks.push(GIRBlock {
            stmts: run,
            term: GIRTerm::Goto(join),
            line,
            col,
        });
        let held = gir.bodies[id].blocks.len() - 1;

        let ty = gir.bodies[id].locals[flag].ty;
        gir.exprs.push(GIRExpr { kind: GIRExprKind::Local(flag), ty, line, col });
        let cond = gir.exprs.len() - 1;
        gir.bodies[id].blocks[block].term =
            GIRTerm::Branch { cond, then: held, els: join };
        held
    }

    fn write(
        &self,
        gir: &mut GIRProgram,
        flag: GIRLocalId,
        held: bool,
        line: usize,
        col: usize,
    ) -> GIRStmt {
        gir.exprs.push(GIRExpr {
            kind: GIRExprKind::Literal(TIRLit::Bool(held)),
            ty: self.bool,
            line,
            col,
        });
        let value = gir.exprs.len() - 1;
        GIRStmt {
            kind: GIRStmtKind::Set { local: flag, value },
            is_unsafe: false,
            line,
            col,
        }
    }

    // What to call a flag: the slot it stands for, with the `$` that says no
    // source wrote it.
    fn name_of(&self, gir: &GIRProgram, id: GIRBodyId, local: GIRLocalId) -> String {
        let held = match &gir.bodies[id].locals[local].name {
            TIRBinding::Name(name) => name.clone(),
            TIRBinding::Discard => "_".to_string(),
            TIRBinding::SelfRecv(..) => "self".to_string(),
        };
        format!("${}$held", held)
    }

    fn leaves(&self, term: &GIRTerm) -> Vec<GIRBlockId> {
        match term {
            GIRTerm::Goto(next) => vec![*next],
            GIRTerm::Branch { then, els, .. } => vec![*then, *els],
            GIRTerm::Match { arms, otherwise, .. } => arms
                .iter()
                .map(|a| a.block)
                .chain(otherwise.iter().copied())
                .collect(),
            GIRTerm::ForEach { body, exit, .. } => vec![*body, *exit],
            GIRTerm::Return(_) | GIRTerm::Unreachable => Vec::new(),
        }
    }

    // What one block does to the state, without changing anything.
    fn through(
        &self,
        gir: &GIRProgram,
        id: GIRBodyId,
        block: GIRBlockId,
        mut state: Vec<Held>,
    ) -> Vec<Held> {
        for i in 0..gir.bodies[id].blocks[block].stmts.len() {
            self.step(gir, id, &gir.bodies[id].blocks[block].stmts[i].kind, &mut state);
        }
        if let GIRTerm::Return(Some(value)) = gir.bodies[id].blocks[block].term {
            self.moves(gir, id, value, &mut state);
        }
        if let GIRTerm::ForEach { local, iter, .. } = gir.bodies[id].blocks[block].term {
            self.moves(gir, id, iter, &mut state);
            state[local] = Held::Value;
        }
        state
    }

    fn step(&self, gir: &GIRProgram, id: GIRBodyId, kind: &GIRStmtKind, state: &mut Vec<Held>) {
        match kind {
            GIRStmtKind::Set { local, value } => {
                self.moves(gir, id, *value, state);
                // Filled, whatever was in it before.
                state[*local] = Held::Value;
            }
            GIRStmtKind::Store { place, value, .. } => {
                self.moves(gir, id, *value, state);
                self.moves(gir, id, *place, state);
            }
            GIRStmtKind::Eval(value) => self.moves(gir, id, *value, state),
            // A release empties what it releases, so two of them in a row is
            // one release and a slot holding nothing.
            GIRStmtKind::Drop { local, .. } => state[*local] = Held::Nothing,
        }
    }

    // Every slot an expression takes the value of. A name reached into is not
    // one -- `p.x` reads a field and leaves `p` where it is -- and neither is
    // one a `&` or an `addr` was taken of.
    fn moves(&self, gir: &GIRProgram, id: GIRBodyId, expr: GIRExprId, state: &mut Vec<Held>) {
        match &gir.exprs[expr].kind {
            GIRExprKind::Local(local) => {
                let ty = gir.bodies[id].locals[*local].ty;
                if !self.copies.is_copy(ty, self.p, &self.generic) {
                    state[*local] = Held::Nothing;
                }
            }
            // Reaching into a place, and taking a reference to one, both leave
            // the place where it is.
            GIRExprKind::Field { base, .. } | GIRExprKind::TupleIndex { base, .. } => {
                let _ = base;
            }
            GIRExprKind::Index { index, .. } => self.moves(gir, id, *index, state),
            GIRExprKind::Unary { op: TIRUnaryOp::Ref(_), .. }
            | GIRExprKind::Unary { op: TIRUnaryOp::Addr, .. } => {}
            GIRExprKind::Unary { operand, .. } | GIRExprKind::Cast(operand) => {
                self.moves(gir, id, *operand, state)
            }
            GIRExprKind::Call { callee, args } => {
                self.moves(gir, id, *callee, state);
                for &arg in args {
                    self.moves(gir, id, arg, state);
                }
            }
            GIRExprKind::Method { recv, args, .. } => {
                self.moves(gir, id, *recv, state);
                for &arg in args {
                    self.moves(gir, id, arg, state);
                }
            }
            GIRExprKind::StructLit { fields, .. }
            | GIRExprKind::VariantLit { fields, .. }
            | GIRExprKind::ArrayLit(fields)
            | GIRExprKind::TupleLit(fields)
            | GIRExprKind::Set { elems: fields, .. } => {
                for &field in fields {
                    self.moves(gir, id, field, state);
                }
            }
            GIRExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.moves(gir, id, key, state);
                    self.moves(gir, id, value, state);
                }
            }
            GIRExprKind::Binary { lhs, rhs, .. } => {
                self.moves(gir, id, *lhs, state);
                self.moves(gir, id, *rhs, state);
            }
            GIRExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.moves(gir, id, *held, state);
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
        gir: &mut GIRProgram,
        id: GIRBodyId,
        block: GIRBlockId,
        mut state: Vec<Held>,
    ) -> Vec<usize> {
        let mut kept: Vec<GIRStmt> = Vec::new();
        let mut asks = Vec::new();
        for i in 0..gir.bodies[id].blocks[block].stmts.len() {
            let stmt = gir.bodies[id].blocks[block].stmts[i].clone();
            if let GIRStmtKind::Drop { local } = stmt.kind {
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
            self.step(gir, id, &stmt.kind, &mut state);
            kept.push(stmt);
        }
        gir.bodies[id].blocks[block].stmts = kept;
        asks
    }
}


#[cfg(test)]
mod tests;
