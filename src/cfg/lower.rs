// Lowering the TTIR to a CFG: the last tree becoming a graph.
//
//     AST -> lower -> TIR -> [ sema ] -> TTIR -> lower -> CFG
//
// Everything a declaration answers on its own was settled by the first
// lowering, and everything needing a second declaration was settled by `sema`.
// What is left is the shape of the control flow, and that is all this does:
// `if`, `while`, `for`, `match`, the jumps and the two short-circuiting
// operators stop being expressions and become edges between blocks.
//
// The one thing it adds is slots. An expression that has a value *and* branches
// -- `let x = if c { 1 } else { 2 }` -- has nowhere to put the answer once the
// branches are edges, so it gets a temporary written on both sides. Those are
// named with a `$`, which no source can collide with.
//
// Nothing calls this yet: `sema` is what would hand it a TTIR, and `sema` is
// not written. The tests build one by hand.

use crate::tir::tir_nodes::{TIRBinOp, TIRBinding, TIRIntro, TIRLit, TIRUnaryOp};
use crate::tir::ttir_nodes::*;

use super::cfg_nodes::*;

pub struct Lowerer<'a> {
    ttir: &'a TTIRProgram,
    cfg:  CFGProgram,
    // The bodies being built, innermost last: a closure's graph is begun in the
    // middle of the one that holds it.
    stack: Vec<Builder>,
}

struct Builder {
    blocks:  Vec<CFGBlock>,
    locals:  Vec<CFGLocal>,
    current: CFGBlockId,
    loops:   Vec<LoopCtx>,
    temps:   usize,
}

// Where a `break` and a `continue` go, and where a `break x` puts its value.
#[derive(Clone, Copy)]
struct LoopCtx {
    brk:   CFGBlockId,
    cont:  CFGBlockId,
    value: Option<CFGLocalId>,
}

impl<'a> Lowerer<'a> {
    pub fn new(ttir: &'a TTIRProgram) -> Lowerer<'a> {
        Lowerer { ttir, cfg: CFGProgram::default(), stack: Vec::new() }
    }

    pub fn finish(self) -> CFGProgram {
        self.cfg
    }

    // Every body the program holds, in the order the TTIR keeps them, so a
    // `TTIRBodyId` and the `CFGBodyId` it became are the same number.
    pub fn lower(&mut self) {
        for id in 0..self.ttir.bodies.len() {
            self.body(id);
        }
    }

    // ---- Reading the TTIR ------------------------------------------------

    fn kind(&self, id: TTIRExprId) -> TTIRExprKind {
        self.ttir.exprs[id].kind.clone()
    }

    fn ty(&self, id: TTIRExprId) -> TyId {
        self.ttir.exprs[id].ty
    }

    fn at(&self, id: TTIRExprId) -> (usize, usize) {
        let e = &self.ttir.exprs[id];
        (e.line, e.col)
    }

    // ---- Building --------------------------------------------------------

    fn b(&mut self) -> &mut Builder {
        self.stack.last_mut().expect("a body is being built")
    }

    fn new_block(&mut self, at: TTIRExprId) -> CFGBlockId {
        let (line, col) = self.at(at);
        let b = self.b();
        b.blocks.push(CFGBlock { stmts: Vec::new(), term: CFGTerm::Unreachable, line, col });
        b.blocks.len() - 1
    }

    fn switch_to(&mut self, block: CFGBlockId) {
        self.b().current = block;
    }

    // The first terminator written wins. A second would be a bug here rather
    // than a program's doing, and ignoring it is what makes `return; g()` cost
    // nothing to lower.
    fn terminate(&mut self, term: CFGTerm) {
        let b = self.b();
        let at = b.current;
        if b.blocks[at].term == CFGTerm::Unreachable {
            b.blocks[at].term = term;
        }
    }

    fn emit(&mut self, kind: CFGStmtKind, is_unsafe: bool, at: TTIRExprId) {
        let (line, col) = self.at(at);
        let b = self.b();
        let block = b.current;
        b.blocks[block].stmts.push(CFGStmt { kind, is_unsafe, line, col });
    }

    fn push_expr(&mut self, kind: CFGExprKind, ty: TyId, at: TTIRExprId) -> CFGExprId {
        let (line, col) = self.at(at);
        self.cfg.exprs.push(CFGExpr { kind, ty, line, col });
        self.cfg.exprs.len() - 1
    }

    // A slot for a value that has to survive a branch, typed as the expression
    // it will hold.
    fn temp(&mut self, ty: TyId) -> CFGLocalId {
        let b = self.b();
        let n = b.temps;
        b.temps += 1;
        b.locals.push(CFGLocal {
            name:      TIRBinding::Name(format!("${}", n)),
            ty,
            intro:     TIRIntro::Var,
            synthetic: true,
        });
        b.locals.len() - 1
    }

    fn local(&mut self, id: CFGLocalId, at: TTIRExprId) -> CFGExprId {
        let ty = self.b().locals[id].ty;
        self.push_expr(CFGExprKind::Local(id), ty, at)
    }

    // The graph of one body.
    fn body(&mut self, id: TTIRBodyId) -> CFGBodyId {
        let source = &self.ttir.bodies[id];
        let locals: Vec<CFGLocal> = source
            .locals
            .iter()
            .map(|l| CFGLocal {
                name:      l.name.clone(),
                ty:        l.ty,
                intro:     l.intro,
                synthetic: false,
            })
            .collect();
        let value = source.value;

        self.stack.push(Builder {
            blocks:  Vec::new(),
            locals,
            current: 0,
            loops:   Vec::new(),
            temps:   0,
        });
        let entry = self.new_block(value);
        self.switch_to(entry);

        // A body's value is what it returns, so the tail goes into a slot and
        // the graph ends by handing that slot back.
        let out = self.temp(self.ty(value));
        self.into(value, out);
        let answer = self.local(out, value);
        self.terminate(CFGTerm::Return(Some(answer)));

        let built = self.stack.pop().expect("a body was being built");
        self.cfg.bodies.push(CFGBody { entry, blocks: built.blocks, locals: built.locals });
        self.cfg.bodies.len() - 1
    }

    // ---- Statements ------------------------------------------------------

    fn stmt(&mut self, stmt: &TTIRStmt) {
        match stmt {
            TTIRStmt::Let { is_unsafe, local, init } => {
                if let Some(init) = init {
                    if branches(&self.kind(*init)) {
                        self.flow(*init, Some(*local));
                    } else {
                        let value = self.value(*init);
                        self.emit(
                            CFGStmtKind::Set { local: *local, value },
                            *is_unsafe,
                            *init,
                        );
                    }
                }
            }
            TTIRStmt::Expr { is_unsafe, expr } => {
                if branches(&self.kind(*expr)) {
                    // Nothing wants the value, so nothing is given a slot.
                    self.flow(*expr, None);
                } else if let TTIRExprKind::Assign { op, place, value } = self.kind(*expr) {
                    let place = self.value(place);
                    let v = self.value(value);
                    self.emit(CFGStmtKind::Store { place, op, value: v }, *is_unsafe, *expr);
                } else {
                    let v = self.value(*expr);
                    self.emit(CFGStmtKind::Eval(v), *is_unsafe, *expr);
                }
            }
            // A declaration written inside a body is a declaration of the
            // program's, and its own body is lowered with the rest.
            TTIRStmt::Item(_) => {}
        }
    }

    // ---- Expressions -----------------------------------------------------

    // Puts the value of `id` into `slot`, branching if it has to.
    fn into(&mut self, id: TTIRExprId, slot: CFGLocalId) {
        if branches(&self.kind(id)) {
            self.flow(id, Some(slot));
        } else {
            let value = self.value(id);
            self.emit(CFGStmtKind::Set { local: slot, value }, false, id);
        }
    }

    // What a condition does to the graph: two edges and no operator. `&&` and
    // `||` are the whole reason this is not just `value` -- writing them as
    // branches is what short-circuiting *is*.
    fn cond(&mut self, id: TTIRExprId, then: CFGBlockId, els: CFGBlockId) {
        match self.kind(id) {
            TTIRExprKind::Binary { op: TIRBinOp::And, lhs, rhs } => {
                let mid = self.new_block(rhs);
                self.cond(lhs, mid, els);
                self.switch_to(mid);
                self.cond(rhs, then, els);
            }
            TTIRExprKind::Binary { op: TIRBinOp::Or, lhs, rhs } => {
                let mid = self.new_block(rhs);
                self.cond(lhs, then, mid);
                self.switch_to(mid);
                self.cond(rhs, then, els);
            }
            // `!` swaps the edges rather than computing anything.
            TTIRExprKind::Unary { op: TIRUnaryOp::Not, operand } => {
                self.cond(operand, els, then)
            }
            _ => {
                let cond = if branches(&self.kind(id)) {
                    let slot = self.temp(self.ty(id));
                    self.flow(id, Some(slot));
                    self.local(slot, id)
                } else {
                    self.value(id)
                };
                self.terminate(CFGTerm::Branch { cond, then, els });
            }
        }
    }

    // An expression that branches, lowered into the graph, with its value put
    // in `dest` where one is wanted.
    fn flow(&mut self, id: TTIRExprId, dest: Option<CFGLocalId>) {
        match self.kind(id) {
            TTIRExprKind::Block { stmts, tail } => {
                for s in &stmts {
                    self.stmt(s);
                }
                match tail {
                    Some(t) => match dest {
                        Some(slot) => self.into(t, slot),
                        None => self.discard(t),
                    },
                    None => self.fill_null(dest, id),
                }
            }

            // The short-circuiting pair where a value is wanted: the branches
            // are the same, and each side writes the answer.
            TTIRExprKind::Binary { op: TIRBinOp::And | TIRBinOp::Or, .. } => {
                let (t, e, join) =
                    (self.new_block(id), self.new_block(id), self.new_block(id));
                self.cond(id, t, e);
                let ty = self.ty(id);
                for (block, answer) in [(t, true), (e, false)] {
                    self.switch_to(block);
                    if let Some(slot) = dest {
                        let value =
                            self.push_expr(CFGExprKind::Literal(TIRLit::Bool(answer)), ty, id);
                        self.emit(CFGStmtKind::Set { local: slot, value }, false, id);
                    }
                    self.terminate(CFGTerm::Goto(join));
                }
                self.switch_to(join);
            }

            TTIRExprKind::If { cond, then, els } => {
                let join = self.new_block(id);
                let (t, e) = (self.new_block(then), self.new_block(id));
                self.cond(cond, t, e);

                self.switch_to(t);
                match dest {
                    Some(slot) => self.into(then, slot),
                    None => self.discard(then),
                }
                self.terminate(CFGTerm::Goto(join));

                self.switch_to(e);
                match els {
                    Some(block) => match dest {
                        Some(slot) => self.into(block, slot),
                        None => self.discard(block),
                    },
                    None => self.fill_null(dest, id),
                }
                self.terminate(CFGTerm::Goto(join));
                self.switch_to(join);
            }

            TTIRExprKind::While { cond, body } => {
                let (head, inner, exit) =
                    (self.new_block(cond), self.new_block(body), self.new_block(id));
                self.terminate(CFGTerm::Goto(head));
                self.switch_to(head);
                self.cond(cond, inner, exit);
                self.switch_to(inner);
                self.b().loops.push(LoopCtx { brk: exit, cont: head, value: dest });
                self.discard(body);
                self.b().loops.pop();
                self.terminate(CFGTerm::Goto(head));
                self.switch_to(exit);
                // A loop nobody broke out of yields `null`; a `break x` will
                // have written the slot itself.
                self.fill_null(dest, id);
            }

            TTIRExprKind::For { local, iter, body } => {
                let it = self.value(iter);
                let (inner, exit) = (self.new_block(body), self.new_block(id));
                self.terminate(CFGTerm::ForEach { local, iter: it, body: inner, exit });
                self.switch_to(inner);
                self.b().loops.push(LoopCtx { brk: exit, cont: inner, value: dest });
                self.discard(body);
                self.b().loops.pop();
                self.terminate(CFGTerm::Goto(inner));
                self.switch_to(exit);
                self.fill_null(dest, id);
            }

            TTIRExprKind::Match { scrutinee, arms } => {
                let s = self.value(scrutinee);
                let join = self.new_block(id);
                let mut built: Vec<CFGArm> = Vec::new();
                for arm in &arms {
                    let block = self.new_block(arm.body);
                    let saved = self.b().current;
                    self.switch_to(block);
                    match dest {
                        Some(slot) => self.into(arm.body, slot),
                        None => self.discard(arm.body),
                    }
                    self.terminate(CFGTerm::Goto(join));
                    self.switch_to(saved);
                    built.push(CFGArm { pats: arm.pats.clone(), block });
                }
                // Whether the arms cover everything is settled by now, so the
                // way out is only for a scrutinee none of them took.
                self.terminate(CFGTerm::Match {
                    scrutinee: s,
                    arms: built,
                    otherwise: Some(join),
                });
                self.switch_to(join);
            }

            TTIRExprKind::Return(value) => {
                let value = value.map(|v| self.value(v));
                self.terminate(CFGTerm::Return(value));
                let next = self.new_block(id);
                self.switch_to(next);
            }

            TTIRExprKind::Break(value) => {
                let ctx = self.b().loops.last().copied();
                if let Some(LoopCtx { brk, value: slot, .. }) = ctx {
                    if let (Some(v), Some(slot)) = (value, slot) {
                        self.into(v, slot);
                    }
                    self.terminate(CFGTerm::Goto(brk));
                }
                let next = self.new_block(id);
                self.switch_to(next);
            }

            TTIRExprKind::Continue => {
                let ctx = self.b().loops.last().copied();
                if let Some(LoopCtx { cont, .. }) = ctx {
                    self.terminate(CFGTerm::Goto(cont));
                }
                let next = self.new_block(id);
                self.switch_to(next);
            }

            other => panic!("a branching expression lowered from {:?}", other),
        }
    }

    // An expression evaluated where its value is not wanted.
    fn discard(&mut self, id: TTIRExprId) {
        if branches(&self.kind(id)) {
            self.flow(id, None);
        } else {
            let v = self.value(id);
            self.emit(CFGStmtKind::Eval(v), false, id);
        }
    }

    // A slot with nothing to put in it gets `null`, which is what a body with
    // no trailing expression yields.
    fn fill_null(&mut self, dest: Option<CFGLocalId>, at: TTIRExprId) {
        if let Some(slot) = dest {
            let ty = self.b().locals[slot].ty;
            let value = self.push_expr(CFGExprKind::Literal(TIRLit::Null), ty, at);
            self.emit(CFGStmtKind::Set { local: slot, value }, false, at);
        }
    }

    // An expression with no control flow in it. Anything that branches is put
    // through a slot first, so what comes back is always straight-line.
    fn value(&mut self, id: TTIRExprId) -> CFGExprId {
        if branches(&self.kind(id)) {
            let slot = self.temp(self.ty(id));
            self.flow(id, Some(slot));
            return self.local(slot, id);
        }
        let ty = self.ty(id);
        let kind = match self.kind(id) {
            TTIRExprKind::Literal(value) => CFGExprKind::Literal(value),
            TTIRExprKind::Local(l) => CFGExprKind::Local(l),
            TTIRExprKind::Item(i) => CFGExprKind::Item(i),
            TTIRExprKind::SelfExpr => CFGExprKind::SelfExpr,

            TTIRExprKind::Field { base, index } => {
                CFGExprKind::Field { base: self.value(base), index }
            }
            TTIRExprKind::TupleIndex { base, index } => {
                CFGExprKind::TupleIndex { base: self.value(base), index }
            }
            TTIRExprKind::Call { callee, args } => CFGExprKind::Call {
                callee: self.value(callee),
                args: args.iter().map(|&a| self.value(a)).collect(),
            },
            TTIRExprKind::Method { recv, item, args } => CFGExprKind::Method {
                recv: self.value(recv),
                item,
                args: args.iter().map(|&a| self.value(a)).collect(),
            },
            TTIRExprKind::Index { base, index } => {
                CFGExprKind::Index { base: self.value(base), index: self.value(index) }
            }
            TTIRExprKind::StructLit { item, fields } => CFGExprKind::StructLit {
                item,
                fields: fields.iter().map(|&f| self.value(f)).collect(),
            },
            TTIRExprKind::VariantLit { item, variant, fields } => CFGExprKind::VariantLit {
                item,
                variant,
                fields: fields.iter().map(|&f| self.value(f)).collect(),
            },

            TTIRExprKind::ArrayLit(elems) => {
                CFGExprKind::ArrayLit(elems.iter().map(|&e| self.value(e)).collect())
            }
            TTIRExprKind::TupleLit(elems) => {
                CFGExprKind::TupleLit(elems.iter().map(|&e| self.value(e)).collect())
            }
            TTIRExprKind::Map { hashed, entries } => CFGExprKind::Map {
                hashed,
                entries: entries
                    .iter()
                    .map(|&(k, v)| (self.value(k), self.value(v)))
                    .collect(),
            },
            TTIRExprKind::Set { hashed, elems } => CFGExprKind::Set {
                hashed,
                elems: elems.iter().map(|&e| self.value(e)).collect(),
            },

            TTIRExprKind::Unary { op, operand } => {
                CFGExprKind::Unary { op, operand: self.value(operand) }
            }
            TTIRExprKind::Binary { op, lhs, rhs } => {
                CFGExprKind::Binary { op, lhs: self.value(lhs), rhs: self.value(rhs) }
            }
            TTIRExprKind::Range { op, start, end } => CFGExprKind::Range {
                op,
                start: start.map(|s| self.value(s)),
                end: end.map(|e| self.value(e)),
            },
            TTIRExprKind::Cast(value) => CFGExprKind::Cast(self.value(value)),
            // The body is lowered with every other one; the handles agree
            // because the two arenas are filled in the same order.
            TTIRExprKind::Closure { is_move, body } => CFGExprKind::Closure { is_move, body },

            // An assignment where a value is wanted: the store happens and the
            // answer is `null`, there being nothing else it could be.
            TTIRExprKind::Assign { op, place, value } => {
                let place = self.value(place);
                let v = self.value(value);
                self.emit(CFGStmtKind::Store { place, op, value: v }, false, id);
                CFGExprKind::Literal(TIRLit::Null)
            }

            other => panic!("an expression lowered from {:?}", other),
        };
        self.push_expr(kind, ty, id)
    }
}

// Whether lowering this expression means adding edges to the graph rather than
// building one straight-line node.
fn branches(kind: &TTIRExprKind) -> bool {
    matches!(
        kind,
        TTIRExprKind::Block { .. }
            | TTIRExprKind::If { .. }
            | TTIRExprKind::While { .. }
            | TTIRExprKind::For { .. }
            | TTIRExprKind::Match { .. }
            | TTIRExprKind::Return(_)
            | TTIRExprKind::Break(_)
            | TTIRExprKind::Continue
            | TTIRExprKind::Binary { op: TIRBinOp::And | TIRBinOp::Or, .. }
    )
}

#[cfg(test)]
mod tests;
