// Lowering the TTIR to a GIR: the last tree becoming a graph.
//
//     AST -> lower -> TIR -> [ sema ] -> TTIR -> lower -> GIR
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
// `sema` is what hands this a TTIR. The tests build one by hand instead, so
// that what is under test is this pass and not the one before it.

use crate::tir::tir_nodes::{TIRBinOp, TIRBinding, TIRIntro, TIRLit, TIRUnaryOp};
use crate::tir::ttir_nodes::*;

use crate::sema::borrows::Copies;

use super::gir_nodes::*;

pub struct Lowerer<'a> {
    ttir: &'a TTIRProgram,
    gir:  GIRProgram,
    // What each type has to release, and the declaration the body being
    // lowered stands in -- a `Ty::Param` is answered by the second.
    copies:  Copies,
    generic: Vec<TTIRGeneric>,
    // The bodies being built, innermost last: a closure's graph is begun in the
    // middle of the one that holds it.
    stack: Vec<Builder>,
}

struct Builder {
    blocks:  Vec<GIRBlock>,
    locals:  Vec<GIRLocal>,
    current: GIRBlockId,
    loops:   Vec<LoopCtx>,
    temps:   usize,
    // The temporaries the statement being lowered made that something has to
    // release -- "a temporary at the end of its statement" (§2). Not every
    // temporary: only the ones holding a value the source produced and nobody
    // keeps, which is what `kept` makes and what `close_temps` releases. The
    // slots the lowering makes for its own sake -- a branch's answer, a value
    // held across the releases of a `return` -- are not among them.
    open:    Vec<GIRLocalId>,
    // The slots each open block declared, innermost last. Leaving one is where
    // its slots are released, in the reverse of the order they were bound:
    // "locals in the reverse of it, which is the order that lets a later one
    // still refer to an earlier one" (§2).
    scopes:  Vec<Vec<GIRLocalId>>,
}

// What a body is a body of, which is `about`'s answer and nothing else's: four
// facts read off whatever owns the body, gathered before it is lowered because
// the lowering cannot go back and look.
struct About {
    params:   Vec<GIRLocalId>,
    generic:  Vec<TTIRGeneric>,
    captures: Vec<TTIRCapture>,
    env:      Option<GIRLocalId>,
}

// Where a `break` and a `continue` go, and where a `break x` puts its value.
#[derive(Clone, Copy)]
struct LoopCtx {
    brk:   GIRBlockId,
    cont:  GIRBlockId,
    value: Option<GIRLocalId>,
    // How many scopes were open when the loop began, so a `break` knows how
    // many it is leaving.
    depth: usize,
}

impl<'a> Lowerer<'a> {
    pub fn new(ttir: &'a TTIRProgram) -> Lowerer<'a> {
        Lowerer {
            ttir,
            copies: Copies::of(ttir),
            generic: Vec::new(),
            gir: GIRProgram::default(),
            stack: Vec::new(),
        }
    }

    pub fn finish(self) -> GIRProgram {
        self.gir
    }

    // Every body the program holds, in the order the TTIR keeps them, so a
    // `TTIRBodyId` and the `GIRBodyId` it became are the same number.
    // What each body is a body *of*: the parameters it was handed, the
    // declaration it stands in, and -- where it is a closure's -- what it took
    // from the body around it. A `TTIRBody` holds none of them, all being
    // facts about whatever owns it rather than about the body.
    fn about(&self, body: TTIRBodyId) -> About {
        for item in &self.ttir.items {
            let TTIRItemKind::Fn(f) = &item.kind else { continue };
            if f.body == Some(body) {
                return About {
                    params:   f.params.iter().filter_map(|p| p.slot).collect(),
                    generic:  f.generics.clone(),
                    captures: Vec::new(),
                    env:      None,
                };
            }
        }
        // A closure's body, which belongs to no declaration. Its parameters
        // are written down on the expression that made it and nowhere else,
        // that being the only place a closure is named at all -- and the
        // environment is the last of them, so a caller that leaves it off is
        // one calling something with nothing to find in it.
        for expr in &self.ttir.exprs {
            let TTIRExprKind::Closure { params, captures, env, body: held } = &expr.kind else {
                continue;
            };
            if *held != body {
                continue;
            }
            let mut params = params.clone();
            params.extend(env);
            return About {
                params,
                generic: Vec::new(),
                captures: captures.clone(),
                env: *env,
            };
        }
        About { params: Vec::new(), generic: Vec::new(), captures: Vec::new(), env: None }
    }

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

    fn new_block(&mut self, at: TTIRExprId) -> GIRBlockId {
        let (line, col) = self.at(at);
        let b = self.b();
        b.blocks.push(GIRBlock { stmts: Vec::new(), term: GIRTerm::Unreachable, line, col });
        b.blocks.len() - 1
    }

    fn switch_to(&mut self, block: GIRBlockId) {
        self.b().current = block;
    }

    // The first terminator written wins. A second would be a bug here rather
    // than a program's doing, and ignoring it is what makes `return; g()` cost
    // nothing to lower.
    fn terminate(&mut self, term: GIRTerm) {
        let b = self.b();
        let at = b.current;
        if b.blocks[at].term == GIRTerm::Unreachable {
            b.blocks[at].term = term;
        }
    }

    fn emit(&mut self, kind: GIRStmtKind, is_unsafe: bool, at: TTIRExprId) {
        let (line, col) = self.at(at);
        let b = self.b();
        let block = b.current;
        b.blocks[block].stmts.push(GIRStmt { kind, is_unsafe, line, col });
    }

    fn push_expr(&mut self, kind: GIRExprKind, ty: TyId, at: TTIRExprId) -> GIRExprId {
        let (line, col) = self.at(at);
        self.gir.exprs.push(GIRExpr { kind, ty, line, col });
        self.gir.exprs.len() - 1
    }

    // A slot for a value that has to survive a branch, typed as the expression
    // it will hold.
    fn temp(&mut self, ty: TyId) -> GIRLocalId {
        let n = {
            let b = self.b();
            let n = b.temps;
            b.temps += 1;
            n
        };
        let drops = self.copies.drops(ty, self.ttir, &self.generic);
        let b = self.b();
        b.locals.push(GIRLocal {
            name:      TIRBinding::Name(format!("${}", n)),
            ty,
            intro:     TIRIntro::Var,
            synthetic: true,
            drops,
        });
        b.locals.len() - 1
    }

    // A temporary the statement holds until its end: the same slot, and a note
    // that something is in it. A type with nothing to release needs no note --
    // there would be no release to write.
    fn kept(&mut self, ty: TyId) -> GIRLocalId {
        let slot = self.temp(ty);
        if self.b().locals[slot].drops {
            self.b().open.push(slot);
        }
        slot
    }

    // The end of a statement: every temporary it made goes, in the reverse of
    // the order they were made, as a block's locals do. Unconditional, like
    // every release the lowering places -- one the statement moved away from
    // is `gir::drops`' to take back out.
    fn close_temps(&mut self, mark: usize, at: TTIRExprId) {
        let held: Vec<GIRLocalId> = self.b().open.split_off(mark);
        self.release(&held, at);
    }

    fn local(&mut self, id: GIRLocalId, at: TTIRExprId) -> GIRExprId {
        let ty = self.b().locals[id].ty;
        self.push_expr(GIRExprKind::Local(id), ty, at)
    }

    // The graph of one body.
    fn body(&mut self, id: TTIRBodyId) -> GIRBodyId {
        let about = self.about(id);
        let held = std::mem::replace(&mut self.generic, about.generic);
        let out = self.body_of(id, about.params, about.captures, about.env);
        self.generic = held;
        out
    }

    fn body_of(
        &mut self,
        id: TTIRBodyId,
        params: Vec<GIRLocalId>,
        captures: Vec<TTIRCapture>,
        env: Option<GIRLocalId>,
    ) -> GIRBodyId {
        let source = &self.ttir.bodies[id];
        let locals: Vec<GIRLocal> = source
            .locals
            .iter()
            .map(|l| GIRLocal {
                name:      l.name.clone(),
                ty:        l.ty,
                intro:     l.intro,
                synthetic: false,
                drops:     self.copies.drops(l.ty, self.ttir, &self.generic),
            })
            .collect();
        let value = source.value;

        self.stack.push(Builder {
            blocks:  Vec::new(),
            locals,
            current: 0,
            loops:   Vec::new(),
            temps:   0,
            open:    Vec::new(),
            // The outermost scope is the frame's, and what it holds is the
            // parameters: they were filled by the caller and they go when the
            // body does, which is one scope further out than anything the body
            // declares.
            scopes:  vec![params.clone()],
        });
        let entry = self.new_block(value);
        self.switch_to(entry);

        // A body's value is what it returns, so the tail goes into a slot and
        // the graph ends by handing that slot back.
        let out = self.temp(self.ty(value));
        self.into(value, out);
        // The frame goes, and then what it worked out is handed back: the slot
        // holding the answer is not one of the frame's, so nothing released
        // here is what the body is worth.
        self.close_scope(value);
        let answer = self.local(out, value);
        self.terminate(GIRTerm::Return(Some(answer)));

        let built = self.stack.pop().expect("a body was being built");
        self.gir.bodies.push(GIRBody {
            entry,
            blocks: built.blocks,
            locals: built.locals,
            params,
            captures,
            env,
        });
        self.gir.bodies.len() - 1
    }

    // ---- Statements ------------------------------------------------------

    fn stmt(&mut self, stmt: &TTIRStmt) {
        // What the statement makes for itself goes at the end of it, which is
        // what this marks the start of. Nested, so a statement inside a block
        // inside a statement closes its own and not the ones around it.
        let mark = self.b().open.len();
        match stmt {
            TTIRStmt::Let { is_unsafe, local, init } => {
                if let Some(scope) = self.b().scopes.last_mut() {
                    scope.push(*local);
                }
                if let Some(init) = init {
                    if branches(&self.kind(*init)) {
                        self.flow(*init, Some(*local));
                    } else {
                        let value = self.value(*init);
                        self.emit(
                            GIRStmtKind::Set { local: *local, value },
                            *is_unsafe,
                            *init,
                        );
                    }
                    self.close_temps(mark, *init);
                }
            }
            TTIRStmt::Expr { is_unsafe, expr } => {
                if branches(&self.kind(*expr)) {
                    // Nothing wants the value, so nothing is given a slot.
                    self.flow(*expr, None);
                } else if let TTIRExprKind::Assign { op, place, value } = self.kind(*expr) {
                    let place = self.value(place);
                    let v = self.value(value);
                    self.emit(GIRStmtKind::Store { place, op, value: v }, *is_unsafe, *expr);
                } else if self.drops(self.ty(*expr)) {
                    // The same as `discard`: a value nobody keeps still has to
                    // be released, and it needs a slot to be released from.
                    let slot = self.kept(self.ty(*expr));
                    let value = self.value(*expr);
                    self.emit(GIRStmtKind::Set { local: slot, value }, *is_unsafe, *expr);
                } else {
                    let v = self.value(*expr);
                    self.emit(GIRStmtKind::Eval(v), *is_unsafe, *expr);
                }
                self.close_temps(mark, *expr);
            }
            // A declaration written inside a body is a declaration of the
            // program's, and its own body is lowered with the rest.
            TTIRStmt::Item(_) => {}
        }
    }

    // ---- Expressions -----------------------------------------------------

    // Puts the value of `id` into `slot`, branching if it has to.
    fn into(&mut self, id: TTIRExprId, slot: GIRLocalId) {
        if branches(&self.kind(id)) {
            self.flow(id, Some(slot));
        } else {
            let value = self.value(id);
            self.emit(GIRStmtKind::Set { local: slot, value }, false, id);
        }
    }

    // What a condition does to the graph: two edges and no operator. `&&` and
    // `||` are the whole reason this is not just `value` -- writing them as
    // branches is what short-circuiting *is*.
    fn cond(&mut self, id: TTIRExprId, then: GIRBlockId, els: GIRBlockId) {
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
                self.terminate(GIRTerm::Branch { cond, then, els });
            }
        }
    }

    // An expression that branches, lowered into the graph, with its value put
    // in `dest` where one is wanted.
    fn flow(&mut self, id: TTIRExprId, dest: Option<GIRLocalId>) {
        match self.kind(id) {
            TTIRExprKind::Block { stmts, tail } => {
                self.b().scopes.push(Vec::new());
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
                // "a local at the end of its block" -- and the tail is already
                // in the slot that outlives the block, so nothing this releases
                // is what the block is worth.
                self.close_scope(id);
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
                            self.push_expr(GIRExprKind::Literal(TIRLit::Bool(answer)), ty, id);
                        self.emit(GIRStmtKind::Set { local: slot, value }, false, id);
                    }
                    self.terminate(GIRTerm::Goto(join));
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
                self.terminate(GIRTerm::Goto(join));

                self.switch_to(e);
                match els {
                    Some(block) => match dest {
                        Some(slot) => self.into(block, slot),
                        None => self.discard(block),
                    },
                    None => self.fill_null(dest, id),
                }
                self.terminate(GIRTerm::Goto(join));
                self.switch_to(join);
            }

            TTIRExprKind::While { cond, body } => {
                let (head, inner, exit) =
                    (self.new_block(cond), self.new_block(body), self.new_block(id));
                self.terminate(GIRTerm::Goto(head));
                self.switch_to(head);
                self.cond(cond, inner, exit);
                self.switch_to(inner);
                let depth = self.b().scopes.len();
                self.b().loops.push(LoopCtx { brk: exit, cont: head, value: dest, depth });
                self.discard(body);
                self.b().loops.pop();
                self.terminate(GIRTerm::Goto(head));
                self.switch_to(exit);
                // A loop nobody broke out of yields `null`; a `break x` will
                // have written the slot itself.
                self.fill_null(dest, id);
            }

            TTIRExprKind::For { local, iter, body } => {
                // The iterator is worked out once, into a slot. A loop is a
                // head that is come back to, and what the terminator takes the
                // next of has to be the same iterator every turn round rather
                // than the expression written for it, run again.
                let held = self.kept(self.ty(iter));
                self.into(iter, held);
                let (head, inner, exit) =
                    (self.new_block(iter), self.new_block(body), self.new_block(id));
                self.terminate(GIRTerm::Goto(head));

                // The head, which is where the loop ends as well as where it
                // goes round: the two edges of a `ForEach` are the turn and
                // the way out, and both are answered here and nowhere else.
                self.switch_to(head);
                let it = self.local(held, iter);
                // What the loop takes the next of, it takes: `gir::drops` reads
                // the terminator as emptying the slot, so nothing releases the
                // iterator afterwards and the binding is what goes each turn.
                // Whether that is the right division is the iterator protocol's
                // to settle, and the language has none.
                self.terminate(GIRTerm::ForEach { local, iter: it, body: inner, exit });

                self.switch_to(inner);
                let depth = self.b().scopes.len();
                // The binding is the body's and a fresh one each turn, so it
                // is released at the end of every one -- a local of the block,
                // and held in a scope of its own because the block opens its
                // own for what it declares itself.
                self.b().scopes.push(vec![local]);
                self.b().loops.push(LoopCtx { brk: exit, cont: head, value: dest, depth });
                self.discard(body);
                self.b().loops.pop();
                self.close_scope(id);
                self.terminate(GIRTerm::Goto(head));

                self.switch_to(exit);
                self.fill_null(dest, id);
            }

            TTIRExprKind::Match { scrutinee, arms } => {
                let s = self.value(scrutinee);
                let join = self.new_block(id);
                let mut built: Vec<GIRArm> = Vec::new();
                for arm in &arms {
                    let block = self.new_block(arm.body);
                    let saved = self.b().current;
                    self.switch_to(block);
                    match dest {
                        Some(slot) => self.into(arm.body, slot),
                        None => self.discard(arm.body),
                    }
                    self.terminate(GIRTerm::Goto(join));
                    self.switch_to(saved);
                    built.push(GIRArm { pats: arm.pats.clone(), block });
                }
                // Whether the arms cover everything is settled by now, so the
                // way out is only for a scrutinee none of them took.
                self.terminate(GIRTerm::Match {
                    scrutinee: s,
                    arms: built,
                    otherwise: Some(join),
                });
                self.switch_to(join);
            }

            TTIRExprKind::Return(value) => {
                // Into a slot first, where the unwinding below has anything to
                // release. An expression built here is not evaluated here: it
                // is built into the terminator, and a terminator runs after
                // every statement of its block -- which those releases are. So
                // `return b.n` would read a slot they had already released and
                // `return take(b)` would hand over one they release again. The
                // slot stands in no scope, so nothing here releases it, and the
                // move into it is written where `drops` can see it comes first.
                let value = value.map(|v| {
                    // Worked out first, and asked afterwards whether it has to
                    // be kept: what the unwinding releases is not known until
                    // it is, since working it out is what makes the
                    // temporaries the statement holds.
                    let built = self.value(v);
                    if self.releases_below(0) && !self.settled(built) {
                        let slot = self.temp(self.ty(v));
                        self.emit(GIRStmtKind::Set { local: slot, value: built }, false, v);
                        self.local(slot, v)
                    } else {
                        built
                    }
                });
                // Everything still open goes, innermost first. The value has
                // already been worked out, so what it was made of is not among
                // what these release.
                self.unwind_to(0, id);
                self.terminate(GIRTerm::Return(value));
                let next = self.new_block(id);
                self.switch_to(next);
            }

            TTIRExprKind::Break(value) => {
                let ctx = self.b().loops.last().copied();
                if let Some(LoopCtx { brk, value: slot, depth, .. }) = ctx {
                    match (value, slot) {
                        (Some(v), Some(slot)) => self.into(v, slot),
                        // Nobody wants the answer, which is not the same as
                        // nothing happening: a loop written as a statement is
                        // worth nothing and its `break f()` still calls `f`.
                        (Some(v), None) => self.discard(v),
                        (None, _) => {}
                    }
                    // Every scope inside the loop goes; the loop's own and
                    // everything outside it are still open after the `break`.
                    self.unwind_to(depth, id);
                    self.terminate(GIRTerm::Goto(brk));
                }
                let next = self.new_block(id);
                self.switch_to(next);
            }

            TTIRExprKind::Continue => {
                let ctx = self.b().loops.last().copied();
                if let Some(LoopCtx { cont, depth, .. }) = ctx {
                    // The same, and for the same reason: the next turn round
                    // starts with the loop's own scopes and no others.
                    self.unwind_to(depth, id);
                    self.terminate(GIRTerm::Goto(cont));
                }
                let next = self.new_block(id);
                self.switch_to(next);
            }

            other => panic!("a branching expression lowered from {:?}", other),
        }
    }

    // ---- Releases --------------------------------------------------------

    // The end of a block: everything it declared goes, "locals in the reverse
    // of [the order they were declared], which is the order that lets a later
    // one still refer to an earlier one" (§2).
    fn close_scope(&mut self, at: TTIRExprId) {
        let held = self.b().scopes.pop().unwrap_or_default();
        self.release(&held, at);
    }

    // Whether what was built already stands in a slot that nothing being left
    // releases -- a temporary the lowering made for its own sake, which is
    // where `value` puts anything that branched. One of those needs no second
    // slot to survive the releases; it was never in reach of them.
    fn settled(&mut self, value: GIRExprId) -> bool {
        let slot = match self.gir.exprs[value].kind {
            GIRExprKind::Local(slot) => slot,
            _ => return false,
        };
        let b = self.b();
        !b.open.contains(&slot) && !b.scopes.iter().flatten().any(|&held| held == slot)
    }

    // Whether leaving every scope down to `depth` would release anything. A
    // value that has to outlive those releases is put in a slot first, and
    // where there is nothing to outlive the expression stands as it was
    // written -- a slot per `return` in a body that releases nothing would be
    // a node the graph has no use for.
    //
    // The temporaries of the statement being lowered count: leaving by a jump
    // releases those as well, and `return mk().n` is a read of one of them.
    fn releases_below(&mut self, depth: usize) -> bool {
        let b = self.b();
        if !b.open.is_empty() {
            return true;
        }
        let (scopes, locals) = (&b.scopes, &b.locals);
        scopes[depth..].iter().flatten().any(|&local| locals[local].drops)
    }

    // Leaving by a jump rather than by falling off the end: every scope down to
    // `depth` goes, innermost first, and the ones below it stay open because
    // the block being jumped out of is still inside them.
    fn unwind_to(&mut self, depth: usize, at: TTIRExprId) {
        // The statement is being left as well as the blocks, so what it made
        // goes too, and first: a temporary stands inside everything a block
        // declared. Not taken off the list, for the same reason the scopes go
        // back on -- what follows the jump is unreachable but still lowered.
        let temps = self.b().open.clone();
        self.release(&temps, at);
        let mut open: Vec<Vec<GIRLocalId>> = Vec::new();
        while self.b().scopes.len() > depth {
            open.push(self.b().scopes.pop().unwrap_or_default());
        }
        for held in &open {
            self.release(held, at);
        }
        // A jump does not close them for what comes after: the tree is still
        // inside those blocks, and what follows a `return` is unreachable but
        // still lowered.
        for held in open.into_iter().rev() {
            self.b().scopes.push(held);
        }
    }

    fn release(&mut self, held: &[GIRLocalId], at: TTIRExprId) {
        for &local in held.iter().rev() {
            if !self.b().locals[local].drops {
                continue;
            }
            self.emit(GIRStmtKind::Drop { local }, false, at);
        }
    }

    // An expression evaluated where its value is not wanted.
    fn discard(&mut self, id: TTIRExprId) {
        if branches(&self.kind(id)) {
            self.flow(id, None);
        } else if self.drops(self.ty(id)) {
            // Discarded is not the same as gone: `mk()` on a line of its own
            // makes a value nobody keeps, and a value nobody keeps is exactly
            // what "a temporary at the end of its statement" is about. It
            // needs a slot to be released from.
            let slot = self.kept(self.ty(id));
            self.into(id, slot);
        } else {
            let v = self.value(id);
            self.emit(GIRStmtKind::Eval(v), false, id);
        }
    }

    // A slot with nothing to put in it gets `null`, which is what a body with
    // no trailing expression yields.
    fn fill_null(&mut self, dest: Option<GIRLocalId>, at: TTIRExprId) {
        if let Some(slot) = dest {
            let ty = self.b().locals[slot].ty;
            let value = self.push_expr(GIRExprKind::Literal(TIRLit::Null), ty, at);
            self.emit(GIRStmtKind::Set { local: slot, value }, false, at);
        }
    }

    // What is reached into, worked out into a slot where it is a value the
    // statement made rather than somewhere the source can name. `mk().n` reads
    // a field of a value nobody keeps, and unless that value is in a slot
    // there is nothing for the end of the statement to release.
    //
    // A place is left alone: it is already somewhere, and putting it in a slot
    // would make a copy and read the field of the copy.
    fn based(&mut self, id: TTIRExprId) -> GIRExprId {
        let ty = self.ty(id);
        if self.drops(ty) && !place(&self.ttir.exprs[id].kind) {
            let slot = self.kept(ty);
            self.into(id, slot);
            return self.local(slot, id);
        }
        self.value(id)
    }

    // Whether a type has anything to release, answered for the declaration the
    // body being lowered stands in.
    fn drops(&self, ty: TyId) -> bool {
        self.copies.drops(ty, self.ttir, &self.generic)
    }

    // The operands of one expression, in the order they were written, with
    // every one that stands to the left of something with effects put in a slot
    // as it is reached.
    //
    // Without that it is *built* here and *worked out* where the expression
    // holding it is -- which is after the statements and the blocks that what
    // stands to its right left behind. `f() + (n = 9)` would store 9 and then
    // call `f`, and `f() + if c { g() } else { 0 }` would run the branch first.
    fn operands(&mut self, ids: &[TTIRExprId]) -> Vec<GIRExprId> {
        let mut out = Vec::with_capacity(ids.len());
        for (at, &id) in ids.iter().enumerate() {
            if ids[at + 1..].iter().any(|&rest| self.effects(rest)) {
                let value = self.pinned(id);
                out.push(value);
            } else {
                let value = self.value(id);
                out.push(value);
            }
        }
        out
    }

    // One operand worked out where it stands rather than where the expression
    // holding it is: a slot, filled here, read there.
    fn pinned(&mut self, id: TTIRExprId) -> GIRExprId {
        // Unless there is nothing to pin. A literal is the same whenever it is
        // read and so is the name of an item, and a slot for one would be a
        // node the graph has no use for.
        if matches!(
            self.ttir.exprs[id].kind,
            TTIRExprKind::Literal(_) | TTIRExprKind::Item(_) | TTIRExprKind::SelfExpr
        ) {
            return self.value(id);
        }
        let slot = self.temp(self.ty(id));
        self.into(id, slot);
        self.local(slot, id)
    }

    // Whether working an expression out leaves anything behind in the graph
    // before the expression around it is worked out: an assignment, which is a
    // statement wherever it is written, or anything that branches, which is
    // blocks. Both are why `operands` exists.
    //
    // A closure is not one: what its body does happens where it is called, and
    // that is a graph of its own.
    fn effects(&self, id: TTIRExprId) -> bool {
        let kind = &self.ttir.exprs[id].kind;
        if branches(kind) {
            return true;
        }
        match kind {
            TTIRExprKind::Assign { .. } => true,
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                self.effects(*base)
            }
            TTIRExprKind::Unary { operand, .. } => self.effects(*operand),
            TTIRExprKind::Cast(operand) => self.effects(*operand),
            TTIRExprKind::Call { callee, args } => {
                self.effects(*callee) || args.iter().any(|&a| self.effects(a))
            }
            TTIRExprKind::Method { recv, args, .. } => {
                self.effects(*recv) || args.iter().any(|&a| self.effects(a))
            }
            TTIRExprKind::Index { base, index } => self.effects(*base) || self.effects(*index),
            TTIRExprKind::Binary { lhs, rhs, .. } => self.effects(*lhs) || self.effects(*rhs),
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => {
                fields.iter().any(|&f| self.effects(f))
            }
            TTIRExprKind::Map { entries, .. } => {
                entries.iter().any(|(k, v)| self.effects(*k) || self.effects(*v))
            }
            TTIRExprKind::Range { start, end, .. } => {
                start.iter().chain(end.iter()).any(|&e| self.effects(e))
            }
            _ => false,
        }
    }

    // An expression with no control flow in it. Anything that branches is put
    // through a slot first, so what comes back is always straight-line.
    fn value(&mut self, id: TTIRExprId) -> GIRExprId {
        if branches(&self.kind(id)) {
            let slot = self.temp(self.ty(id));
            self.flow(id, Some(slot));
            return self.local(slot, id);
        }
        let ty = self.ty(id);
        let kind = match self.kind(id) {
            TTIRExprKind::Literal(value) => GIRExprKind::Literal(value),
            TTIRExprKind::Local(l) => GIRExprKind::Local(l),
            TTIRExprKind::Item(i) => GIRExprKind::Item(i),
            TTIRExprKind::SelfExpr => GIRExprKind::SelfExpr,

            TTIRExprKind::Field { base, index } => {
                GIRExprKind::Field { base: self.based(base), index }
            }
            TTIRExprKind::TupleIndex { base, index } => {
                GIRExprKind::TupleIndex { base: self.based(base), index }
            }
            TTIRExprKind::Call { callee, args } => {
                let mut all = vec![callee];
                all.extend(args.iter().copied());
                let mut built = self.operands(&all).into_iter();
                GIRExprKind::Call {
                    callee: built.next().expect("the callee"),
                    args:   built.collect(),
                }
            }
            TTIRExprKind::Method { recv, item, args } => GIRExprKind::Method {
                // Reached into rather than handed over, so the same as a
                // base: a slot only where the receiver is a value the
                // statement made and nobody keeps. A receiver that is already
                // a place stays one -- a method may be written for `&self` or
                // `*self`, and a place put in a slot is a copy of the thing
                // that was to be reached through.
                recv: self.based(recv),
                item,
                args: self.operands(&args),
            },
            TTIRExprKind::Index { base, index } => {
                GIRExprKind::Index { base: self.based(base), index: self.value(index) }
            }
            TTIRExprKind::StructLit { item, fields } => {
                GIRExprKind::StructLit { item, fields: self.operands(&fields) }
            }
            TTIRExprKind::VariantLit { item, variant, fields } => {
                GIRExprKind::VariantLit { item, variant, fields: self.operands(&fields) }
            }

            TTIRExprKind::ArrayLit(elems) => GIRExprKind::ArrayLit(self.operands(&elems)),
            TTIRExprKind::TupleLit(elems) => GIRExprKind::TupleLit(self.operands(&elems)),
            TTIRExprKind::Map { hashed, entries } => {
                // A key and its value are two operands like any other, and the
                // pairs are undone and done up again around that.
                let flat: Vec<TTIRExprId> =
                    entries.iter().flat_map(|&(k, v)| [k, v]).collect();
                let built = self.operands(&flat);
                GIRExprKind::Map {
                    hashed,
                    entries: built.chunks(2).map(|pair| (pair[0], pair[1])).collect(),
                }
            }
            TTIRExprKind::Set { hashed, elems } => {
                GIRExprKind::Set { hashed, elems: self.operands(&elems) }
            }

            TTIRExprKind::Unary { op, operand } => {
                GIRExprKind::Unary { op, operand: self.value(operand) }
            }
            TTIRExprKind::Binary { op, lhs, rhs } => {
                let built = self.operands(&[lhs, rhs]);
                GIRExprKind::Binary { op, lhs: built[0], rhs: built[1] }
            }
            TTIRExprKind::Range { op, start, end } => {
                let written: Vec<TTIRExprId> = start.iter().chain(end.iter()).copied().collect();
                let mut built = self.operands(&written).into_iter();
                GIRExprKind::Range {
                    op,
                    start: start.map(|_| built.next().expect("a start")),
                    end: end.map(|_| built.next().expect("an end")),
                }
            }
            TTIRExprKind::Cast(value) => GIRExprKind::Cast(self.value(value)),
            // The body is lowered with every other one; the handles agree
            // because the two arenas are filled in the same order.
            TTIRExprKind::Closure { captures, body, .. } => {
                GIRExprKind::Closure { captures, body }
            }

            // An assignment where a value is wanted: the store happens and the
            // answer is `null`, there being nothing else it could be.
            TTIRExprKind::Assign { op, place, value } => {
                let place = self.value(place);
                let v = self.value(value);
                self.emit(GIRStmtKind::Store { place, op, value: v }, false, id);
                GIRExprKind::Literal(TIRLit::Null)
            }

            other => panic!("an expression lowered from {:?}", other),
        };
        self.push_expr(kind, ty, id)
    }
}

// Somewhere the source can name, which is somewhere a value already is. What
// is not one is a value that was worked out, and the difference is whether
// reaching into it needs a slot to reach into.
fn place(kind: &TTIRExprKind) -> bool {
    matches!(
        kind,
        TTIRExprKind::Local(_)
            | TTIRExprKind::Item(_)
            | TTIRExprKind::SelfExpr
            | TTIRExprKind::Field { .. }
            | TTIRExprKind::TupleIndex { .. }
            | TTIRExprKind::Index { .. }
    )
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
