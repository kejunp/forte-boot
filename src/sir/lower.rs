// Lowering the GIR to the SIR: the graph again, with every value named once.
//
//     TTIR -> lower -> GIR -> lower -> SIR
//
// Three things happen here, and only the first is what "SSA" usually means.
//
// The trees go. A GIR statement hangs an expression tree off itself, and a
// tree is a shape with no place to say when each part runs. Flattening it is
// what makes the order the graph's rather than a reader's: `f(g(), h())`
// becomes the call to `g`, then the call to `h`, then the call to `f`, and
// which ran first is a fact about the block and not about an argument list.
// `gir::lower` already pinned every operand with effects into a slot, so the
// order this walk finds is the order that pass settled, written down.
//
// The two terminators the GIR left whole go. A `Match` becomes tests and
// branches -- the arms are tried in the order they were written, because the
// first arm that takes it is the one that runs and that *is* an order. A
// `for` becomes a cursor and a loop over the closed set of things the checker
// agreed to walk. Neither is a decision the GIR could have made: "how to test
// them in what order is a later question than this one", and this is later.
//
// And the names go into memory -- all of them, every local a slot, every read
// a `Load` and every write a `Store`. That looks like the opposite of SSA and
// is how it is reached: `sir::promote` takes back out every slot whose address
// never goes anywhere but a load or a store, and putting them all in first is
// what lets one rule decide which come out rather than a guess made here,
// where the uses have not all been seen yet.
//
// So what leaves this pass is already SSA -- every value is made by one
// instruction -- and it is SSA with the names still in the frame. What makes
// it worth reading is the pass after.

use std::collections::HashMap;

use crate::gir::gir_nodes::*;
use crate::tir::tir_nodes::{TIRAssignOp, TIRBinOp, TIRBinding, TIRLit, TIRPrim, TIRRangeOp,
                            TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRPatId, TTIRPatKind, TTIRProgram, Ty, TyId};

use super::sir_nodes::*;

pub struct Lowerer<'a> {
    ttir: &'a TTIRProgram,
    gir:  &'a GIRProgram,
    out:  SIRProgram,
    // The two types this pass needs and the source may never have mentioned: a
    // comparison answers with one and a cursor is counted in the other. `sema`
    // interns `bool` whether a program names it or not; the rest is looked up
    // and falls back to the first type in the arena, which is what `gir::drops`
    // does with the same problem and for the same reason -- a type that is not
    // there is a type nothing can be written with either.
    bool: TyId,
    int:  TyId,
    b:    Builder,
}

#[derive(Default)]
struct Builder {
    blocks:  Vec<SIRBlock>,
    values:  Vec<SIRValue>,
    slots:   Vec<SIRSlot>,
    params:  Vec<SIRValueId>,
    current: SIRBlockId,
    // The slot each GIR local went into, by that local's id.
    slot_of: Vec<SIRSlotId>,
    // Where an edge into each GIR block lands. For a block that ends in a
    // `ForEach` this is the pre-header, which is not where an edge from inside
    // the loop should go -- see `edge_to`.
    at:      Vec<SIRBlockId>,
    loops:   HashMap<GIRBlockId, Walk>,
    // The GIR block being translated, which is the "from" of every edge this
    // pass writes.
    from:    GIRBlockId,
    // Whether the statement being lowered stood under an `unsafe`, carried on
    // to every instruction it becomes.
    unsafe_: bool,
}

// What a `for` needs that the terminator does not hold: where the test lives,
// where the cursor is kept, and which blocks are the loop's own.
struct Walk {
    head:   SIRBlockId,
    cursor: SIRSlotId,
    // By GIR block: whether it stands inside this loop. An edge into the head
    // from inside is the turn of the loop and must not run the pre-header
    // again -- that would put the cursor back before the first and the loop
    // would never end.
    inside: Vec<bool>,
}

impl<'a> Lowerer<'a> {
    pub fn new(ttir: &'a TTIRProgram, gir: &'a GIRProgram) -> Lowerer<'a> {
        Lowerer {
            ttir,
            gir,
            out: SIRProgram::default(),
            bool: prim(ttir, TIRPrim::Bool),
            int: prim(ttir, TIRPrim::I64),
            b: Builder::default(),
        }
    }

    pub fn finish(self) -> SIRProgram {
        self.out
    }

    // Every body the graph holds, in the order it holds them, so a `GIRBodyId`
    // and the `SIRBodyId` it became are the same number -- which is what lets a
    // `Closure` keep pointing at the body it always pointed at.
    pub fn lower(&mut self) {
        for id in 0..self.gir.bodies.len() {
            let built = self.body(id);
            self.out.bodies.push(built);
        }
    }

    // ---- One body ---------------------------------------------------------

    fn body(&mut self, id: GIRBodyId) -> SIRBody {
        let source = &self.gir.bodies[id];
        self.b = Builder::default();

        // A slot per local, before anything reads one: a block may be
        // translated before the block that declared what it reads.
        for (local, held) in source.locals.iter().enumerate() {
            self.b.slots.push(SIRSlot {
                name:      held.name.clone(),
                ty:        held.ty,
                of:        Some(local),
                drops:     held.drops,
                synthetic: held.synthetic,
            });
            self.b.slot_of.push(self.b.slots.len() - 1);
        }

        // A block per GIR block, likewise: an edge may be written before its
        // target has been reached.
        self.b.at = Vec::with_capacity(source.blocks.len());
        for block in &source.blocks {
            let at = self.new_block(block.line, block.col);
            self.b.at.push(at);
        }
        // And the loops, which need a head and a cursor that both the
        // pre-header and the test can name.
        for (at, block) in source.blocks.iter().enumerate() {
            let GIRTerm::ForEach { body, .. } = &block.term else { continue };
            let head = self.new_block(block.line, block.col);
            let cursor = self.slot(TIRBinding::Name(format!("$cursor{}", at)), self.int, false);
            let inside = self.inside(source, at, *body);
            self.b.loops.insert(at, Walk { head, cursor, inside });
        }

        // The entry is this pass's own, and holds one thing: the parameters
        // going into the slots the rest of the body reads them out of. A
        // parameter is made by no instruction -- the caller made it -- and the
        // store is what puts it somewhere the same rule reaches.
        let (line, col) = (source.blocks[source.entry].line, source.blocks[source.entry].col);
        let entry = self.new_block(line, col);
        self.switch_to(entry);
        for &param in &source.params.clone() {
            let ty = self.b.slots[self.b.slot_of[param]].ty;
            let value = self.new_value(ty, Some(param), line, col);
            self.b.params.push(value);
            let to = self.address_of_slot(self.b.slot_of[param], line, col);
            self.effect(SIRInstKind::Store { to, value }, line, col);
        }
        let first = self.b.at[source.entry];
        self.terminate(SIRTerm::Goto(first));

        for at in 0..source.blocks.len() {
            self.block(id, at);
        }

        let built = std::mem::take(&mut self.b);
        SIRBody {
            entry,
            blocks: built.blocks,
            values: built.values,
            slots: built.slots,
            params: built.params,
        }
    }

    // Which GIR blocks stand inside the loop whose test is at `head`:
    // everything the body reaches without going back through the head. That is
    // the whole of what "inside" has to mean here -- a `continue` jumps to the
    // head and a `break` jumps past it, and only the first must not run the
    // pre-header again.
    fn inside(&self, body: &GIRBody, head: GIRBlockId, start: GIRBlockId) -> Vec<bool> {
        let mut seen = vec![false; body.blocks.len()];
        let mut stack = vec![start];
        while let Some(at) = stack.pop() {
            if at == head || seen[at] {
                continue;
            }
            seen[at] = true;
            stack.extend(goes_to(&body.blocks[at].term));
        }
        seen
    }

    fn block(&mut self, id: GIRBodyId, at: GIRBlockId) {
        let block = self.gir.bodies[id].blocks[at].clone();
        self.b.from = at;

        // A `for`'s pre-header, which is what `at` names for this block: the
        // cursor is put before the first and the test is left to the head.
        // Every edge from outside comes through here and every edge from
        // inside goes straight to the head, which is what makes the head the
        // one block that both kinds of turn pass through.
        if let Some(walk) = self.b.loops.get(&at) {
            let (head, cursor) = (walk.head, walk.cursor);
            self.switch_to(self.b.at[at]);
            let start = self.push(SIRInstKind::IterStart, self.int, block.line, block.col);
            let to = self.address_of_slot(cursor, block.line, block.col);
            self.effect(SIRInstKind::Store { to, value: start }, block.line, block.col);
            self.terminate(SIRTerm::Goto(head));
            self.switch_to(head);
        } else {
            self.switch_to(self.b.at[at]);
        }

        for stmt in &block.stmts {
            self.stmt(stmt);
        }
        self.b.unsafe_ = false;
        self.term(&block.term, block.line, block.col);
    }

    // ---- Statements -------------------------------------------------------

    fn stmt(&mut self, stmt: &GIRStmt) {
        self.b.unsafe_ = stmt.is_unsafe;
        let (line, col) = (stmt.line, stmt.col);
        match &stmt.kind {
            GIRStmtKind::Set { local, value } => {
                let value = self.value(*value);
                let to = self.address_of_slot(self.b.slot_of[*local], line, col);
                self.effect(SIRInstKind::Store { to, value }, line, col);
            }
            GIRStmtKind::Store { place, op, value } => {
                // The place first, then the value: that is the order the
                // source wrote them in, and a place may be an index whose
                // computation has effects of its own.
                let to = self.address(*place);
                let mut value = self.value(*value);
                if let Some(op) = compound(*op) {
                    // `x += 1` reads before it writes, and the read is of the
                    // place rather than of a copy taken earlier.
                    let ty = self.gir.exprs[*place].ty;
                    let lhs = self.push(SIRInstKind::Load { from: to }, ty, line, col);
                    value = self.push(SIRInstKind::Binary { op, lhs, rhs: value }, ty, line, col);
                }
                self.effect(SIRInstKind::Store { to, value }, line, col);
            }
            // Made and not kept. The instruction still names what it made --
            // a value with no reader is what "evaluated for what it does" is,
            // and the GIR's `Eval` had nothing else to say.
            GIRStmtKind::Eval(expr) => {
                self.value(*expr);
            }
            GIRStmtKind::Drop { local } => {
                let slot = self.b.slot_of[*local];
                self.effect(SIRInstKind::DropSlot(slot), line, col);
            }
        }
    }

    // ---- Terminators ------------------------------------------------------

    fn term(&mut self, term: &GIRTerm, line: usize, col: usize) {
        match term {
            GIRTerm::Goto(to) => {
                let to = self.edge_to(*to);
                self.terminate(SIRTerm::Goto(to));
            }
            GIRTerm::Branch { cond, then, els } => {
                let cond = self.value(*cond);
                let (then, els) = (self.edge_to(*then), self.edge_to(*els));
                self.terminate(SIRTerm::Branch { cond, then, els });
            }
            GIRTerm::Return(value) => {
                let value = value.map(|v| self.value(v));
                self.terminate(SIRTerm::Return(value));
            }
            GIRTerm::Unreachable => self.terminate(SIRTerm::Unreachable),
            GIRTerm::Match { scrutinee, arms, otherwise } => {
                self.decide(*scrutinee, arms, *otherwise, line, col);
            }
            GIRTerm::ForEach { local, iter, body, exit } => {
                self.walk(*local, *iter, *body, *exit, line, col);
            }
        }
    }

    // Where an edge from the block being translated to `to` actually lands.
    // The only block with two answers is a `for`'s: from inside the loop the
    // edge is the turn and goes to the test, and from anywhere else it is the
    // way in and goes to the pre-header.
    fn edge_to(&self, to: GIRBlockId) -> SIRBlockId {
        match self.b.loops.get(&to) {
            Some(walk) if walk.inside.get(self.b.from).copied().unwrap_or(false) => walk.head,
            _ => self.b.at[to],
        }
    }

    // ---- What a match becomes ---------------------------------------------
    //
    // The arms in the order they were written, and each arm's alternatives in
    // the order they were written, because that order is what a match *means*:
    // the first pattern that takes the scrutinee is the arm that runs. A
    // cleverer tree -- one that tests each field once across all the arms -- is
    // a later question again, and it has to give the same answer as this.
    //
    // A binding is not made where it is matched. The tests of one alternative
    // may fail half way through, and a name bound by the half that passed
    // would be a name written on a path the arm never runs on. They are
    // collected and written out together in a block of their own, which the
    // whole of that alternative's testing dominates.
    fn decide(
        &mut self,
        scrutinee: GIRExprId,
        arms: &[GIRArm],
        otherwise: Option<GIRBlockId>,
        line: usize,
        col: usize,
    ) {
        let on = self.value(scrutinee);
        for arm in arms {
            let block = self.edge_to(arm.block);
            for &pat in &arm.pats {
                let fail = self.new_block(line, col);
                let mut binds = Vec::new();
                self.test(pat, on, fail, &mut binds);
                for (slot, value) in binds {
                    let to = self.address_of_slot(slot, line, col);
                    self.effect(SIRInstKind::Store { to, value }, line, col);
                }
                self.terminate(SIRTerm::Goto(block));
                self.switch_to(fail);
            }
        }
        // Nothing took it. Whether the arms cover everything was settled by
        // `sema`, so the GIR always hands a way out -- but a `Match` with none
        // is a shape this has to answer for rather than assume away.
        match otherwise {
            Some(to) => {
                let to = self.edge_to(to);
                self.terminate(SIRTerm::Goto(to));
            }
            None => self.terminate(SIRTerm::Unreachable),
        }
    }

    // The tests one pattern asks of one value. Each failure goes to `fail`;
    // each success falls into a fresh block, which is where the caller carries
    // on. Nothing here branches on a pattern that cannot fail, so a wildcard
    // and a bare binding cost no blocks at all.
    fn test(
        &mut self,
        pat: TTIRPatId,
        on: SIRValueId,
        fail: SIRBlockId,
        binds: &mut Vec<(SIRSlotId, SIRValueId)>,
    ) {
        let held = self.ttir.pats[pat].clone();
        let (line, col) = (held.line, held.col);
        match held.kind {
            TTIRPatKind::Wildcard => {}
            // A pattern binds a TTIR local, and `gir::lower` made its slots
            // from the TTIR's locals in that order -- so the two are the one
            // number, and every local a pattern can name is one the body
            // declared.
            TTIRPatKind::Bind(local) => binds.push((self.b.slot_of[local], on)),
            TTIRPatKind::Lit { negated, value } => {
                let lit = self.push(SIRInstKind::Literal(negate(negated, value)), held.ty, line,
                                    col);
                self.check(TIRBinOp::Eq, on, lit, fail, line, col);
            }
            TTIRPatKind::Const(item) => {
                let lit = self.push(SIRInstKind::Item(item), held.ty, line, col);
                self.check(TIRBinOp::Eq, on, lit, fail, line, col);
            }
            TTIRPatKind::Range { op, lo, hi } => {
                if let Some(lo) = self.bound(lo) {
                    self.check(TIRBinOp::Ge, on, lo, fail, line, col);
                }
                if let Some(hi) = self.bound(hi) {
                    let op = match op {
                        TIRRangeOp::Inclusive => TIRBinOp::Le,
                        TIRRangeOp::Exclusive => TIRBinOp::Lt,
                    };
                    self.check(op, on, hi, fail, line, col);
                }
            }
            TTIRPatKind::Variant { item, variant, elems } => {
                // Which variant first, and the payload only afterwards:
                // reading a field of a variant the value is not is reading a
                // field that is not there.
                let tag = self.push(SIRInstKind::Discriminant(on), self.int, line, col);
                let value = self.tag_of(item, variant);
                let lit = self.push(SIRInstKind::Literal(TIRLit::Int(value)), self.int, line, col);
                self.check(TIRBinOp::Eq, tag, lit, fail, line, col);
                for (index, &elem) in elems.iter().enumerate() {
                    let ty = self.ttir.pats[elem].ty;
                    let of = self.push(SIRInstKind::Payload { of: on, variant, index }, ty, line,
                                       col);
                    self.test(elem, of, fail, binds);
                }
            }
            TTIRPatKind::Tuple(elems) => {
                for (index, &elem) in elems.iter().enumerate() {
                    let ty = self.ttir.pats[elem].ty;
                    let base = self.push(
                        SIRInstKind::TupleIndex { base: on, index: index as u64 },
                        ty,
                        line,
                        col,
                    );
                    self.test(elem, base, fail, binds);
                }
            }
            // Fields in declaration order, and the ones the pattern did not
            // name are not read: `Point { x }` asks nothing of `y`.
            TTIRPatKind::Struct { fields, .. } => {
                for (index, elem) in fields.iter().enumerate() {
                    let Some(elem) = elem else { continue };
                    let ty = self.ttir.pats[*elem].ty;
                    let base =
                        self.push(SIRInstKind::Field { base: on, index }, ty, line, col);
                    self.test(*elem, base, fail, binds);
                }
            }
        }
    }

    // One test, and the branch that carries it out. The success side is a new
    // block rather than the one being built, because a test that passed is a
    // point every later test of the same pattern is reached through.
    fn check(
        &mut self,
        op: TIRBinOp,
        lhs: SIRValueId,
        rhs: SIRValueId,
        fail: SIRBlockId,
        line: usize,
        col: usize,
    ) {
        let cond = self.push(SIRInstKind::Binary { op, lhs, rhs }, self.bool, line, col);
        let then = self.new_block(line, col);
        self.terminate(SIRTerm::Branch { cond, then, els: fail });
        self.switch_to(then);
    }

    // What one end of a range pattern comes to. A literal or a constant, which
    // is what a range's ends can be; an open end -- `..5` -- is a wildcard
    // there and asks nothing.
    fn bound(&mut self, pat: TTIRPatId) -> Option<SIRValueId> {
        let held = self.ttir.pats[pat].clone();
        let (line, col) = (held.line, held.col);
        match held.kind {
            TTIRPatKind::Lit { negated, value } => {
                Some(self.push(SIRInstKind::Literal(negate(negated, value)), held.ty, line, col))
            }
            TTIRPatKind::Const(item) => {
                Some(self.push(SIRInstKind::Item(item), held.ty, line, col))
            }
            _ => None,
        }
    }

    // The number the checker gave a variant, which is what a discriminant is
    // compared against. Its place in the list is not it: `%repr` does not
    // exist yet but a written `= 3` does, and the checker has already worked
    // out what each one comes to.
    fn tag_of(&self, item: crate::tir::ttir_nodes::TTIRItemId, variant: usize) -> i64 {
        match &self.ttir.items[item].kind {
            TTIRItemKind::Enum { variants, .. } => {
                variants.get(variant).map(|v| v.value).unwrap_or(variant as i64)
            }
            _ => variant as i64,
        }
    }

    // ---- What a for becomes -----------------------------------------------
    //
    // The head, which every turn passes through: the cursor is advanced, and
    // whether it landed on anything is what the loop turns on.
    //
    //     head:   %it = <the iterable>
    //             %c  = load  $cursor
    //             %c' = step  %it, %c
    //                   store $cursor, %c'
    //             %ok = valid %it, %c'
    //             branch %ok -> elem, exit
    //     elem:   %e  = elem  %it, %c'
    //                   store $x, %e
    //             goto <the body>
    //
    // Advancing first is what makes the head the only block the loop needs.
    // The pre-header put the cursor *before* the first, so the first turn's
    // advance lands on the first element and every later one on the next; if
    // the step stood at the end of the body instead there would have to be a
    // block per way back in, and a `continue` is one of those.
    //
    // The iterable is worked out again each turn, which is what the GIR says
    // to do: `gir::lower` put it in a slot of its own before the loop and the
    // terminator holds a read of that slot, so "again" is a load and the
    // iterator is the same one every time.
    fn walk(
        &mut self,
        local: GIRLocalId,
        iter: GIRExprId,
        body: GIRBlockId,
        exit: GIRBlockId,
        line: usize,
        col: usize,
    ) {
        let cursor = self.b.loops[&self.b.from].cursor;
        let it = self.value(iter);

        let from = self.address_of_slot(cursor, line, col);
        let held = self.push(SIRInstKind::Load { from }, self.int, line, col);
        let next = self.push(SIRInstKind::IterStep { iter: it, at: held }, self.int, line, col);
        let to = self.address_of_slot(cursor, line, col);
        self.effect(SIRInstKind::Store { to, value: next }, line, col);

        let cond = self.push(SIRInstKind::IterValid { iter: it, at: next }, self.bool, line, col);
        let elem = self.new_block(line, col);
        let els = self.edge_to(exit);
        self.terminate(SIRTerm::Branch { cond, then: elem, els });

        // The binding is the body's and a fresh one each turn, which is what
        // the store says: the slot is written at the top of every turn and
        // `gir::lower` put its release at the bottom of one.
        self.switch_to(elem);
        let slot = self.b.slot_of[local];
        let ty = self.b.slots[slot].ty;
        let value = self.push(SIRInstKind::IterElem { iter: it, at: next }, ty, line, col);
        let to = self.address_of_slot(slot, line, col);
        self.effect(SIRInstKind::Store { to, value }, line, col);
        let to = self.edge_to(body);
        self.terminate(SIRTerm::Goto(to));
    }

    // ---- Expressions ------------------------------------------------------

    // One GIR expression, flattened into the instructions that build it and
    // answered with the value the last of them makes. Post-order: an operand
    // is emitted before the thing that reads it, which is the order it runs in.
    fn value(&mut self, id: GIRExprId) -> SIRValueId {
        let held = self.gir.exprs[id].clone();
        let (ty, line, col) = (held.ty, held.line, held.col);
        let kind = match held.kind {
            GIRExprKind::Literal(lit) => SIRInstKind::Literal(lit),
            GIRExprKind::Item(item) => SIRInstKind::Item(item),
            GIRExprKind::SelfExpr => SIRInstKind::SelfValue,

            // Reading a name is reading what is in its slot. Every one of
            // these is a load that `sir::promote` expects to take back out
            // again -- which it can, unless something took the address too.
            GIRExprKind::Local(local) => {
                let from = self.address_of_slot(self.b.slot_of[local], line, col);
                SIRInstKind::Load { from }
            }

            // Taking a reference *is* taking the address; the two spellings
            // the language has -- `&x` and `*x` -- differ in what may be done
            // through the result and not in what the result is. `addr x` is
            // the same again with the checker's answers left behind.
            //
            // The address is retyped to what the source gave it rather than
            // wrapped in an instruction that does nothing. It is a value this
            // call has just made, so nothing else is holding it to the type it
            // had a moment ago.
            GIRExprKind::Unary { op: TIRUnaryOp::Ref(_) | TIRUnaryOp::Addr, operand } => {
                let at = self.address(operand);
                self.b.values[at].ty = ty;
                return at;
            }
            GIRExprKind::Unary { op, operand } => {
                let operand = self.value(operand);
                SIRInstKind::Unary { op, operand }
            }
            GIRExprKind::Binary { op, lhs, rhs } => {
                let (lhs, rhs) = (self.value(lhs), self.value(rhs));
                SIRInstKind::Binary { op, lhs, rhs }
            }
            GIRExprKind::Cast(of) => SIRInstKind::Cast(self.value(of)),
            GIRExprKind::Range { op, start, end } => SIRInstKind::Range {
                op,
                start: start.map(|v| self.value(v)),
                end: end.map(|v| self.value(v)),
            },

            GIRExprKind::Field { base, index } => {
                let base = self.value(base);
                SIRInstKind::Field { base, index }
            }
            GIRExprKind::TupleIndex { base, index } => {
                let base = self.value(base);
                SIRInstKind::TupleIndex { base, index }
            }
            GIRExprKind::Index { base, index } => {
                let (base, index) = (self.value(base), self.value(index));
                SIRInstKind::Index { base, index }
            }

            GIRExprKind::Call { callee, args } => {
                let callee = self.value(callee);
                SIRInstKind::Call { callee, args: self.values(&args) }
            }
            GIRExprKind::Method { recv, item, args } => {
                let recv = self.value(recv);
                SIRInstKind::Method { recv, item, args: self.values(&args) }
            }

            GIRExprKind::StructLit { item, fields } => {
                SIRInstKind::StructLit { item, fields: self.values(&fields) }
            }
            GIRExprKind::VariantLit { item, variant, fields } => {
                SIRInstKind::VariantLit { item, variant, fields: self.values(&fields) }
            }
            GIRExprKind::ArrayLit(elems) => SIRInstKind::ArrayLit(self.values(&elems)),
            GIRExprKind::TupleLit(elems) => SIRInstKind::TupleLit(self.values(&elems)),
            GIRExprKind::Map { hashed, entries } => SIRInstKind::Map {
                hashed,
                entries: entries
                    .iter()
                    .map(|(k, v)| {
                        let k = self.value(*k);
                        (k, self.value(*v))
                    })
                    .collect(),
            },
            GIRExprKind::Set { hashed, elems } => {
                SIRInstKind::Set { hashed, elems: self.values(&elems) }
            }
            // The body is a graph of its own and keeps its number.
            GIRExprKind::Closure { captures, body } => SIRInstKind::Closure { captures, body },
        };
        self.push(kind, ty, line, col)
    }

    fn values(&mut self, ids: &[GIRExprId]) -> Vec<SIRValueId> {
        ids.iter().map(|id| self.value(*id)).collect()
    }

    // Where an expression *is*, rather than what it holds. The six shapes a
    // place can have are the six `gir::lower` named, and each is a projection
    // off the one before it, so a place is a root and a path down from it.
    fn address(&mut self, id: GIRExprId) -> SIRValueId {
        let held = self.gir.exprs[id].clone();
        let (ty, line, col) = (held.ty, held.line, held.col);
        let kind = match held.kind {
            GIRExprKind::Local(local) => SIRInstKind::Addr(self.b.slot_of[local]),
            GIRExprKind::Item(item) => SIRInstKind::ItemAddr(item),
            GIRExprKind::SelfExpr => SIRInstKind::SelfAddr,
            GIRExprKind::Field { base, index } => {
                let base = self.address(base);
                SIRInstKind::FieldAddr { base, index }
            }
            GIRExprKind::TupleIndex { base, index } => {
                let base = self.address(base);
                SIRInstKind::TupleAddr { base, index }
            }
            GIRExprKind::Index { base, index } => {
                let base = self.address(base);
                let index = self.value(index);
                SIRInstKind::IndexAddr { base, index }
            }
            // Not a place, so it has no address until it is given one. `&mk()`
            // is a reference to a value nothing named, and what it refers to is
            // a slot this pass makes to hold it -- which is what a temporary
            // is, spelled where the address is asked for rather than earlier.
            _ => {
                let value = self.value(id);
                let slot = self.slot(TIRBinding::Discard, ty, false);
                let to = self.address_of_slot(slot, line, col);
                self.effect(SIRInstKind::Store { to, value }, line, col);
                return to;
            }
        };
        self.push(kind, ty, line, col)
    }

    // ---- Building ---------------------------------------------------------

    fn new_block(&mut self, line: usize, col: usize) -> SIRBlockId {
        self.b.blocks.push(SIRBlock {
            phis:  Vec::new(),
            insts: Vec::new(),
            term:  SIRTerm::Unreachable,
            line,
            col,
        });
        self.b.blocks.len() - 1
    }

    fn switch_to(&mut self, block: SIRBlockId) {
        self.b.current = block;
    }

    // The first terminator written wins, as it does in `gir::lower` and for the
    // same reason: a second is this pass's bug rather than the program's, and
    // ignoring it keeps the block that a `return` already ended from being
    // rewritten by whatever was lowered after it.
    fn terminate(&mut self, term: SIRTerm) {
        let at = self.b.current;
        if self.b.blocks[at].term == SIRTerm::Unreachable {
            self.b.blocks[at].term = term;
        }
    }

    fn new_value(&mut self, ty: TyId, of: Option<GIRLocalId>, line: usize, col: usize)
        -> SIRValueId {
        self.b.values.push(SIRValue { ty, of, line, col });
        self.b.values.len() - 1
    }

    fn push(&mut self, kind: SIRInstKind, ty: TyId, line: usize, col: usize) -> SIRValueId {
        let def = self.new_value(ty, None, line, col);
        let at = self.b.current;
        let is_unsafe = self.b.unsafe_;
        self.b.blocks[at].insts.push(SIRInst { def: Some(def), kind, is_unsafe, line, col });
        def
    }

    fn effect(&mut self, kind: SIRInstKind, line: usize, col: usize) {
        let at = self.b.current;
        let is_unsafe = self.b.unsafe_;
        self.b.blocks[at].insts.push(SIRInst { def: None, kind, is_unsafe, line, col });
    }

    fn slot(&mut self, name: TIRBinding, ty: TyId, drops: bool) -> SIRSlotId {
        self.b.slots.push(SIRSlot { name, ty, of: None, drops, synthetic: true });
        self.b.slots.len() - 1
    }

    // The address of a slot, taken afresh each time it is wanted. One `Addr`
    // per use rather than one per slot: they are what `sir::promote` walks, and
    // a use it can see is a use it can take out, where a shared one would have
    // to be counted instead.
    fn address_of_slot(&mut self, slot: SIRSlotId, line: usize, col: usize) -> SIRValueId {
        let ty = self.b.slots[slot].ty;
        self.push(SIRInstKind::Addr(slot), ty, line, col)
    }
}

// What a compound assignment does before it writes. `Set` does nothing, which
// is the `None`; the rest are the binary operator that shares their spelling,
// and `&=`, `|=` and `^=` go with the single-character three and not with the
// logical ones -- "the compound assignments are one per binary operator that
// has a use for one", and `^^=` is not written (§5).
fn compound(op: TIRAssignOp) -> Option<TIRBinOp> {
    match op {
        TIRAssignOp::Set => None,
        TIRAssignOp::Add => Some(TIRBinOp::Add),
        TIRAssignOp::Sub => Some(TIRBinOp::Sub),
        TIRAssignOp::Mul => Some(TIRBinOp::Mul),
        TIRAssignOp::Div => Some(TIRBinOp::Div),
        TIRAssignOp::And => Some(TIRBinOp::BitAnd),
        TIRAssignOp::Or => Some(TIRBinOp::BitOr),
        TIRAssignOp::Xor => Some(TIRBinOp::BitXor),
        TIRAssignOp::Shl => Some(TIRBinOp::Shl),
        TIRAssignOp::Shr => Some(TIRBinOp::Shr),
    }
}

// A pattern's literal with its sign folded in. The minus is part of the
// pattern and not an operator applied to it -- there is nothing to apply one to
// -- so the constant a test compares against is the negative one.
fn negate(negated: bool, value: TIRLit) -> TIRLit {
    match (negated, value) {
        (true, TIRLit::Int(n)) => TIRLit::Int(-n),
        (true, TIRLit::Float(f)) => TIRLit::Float(-f),
        (_, value) => value,
    }
}

fn goes_to(term: &GIRTerm) -> Vec<GIRBlockId> {
    match term {
        GIRTerm::Goto(to) => vec![*to],
        GIRTerm::Branch { then, els, .. } => vec![*then, *els],
        GIRTerm::Match { arms, otherwise, .. } => {
            let mut out: Vec<GIRBlockId> = arms.iter().map(|a| a.block).collect();
            out.extend(otherwise.iter().copied());
            out
        }
        GIRTerm::ForEach { body, exit, .. } => vec![*body, *exit],
        GIRTerm::Return(_) | GIRTerm::Unreachable => Vec::new(),
    }
}

// A primitive's handle in the TTIR's arena. `sema` interns `bool` whether the
// program mentions one or not, so the one this pass leans on hardest is always
// there; the fallback is `gir::drops`' -- the first entry, which is wrong and
// is only reached in a program with no types at all, where nothing reads it.
fn prim(p: &TTIRProgram, want: TIRPrim) -> TyId {
    p.types.iter().position(|ty| *ty == Ty::Prim(want)).unwrap_or(0)
}

#[cfg(test)]
mod tests;
