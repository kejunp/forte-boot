// The walk itself: every expression, in the order it was written.
//
// It walks the TTIR and not the GIR, and the header of `borrows.rs` says why:
// the language is structured, so a walk that joins at an `if` and settles a
// loop by going round it twice reaches what a dataflow over a graph would --
// and the graph has already thrown away what this needs, which is the blocks a
// borrow's extent is measured in and the line every refusal has to point at.
//
// Two things make it a walk rather than a tree-print. It carries `Gone` and
// joins it where paths meet, so what one arm of an `if` moved is `Maybe` below
// it rather than moved or not. And it goes round a loop twice with `quiet` on
// for the first turn, because what stands above a use runs below it on the
// next turn -- one pass over a loop would say nothing about the second turn
// and two passes would say everything twice.
//
// What each expression *does* is the other half, and it is `Use`: reading a
// place, passing it, returning it, assigning through it. The rules in
// `rules.rs` are what those four turn into.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::{TIRRefOp, TIRSelf, TIRUnaryOp};
use crate::tir::ttir_nodes::{
    TTIRBodyId, TTIRCapture, TTIRCaptureMode, TTIRExprId, TTIRExprKind, TTIRGeneric, TTIRLocalId,
};

use super::rules::sigil;
use super::regions::Handed;
use super::place::Place;
use super::state::{Flow, Gone, Held, Use};
use super::Checker;

impl<'a> Checker<'a> {
    fn walk_body(&mut self, body: TTIRBodyId, generic: Vec<TTIRGeneric>) {
        self.walk_body_of(body, generic, &[], &[]);
    }

    // `args` is the slots the parameters were put in. They came from outside,
    // so they outlive everything the body declares, which is depth 0.
    pub(super) fn walk_body_of(
        &mut self,
        body: TTIRBodyId,
        generic: Vec<TTIRGeneric>,
        args: &[TTIRLocalId],
        caught: &[TTIRLocalId],
    ) {
        self.body = body;
        self.generic = generic;
        self.measure(body);
        self.depth.clear();
        self.from.clear();
        self.said_of.clear();
        for &slot in args {
            self.depth.insert(slot, 0);
        }
        // A captured name came from outside and goes on living there -- by
        // reference it is the enclosing frame's, and by value it is the
        // closure's, and either way it outlives the body's own blocks.
        for &slot in caught {
            self.depth.insert(slot, 0);
        }
        self.gone = Gone::default();
        self.held.clear();
        self.marks.clear();
        self.breaks.clear();
        let value = self.p.bodies[body].value;
        self.expr(value, Use::Read);
        // The tail. A `return` is checked where it stands, since what follows
        // it is not walked; what a body falls off the end of is checked here,
        // and a closure's body falls off the end of itself as much as a fn's.
        let (line, col) = (self.p.exprs[value].line, self.p.exprs[value].col);
        self.escaping(value, line, col);
    }

    // ---- Escapes ---------------------------------------------------------
    //
    //     Every reference in a signature with no lifetime of its own gets one,
    //     and a reference in the return type gets the shortest-lived of the
    //     ones the parameters brought in.                (docs/prose.txt, §3)
    //
    // A signature's regions are all brought in from outside, so a reference
    // rooted at a local of this body stands in none of them -- it is good until
    // the end of the block that declared it and the signature promises longer.
    // That is the whole of the check, and it needs no second frame: the caller
    // side of `outlives` is a different pass.

    // One expression, and what using it does. `how` is what the *place* this
    // expression names is being used for, where it names one.
    pub(super) fn expr(&mut self, id: TTIRExprId, how: Use) -> Flow {
        let (line, col) = (self.p.exprs[id].line, self.p.exprs[id].col);
        self.now = self.when.get(&id).copied().unwrap_or(self.now);
        match self.p.exprs[id].kind.clone() {
            TTIRExprKind::Literal(_) | TTIRExprKind::Item(_) | TTIRExprKind::SelfExpr => {
                Flow::Normal
            }

            // A name, and every way of reaching into one. Reading it is what
            // asks whether it is still there.
            TTIRExprKind::Local(_)
            | TTIRExprKind::Field { .. }
            | TTIRExprKind::TupleIndex { .. } => {
                if let Some(place) = self.place(id) {
                    self.reading(&place, how, line, col);
                }
                Flow::Normal
            }
            TTIRExprKind::Index { base, index } => {
                if self.expr(index, Use::Read).left() {
                    return Flow::Left;
                }
                let _ = base;
                if let Some(place) = self.place(id) {
                    self.reading(&place, how, line, col);
                }
                Flow::Normal
            }

            // Taking a reference, and the one that is not one: "`addr x` is the
            // third of them and the odd one: what it gives back is a `ptr` and
            // not a reference, so none of the above is asked of it and none of
            // it is promised" (§5).
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(op), operand } => {
                self.borrowing(id, operand, op, line, col)
            }
            TTIRExprKind::Unary { op: TIRUnaryOp::Addr, operand } => {
                self.expr(operand, Use::Read)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => {
                self.expr(operand, Use::Read)
            }

            TTIRExprKind::Binary { lhs, rhs, .. } => {
                if self.expr(lhs, Use::Read).left() {
                    return Flow::Left;
                }
                self.expr(rhs, Use::Read)
            }

            // "the right of an assignment" is one of the four places a value is
            // handed over (§2), and the left is a place being filled.
            TTIRExprKind::Assign { op, place, value } => {
                if self.expr(value, Use::Pass).left() {
                    return Flow::Left;
                }
                self.moving(value);
                // A compound assignment reads the place before it writes it.
                if op != crate::tir::tir_nodes::TIRAssignOp::Set {
                    if let Some(held) = self.place(place) {
                        self.reading(&held, Use::Assign, line, col);
                    }
                }
                if let Some(held) = self.place(place) {
                    // What the place is good for is what its root is good for,
                    // and it may not be given something shorter-lived. This is
                    // the refusal §3 promises lands "at the call rather than at
                    // the declaration", in the shape it takes when nothing is
                    // being returned: `r = pick(&outer, &inner)` where `r`
                    // outlives the block `inner` was declared in.
                    let lives = self.lives(held.root);
                    let (at_line, at_col) =
                        (self.p.exprs[value].line, self.p.exprs[value].col);
                    self.outstays(
                        value,
                        lives,
                        "this puts a reference to it somewhere longer-lived",
                        Span::at(at_line, at_col),
                    );
                    self.gone.filled(&held);
                }
                Flow::Normal
            }

            // Every argument is a place a value is handed over.
            TTIRExprKind::Call { callee, args } => {
                if self.expr(callee, Use::Read).left() {
                    return Flow::Left;
                }
                // "one call and no more": calling a `once fn` hands away what
                // it captured, so the call takes the closure. A second one is
                // then a use of something that has gone, and the message for
                // that is the one every other move already has.
                self.moving(callee);
                let flow = self.handing(&args);
                // After the arguments, so that what each was handed is known.
                if let Some(item) = self.callee(callee) {
                    let given: Vec<_> = args.iter().map(|&a| Handed::Written(a)).collect();
                    self.bounds_at_call(item, &given, Span::at(line, col));
                }
                flow
            }

            // A method holds a borrow of its receiver for the length of the
            // call, or moves it: "A `*self` receiver holds a mutable reference
            // to the whole value for the length of the call, so nothing reads
            // that value while the method runs" (§3).
            TTIRExprKind::Method { recv, item, args } => {
                let mode = self.receiver(item);
                // The receiver stands where parameter 0 does, so the two go
                // into one list before anything is asked of them -- and it is
                // borrowed rather than handed over, which is a different
                // question about how long it is good for.
                let first = match mode {
                    Some(TIRSelf::Ref) | Some(TIRSelf::Mut) => {
                        Handed::Whole(self.handed_borrowed(recv))
                    }
                    _ => Handed::Written(recv),
                };
                let given: Vec<_> = std::iter::once(first)
                    .chain(args.iter().map(|&a| Handed::Written(a)))
                    .collect();
                let flow = match mode {
                    Some(TIRSelf::Value) => {
                        if self.expr(recv, Use::Pass).left() {
                            return Flow::Left;
                        }
                        self.moving(recv);
                        self.handing(&args)
                    }
                    Some(TIRSelf::Ref) | Some(TIRSelf::Mut) => {
                        let op = if matches!(mode, Some(TIRSelf::Mut)) {
                            TIRRefOp::Mut
                        } else {
                            TIRRefOp::Imm
                        };
                        let mark = self.held.len();
                        if self.borrowing(id, recv, op, line, col).left() {
                            return Flow::Left;
                        }
                        let out = self.handing(&args);
                        // The call is over, and so is what it held.
                        self.held.truncate(mark);
                        out
                    }
                    None => {
                        if self.expr(recv, Use::Read).left() {
                            return Flow::Left;
                        }
                        self.handing(&args)
                    }
                };
                self.bounds_at_call(item, &given, Span::at(line, col));
                flow
            }

            // "a field of a literal being built" (§2).
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => self.handing(&fields),
            TTIRExprKind::Map { entries, .. } => {
                let flat: Vec<TTIRExprId> =
                    entries.iter().flat_map(|&(k, v)| [k, v]).collect();
                self.handing(&flat)
            }

            TTIRExprKind::Range { start, end, .. } => {
                for held in start.iter().chain(end.iter()) {
                    if self.expr(*held, Use::Read).left() {
                        return Flow::Left;
                    }
                }
                Flow::Normal
            }

            // What it captured, and then its body. The captures are taken in
            // the frame the closure was written in -- they are names of *that*
            // body -- and the body is walked on its own afterwards.
            TTIRExprKind::Closure { captures, body } => {
                for held in &captures {
                    let place = Place::of(held.outer);
                    match held.mode {
                        // "Reading one takes a `&` of it and assigning to one
                        // takes a `*`" (§5), and the reference is held for as
                        // long as the closure is.
                        TTIRCaptureMode::Ref(op) => {
                            self.captured(id, &place, op, held.line, held.col);
                        }
                        // "By value is a copy where the name's type copies and
                        // a move where it does not" -- the same rule every
                        // other handing-over follows.
                        TTIRCaptureMode::Value => {
                            let ty = self.p.bodies[self.body].locals[held.outer].ty;
                            if !self.copies.is_copy(ty, self.p, &self.generic) {
                                self.gone.moved(place, held.line, held.col);
                            }
                        }
                    }
                }
                self.closure(&captures, body)
            }

            TTIRExprKind::Block { stmts, tail } => self.block(&stmts, tail),
            TTIRExprKind::If { cond, then, els } => self.conditional(cond, then, els),
            TTIRExprKind::While { cond, body } => self.loop_over(Some(cond), None, body),
            TTIRExprKind::For { local, iter, body } => {
                self.loop_over(None, Some((local, iter)), body)
            }
            TTIRExprKind::Match { scrutinee, arms } => self.matching(scrutinee, &arms),

            // The three that do not come back.
            TTIRExprKind::Return(value) => {
                if let Some(value) = value {
                    if self.expr(value, Use::Return).left() {
                        return Flow::Left;
                    }
                    self.moving(value);
                    self.escaping(value, line, col);
                }
                Flow::Left
            }
            TTIRExprKind::Break(value) => {
                if let Some(value) = value {
                    if self.expr(value, Use::Pass).left() {
                        return Flow::Left;
                    }
                    self.moving(value);
                }
                // What is gone here is gone after the loop as well.
                if let Some(out) = self.breaks.last_mut() {
                    out.push(self.gone.clone());
                }
                Flow::Left
            }
            TTIRExprKind::Continue => Flow::Left,
        }
    }

    // A closure's body, walked with nothing of the frame around it: its slots
    // are its own, the ones it captured among them, and a capture arrives whole
    // however the name outside it stood.
    fn closure(&mut self, captures: &[TTIRCapture], body: TTIRBodyId) -> Flow {
        // Everything keyed by a slot or an expression has to be put aside and
        // put back: "a `TTIRLocalId` is a slot of the body that holds it, not
        // of the program", so a closure's slot 0 and the enclosing frame's are
        // two different things with one number, and the same for an expression.
        let outer = self.body;
        let gone = std::mem::take(&mut self.gone);
        let held = std::mem::take(&mut self.held);
        let marks = std::mem::take(&mut self.marks);
        let breaks = std::mem::take(&mut self.breaks);
        let depth = std::mem::take(&mut self.depth);
        let from = std::mem::take(&mut self.from);
        let said_of = std::mem::take(&mut self.said_of);
        let when = std::mem::take(&mut self.when);
        let last = std::mem::take(&mut self.last);
        let now = self.now;
        // What the body gives back is the closure's result, and a reference in
        // it may point at what the closure captured -- which outlives the
        // closure -- but not at anything the body declared, which does not.
        let value = self.p.bodies[body].value;
        let gives = self.holds_any_ref(self.p.exprs[value].ty);
        let leaves = std::mem::replace(&mut self.leaves, gives);
        // "the one place a reference is taken without being written" (§5): a
        // slot holding one is a slot whose value is somebody else's.
        let borrowed = captures
            .iter()
            .filter_map(|c| match c.mode {
                TTIRCaptureMode::Ref(op) => Some((c.slot, op)),
                TTIRCaptureMode::Value => None,
            })
            .collect();
        let caught = std::mem::replace(&mut self.caught, borrowed);

        // A closure declares no parameters of its own, so the generics it is
        // checked under are the ones it was written inside.
        let generic = self.generic.clone();
        let slots: Vec<TTIRLocalId> = captures.iter().map(|c| c.slot).collect();
        self.walk_body_of(body, generic, &[], &slots);

        self.body = outer;
        self.gone = gone;
        self.held = held;
        self.marks = marks;
        self.breaks = breaks;
        self.depth = depth;
        self.from = from;
        self.said_of = said_of;
        self.when = when;
        self.last = last;
        self.now = now;
        self.leaves = leaves;
        self.caught = caught;
        Flow::Normal
    }

    // A reference nobody wrote. Held like any other, and reported like any
    // other -- what changes is only what the secondary says, a reader who did
    // not write a `&` needing to be told one is there.
    fn captured(
        &mut self,
        id: TTIRExprId,
        place: &Place,
        op: TIRRefOp,
        line: usize,
        col: usize,
    ) {
        let now = self.now;
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.until >= now
                    && held.place.conflicts(place)
                    && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
            })
            .cloned()
        {
            let name = self.name(place);
            self.say(
                Diagnostic::error(format!("`{}` is borrowed already", name), Span::at(line, col))
                    .with_label(format!("the closure captures it by `{}`", sigil(op)))
                    .with_secondary(
                        Span::at(other.line, other.col),
                        format!("a `{}` of it is held from", sigil(other.op)),
                    )
                    .with_help(
                        "a place is reached through one `*`, or through any number of `&`, and never both",
                    ),
            );
        }
        self.held.push(Held { place: place.clone(), op, line, col, until: usize::MAX, at: id });
    }

    // A run of things each of which is handed over: an argument list, the
    // fields of a literal. "all of them are one thing said in four places" (§2).
    fn handing(&mut self, args: &[TTIRExprId]) -> Flow {
        for &arg in args {
            if self.expr(arg, Use::Pass).left() {
                return Flow::Left;
            }
            self.moving(arg);
        }
        Flow::Normal
    }
}
