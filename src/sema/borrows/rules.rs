// The refusals, and the words they are refused in.
//
// Everything above this file works out what is true; this is where a program
// is turned down for it. The two rules are the two the language spends its
// ownership story on -- a place that was moved out of may not be used again,
// and a place may be borrowed by one mutable reference or many immutable ones
// and never both -- and each of them is a handful of lines here because
// everything hard about them was decided before the call.
//
// What is not a handful of lines is the messages. A refusal that says only
// "this is moved" is a refusal the reader has to reconstruct, so each of these
// carries where the value went as well as where it was wanted, and each says
// which of the four things §2 names the use was doing. That is most of the
// length below and it is the part worth keeping.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::{TIRBinding, TIRRefOp, TIRSelf};
use crate::tir::ttir_nodes::{
    TTIRExprId, TTIRItemId, TTIRItemKind, TTIRLocalId, TTIRPatId, TTIRPatKind, TTIRStmt, Ty,
};

use super::place::{Place, Step};
use super::state::{Flow, Gone, Held, Use};
use super::Checker;

impl<'a> Checker<'a> {
    // A place being used, which is where a move is found out about.
    pub(super) fn reading(&mut self, place: &Place, how: Use, line: usize, col: usize) {
        let Some(state) = self.gone.of(place) else { return };
        let name = self.name(place);
        let (message, note) = if state.certain() {
            (format!("`{}` has been moved", name), "it was moved".to_string())
        } else {
            (
                format!("`{}` may have been moved", name),
                "it is moved on one way here".to_string(),
            )
        };
        self.say(
            Diagnostic::error(message, Span::at(line, col))
                .with_label(how.word())
                .with_secondary(state.at(), note)
                .with_help("a value moves unless its type says `impl Copy`"),
        );
    }

    // A value handed over: an argument, a return, the right of an assignment, a
    // field of a literal being built. It goes unless its type copies, and the
    // place it came from is done with.
    pub(super) fn moving(&mut self, id: TTIRExprId) {
        let ty = self.p.exprs[id].ty;
        if self.copies.is_copy(ty, self.p, &self.generic) {
            return;
        }
        let Some(place) = self.place(id) else { return };
        let (line, col) = (self.p.exprs[id].line, self.p.exprs[id].col);

        // A value that moves has one owner at a time (§2), and neither of these
        // is this frame's to give away: what a reference refers to is owned
        // where it was borrowed from, and an element that went would leave the
        // array it was in with a hole in it.
        //
        // Neither is written down in the prose. Both follow from one owner at a
        // time, and a reader meets them early enough that saying nothing would
        // be worse than saying this.
        // A name the closure captured by reference is the enclosing frame's,
        // and handing it away from here would hand away what somebody else
        // still owns. §5 works the mode out from what the body asks -- reading
        // takes a `&` and assigning takes a `*` -- and taking the value is
        // more than either, with no mode for it short of `move`.
        if let Some(op) = self.caught.get(&place.root).copied() {
            if place.path.is_empty() || !place.path.contains(&Step::Deref) {
                let name = self.name(&place);
                self.say(
                    Diagnostic::error(
                        format!("`{}` cannot be moved out of a closure", name),
                        Span::at(line, col),
                    )
                    .with_label("this takes it")
                    .with_note(format!(
                        "the closure captured it by `{}`, which borrows it",
                        sigil(op)
                    ))
                    .with_help("a `move` closure takes what it captures, and may give it away"),
                );
                return;
            }
        }

        let out_of = if place.path.contains(&Step::Deref) {
            Some(("a reference", "`&` it instead, which borrows rather than takes"))
        } else if place.path.contains(&Step::Index) {
            Some(("an array", "an element that went would leave a hole where it was"))
        } else {
            None
        };
        if let Some((what, help)) = out_of {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(
                    format!("`{}` cannot be moved out of {}", name, what),
                    Span::at(line, col),
                )
                .with_label("this takes it")
                .with_help(help),
            );
            return;
        }

        self.gone.moved(place, line, col);
    }

    // Taking a reference. Two rules meet here: what `*` asks of its operand,
    // and how many of each may stand at once.
    pub(super) fn borrowing(
        &mut self,
        id: TTIRExprId,
        operand: TTIRExprId,
        op: TIRRefOp,
        line: usize,
        col: usize,
    ) -> Flow {
        if self.expr(operand, Use::Read).left() {
            return Flow::Left;
        }
        // A value with no home of its own: "`&x` asks less: any place at all,
        // and a value with no home of its own, which the compiler gives one".
        let Some(place) = self.place(operand) else { return Flow::Normal };

        // "`*x` asks that x be a place the writer may write to -- a `var`, or a
        // field or element reached from one" (§5). Mutability is the root
        // binding's and reaches through whatever is reached from it (§2), so
        // the root is what is asked.
        if op == TIRRefOp::Mut && !self.writable(&place) {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(
                    format!("`{}` may not be written to", name),
                    Span::at(line, col),
                )
                .with_label("this takes a `*`")
                .with_help("a `*` wants a `var`, or a field or an element of one"),
            );
        }

        // "A place is reached either through one `*` and nothing else, or
        // through any number of `&` and no `*` -- one mutable reference or many
        // immutable ones, and never both" (§3).
        let now = self.now;
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.until >= now
                    && held.place.conflicts(&place)
                    && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
            })
            .cloned()
        {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(format!("`{}` is borrowed already", name), Span::at(line, col))
                    .with_label(format!("this takes a `{}`", sigil(op)))
                    .with_secondary(
                        Span::at(other.line, other.col),
                        format!("a `{}` of it is held from", sigil(other.op)),
                    )
                    .with_help(
                        "a place is reached through one `*`, or through any number of `&`, and never both",
                    ),
            );
        }

        self.held.push(Held { place, op, line, col, until: usize::MAX, at: id });
        Flow::Normal
    }

    // Whether the writer may write to a place. The root binding's answer, since
    // "there is no marking a single field of a `let` writable, and none
    // weakening one of a `var` either" (§2) -- and a `*` reached through is
    // written through whatever the binding says.
    fn writable(&self, place: &Place) -> bool {
        let local = &self.p.bodies[self.body].locals[place.root];
        if matches!(local.intro, crate::tir::tir_nodes::TIRIntro::Var) {
            return true;
        }
        // A `let` of reference type never re-aims and still writes into what it
        // refers to, where the reference is a `*`: "what a `let` fixes is the
        // binding and not the referent" (§2).
        place.path.contains(&Step::Deref)
            && matches!(&self.p.types[local.ty], Ty::Ref { op: TIRRefOp::Mut, .. })
    }

    // How a method takes its receiver, where the item is one that has a body.
    pub(super) fn receiver(&self, item: TTIRItemId) -> Option<TIRSelf> {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return None };
        match f.params.first().map(|param| &param.name) {
            Some(TIRBinding::SelfRecv(mode, _)) => Some(*mode),
            _ => None,
        }
    }

    // ---- Control flow ----------------------------------------------------

    // A block, which is what a borrow's extent is measured in: everything taken
    // inside one is let go at the end of it.
    pub(super) fn block(&mut self, stmts: &[TTIRStmt], tail: Option<TTIRExprId>) -> Flow {
        self.marks.push(self.held.len());
        let mut flow = Flow::Normal;
        for stmt in stmts {
            match stmt {
                // A `let` is the exception: what its initialiser borrowed may
                // have reached the slot, so the borrow keeps the block's
                // extent rather than the statement's. Bluntly -- every borrow
                // taken while working the value out, whether it reached the
                // slot or not -- which is the conservative half and costs a
                // reachability walk to sharpen.
                TTIRStmt::Let { local, init, .. } => {
                    // How long the slot is good for: the block it stands in,
                    // which is however many blocks deep the walk is now.
                    let held = self.marks.len();
                    self.depth.insert(*local, held);
                    let taken = self.held.len();
                    if let Some(init) = init {
                        if self.expr(*init, Use::Pass).left() {
                            flow = Flow::Left;
                            break;
                        }
                        self.moving(*init);
                        // A slot that outlives what it is given is the same
                        // refusal as a return that does, one block in rather
                        // than all the way out.
                        let (line, col) =
                            (self.p.exprs[*init].line, self.p.exprs[*init].col);
                        self.outstays(
                            *init,
                            held,
                            "this puts a reference to it somewhere longer-lived",
                            Span::at(line, col),
                        );
                        // And where it points, so a reference handed through a
                        // name is followed to what it was taken from.
                        let roots = self.roots(*init);
                        if roots.is_empty() {
                            self.from.remove(local);
                        } else {
                            self.from.insert(*local, roots);
                        }
                    }
                    // A borrow that got as far as the slot keeps the slot's
                    // extent, which ends where the slot is last read. One that
                    // did not is a temporary and goes with the statement:
                    // "a local at the end of its block, a temporary at the end
                    // of its statement" (§2), and a `&` handed to something
                    // that gives back no reference is a temporary however it
                    // was written.
                    let until = self.last.get(local).copied().unwrap_or(usize::MAX);
                    let reaching = match init {
                        Some(init) => self.reaching(*init),
                        None => Vec::new(),
                    };
                    let now = self.now;
                    for held in &mut self.held[taken..] {
                        held.until = if reaching.contains(&held.at) { until } else { now };
                    }
                    // The slot is filled, whatever was in it before.
                    self.gone.filled(&Place::of(*local));
                }
                TTIRStmt::Expr { expr, .. } => {
                    // "a local at the end of its block, a temporary at the end
                    // of its statement" (§2). A reference taken in a statement
                    // and bound to nothing is a temporary, so it goes with the
                    // statement -- which is what lets `f(&p)` and `g(*p)` stand
                    // one after the other.
                    let mark = self.held.len();
                    let left = self.expr(*expr, Use::Read).left();
                    self.held.truncate(mark);
                    if left {
                        flow = Flow::Left;
                        break;
                    }
                }
                // A declaration written in a block is walked where it is
                // declared, by `check` over every item.
                TTIRStmt::Item(_) => {}
            }
        }
        if flow == Flow::Normal {
            if let Some(tail) = tail {
                flow = self.expr(tail, Use::Read);
            }
        }
        let mark = self.marks.pop().unwrap_or(0);
        self.held.truncate(mark);
        flow
    }

    // Two ways, and what is true after them is what is true of both.
    pub(super) fn conditional(
        &mut self,
        cond: TTIRExprId,
        then: TTIRExprId,
        els: Option<TTIRExprId>,
    ) -> Flow {
        if self.expr(cond, Use::Read).left() {
            return Flow::Left;
        }
        let before = self.gone.clone();
        let took = self.expr(then, Use::Read);
        let after_then = std::mem::replace(&mut self.gone, before);
        let other = match els {
            Some(els) => self.expr(els, Use::Read),
            None => Flow::Normal,
        };

        match (took.left(), other.left()) {
            // Neither came back, so nothing after this is reached.
            (true, true) => Flow::Left,
            // One left: what it did to the state left with it.
            (true, false) => Flow::Normal,
            (false, true) => {
                self.gone = after_then;
                Flow::Normal
            }
            (false, false) => {
                self.gone.join(&after_then);
                Flow::Normal
            }
        }
    }

    // Every arm, joined. A pattern binds slots of its own, and what it binds is
    // filled rather than moved from.
    pub(super) fn matching(&mut self, scrutinee: TTIRExprId, arms: &[crate::tir::ttir_nodes::TTIRArm]) -> Flow {
        if self.expr(scrutinee, Use::Read).left() {
            return Flow::Left;
        }
        let before = self.gone.clone();
        let mut joined: Option<Gone> = None;
        let mut all_left = !arms.is_empty();

        let from_of = self.roots(scrutinee);
        for arm in arms {
            self.gone = before.clone();
            self.from_of = from_of.clone();
            for &pat in &arm.pats {
                self.binds(pat);
            }
            self.from_of.clear();
            if !self.expr(arm.body, Use::Read).left() {
                all_left = false;
                let reached = self.gone.clone();
                joined = Some(match joined {
                    None => reached,
                    Some(mut held) => {
                        held.join(&reached);
                        held
                    }
                });
            }
        }

        if all_left {
            return Flow::Left;
        }
        self.gone = joined.unwrap_or(before);
        Flow::Normal
    }

    // The slots a pattern binds. Each is filled by the match, so anything that
    // had gone from one is whole again.
    fn binds(&mut self, pat: TTIRPatId) {
        match &self.p.pats[pat].kind {
            TTIRPatKind::Bind(local) => {
                let place = Place::of(*local);
                // A name a pattern binds stands in the arm and nowhere else, so
                // it is one block shorter-lived than where the `match` is.
                self.depth.insert(*local, self.marks.len() + 1);
                // And it came out of what was matched on, so it points wherever
                // that did. Not *at* it: a name bound out of a value is the
                // value's own, and `match opt { Some(v) => v }` gives back what
                // `opt` held rather than a reference into `opt`.
                let (local, from) = (*local, self.from_of.clone());
                if from.is_empty() {
                    self.from.remove(&local);
                } else {
                    self.from.insert(local, from);
                }
                self.gone.filled(&place);
            }
            TTIRPatKind::Variant { elems, .. } => {
                for &elem in elems.clone().iter() {
                    self.binds(elem);
                }
            }
            TTIRPatKind::Tuple(elems) => {
                for &elem in elems.clone().iter() {
                    self.binds(elem);
                }
            }
            TTIRPatKind::Struct { fields, .. } => {
                for field in fields.clone().iter().flatten() {
                    self.binds(*field);
                }
            }
            TTIRPatKind::Range { lo, hi, .. } => {
                let (lo, hi) = (*lo, *hi);
                self.binds(lo);
                self.binds(hi);
            }
            TTIRPatKind::Wildcard | TTIRPatKind::Const(_) | TTIRPatKind::Lit { .. } => {}
        }
    }

    // A loop, walked twice: what a body does to the state is what the next turn
    // round it starts from, so a move in the body is a move at the top of the
    // second turn. The first walk says nothing -- it is how the state is
    // settled, and reporting from it would report a body that never ran.
    pub(super) fn loop_over(
        &mut self,
        cond: Option<TTIRExprId>,
        each: Option<(TTIRLocalId, TTIRExprId)>,
        body: TTIRExprId,
    ) -> Flow {
        if let Some(cond) = cond {
            if self.expr(cond, Use::Read).left() {
                return Flow::Left;
            }
        }
        if let Some((local, iter)) = each {
            if self.expr(iter, Use::Pass).left() {
                return Flow::Left;
            }
            self.moving(iter);
            // The loop variable stands in the body and nowhere else, so it is
            // one block shorter-lived than where the `for` is.
            self.depth.insert(local, self.marks.len() + 1);
            // And it comes out of what is being gone through, so it points
            // wherever that did: `for v in &things` hands out references into
            // `things`, and `for v in things` hands out what `things` held.
            let from = self.roots(iter);
            if from.is_empty() {
                self.from.remove(&local);
            } else {
                self.from.insert(local, from);
            }
            self.gone.filled(&Place::of(local));
        }

        // Round once with nothing said, to find what the body leaves behind.
        let before = self.gone.clone();
        let was_quiet = std::mem::replace(&mut self.quiet, true);
        self.breaks.push(Vec::new());
        self.expr(body, Use::Read);
        self.breaks.pop();
        self.quiet = was_quiet;

        // And round again from the state the first turn reached, which is what
        // the second turn would really see.
        self.gone.join(&before);
        self.breaks.push(Vec::new());
        let flow = self.expr(body, Use::Read);
        let ways_out = self.breaks.pop().unwrap_or_default();

        // What is true after the loop is true of every way out of it, the body
        // running to the end among them -- unless nothing came back that way.
        if !flow.left() {
            self.gone.join(&before);
        } else {
            self.gone = before.clone();
        }
        for out in &ways_out {
            self.gone.join(out);
        }
        Flow::Normal
    }
}

pub(super) fn sigil(op: TIRRefOp) -> &'static str {
    match op {
        TIRRefOp::Imm => "&",
        TIRRefOp::Mut => "*",
    }
}
