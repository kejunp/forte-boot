// Moves and borrows: the two rules the language spends its ownership story on.
//
//     A place is reached either through one `*` and nothing else, or through
//     any number of `&` and no `*` -- one mutable reference or many immutable
//     ones, and never both.                              (docs/prose.txt, §3)
//
//     What `let b = a` does to a is move it. The value goes to the new name and
//     the old one is done with: reading a after that is refused where it is
//     written, and so is passing it, returning it or assigning through it.
//                                                        (docs/prose.txt, §2)
//
// Both are marked settled in the prose and both are handed to "the checker"
// without a pass being named. This is that pass.
//
// It walks the TTIR and not the GIR. The language is structured -- every branch
// and every loop is an expression and there is no goto -- so a walk that joins
// at an `if` and settles a loop by going round it twice reaches what a dataflow
// over a graph would reach. What the graph does not keep is what this needs:
// `gir::lower` flattens the blocks a borrow's extent is measured in, drops which
// locals were parameters, and binds a pattern's names on an edge rather than in
// a statement.
//
// A closure that hands away what it captured is a `once fn`, and calling one
// takes it: `is_copy` says a `once fn` moves, so the second call is a use of
// something that has gone and needs no rule here of its own. What tells the
// three fn types apart is `sema::lower`, from what each capture asks.
//
// A closure's body is walked like any other, with two things said about the
// names it did not declare: one captured by reference is somebody else's and
// may not be handed away from inside, and what the body gives back may point at
// a capture -- which outlives the closure -- but not at anything the body
// declared, which does not.
//
// A borrow lasts from where it is taken to the last place anything can reach
// through it, which is where the slot holding it is last read -- the rule Rust
// reached with NLL, and sharper than the block-long extent this used to have.
// Everything is numbered in the order it was written; a loop is the one place
// that is not enough, since what stands above a use runs below it on the next
// turn, and a slot last read inside one is held to all of it. Which borrows
// keep a slot's extent is the other half: a `&` that got as far as the value
// keeps it, and one that did not is a temporary and goes with the statement --
// `len(&x)` gives back an `i32` and can hold nothing, so the `&x` is over when
// the line is.
//
// Regions are checked too, and so are the bounds on them -- a `'a: 'b` and a
// `T: 'a` are promises a *caller* keeps, so they are held to at the call. The
// shape all of it takes here is worth saying:
//
//     What the rule costs is precision, and it spends it at the call rather
//     than at the declaration ... the program that cannot be proved is turned
//     down where it is used and not where the thing that could not be proved
//     was written.                                      (docs/prose.txt, §3)
//
// So there is no second frame and no constraint solver. A signature's
// `outlives` says which of its parameters its result is tied to; a body orders
// its own slots by how deeply nested the block that declared each one is; and
// the check is that a value never reaches a place that outlives it. What the
// return type asks for is the same question with the place being the caller,
// which outlives everything the body declares.
//
// What it does not do:
//
//   - Count the regions of a declaration reached from itself. `struct A { b:
//     &B }` beside `struct B { a: &A }` has no finite number of them, each
//     turn round adding the last one's, and 0 is what such a declaration is
//     given. `holds_ref` still sees the reference, so what comes of one is
//     held to every parameter -- the elision rule's own answer, and never
//     wrong.
//   - Where a `Drop` runs. Settled in §2 and placed by `gir::drops`, which is
//     where the graph is: "nothing at all where the value was moved away
//     first" is a question about a program point, and a graph is what answers
//     one. What this pass does with a move is refuse it, which wants the line
//     it was written on and so wants the tree.
//
// This file holds the `Checker` itself and the two things it does before any
// rule is asked: work out which types copy, and number every expression of a
// body so that a borrow's extent can be measured against the order it was
// written in. The rest is one file apiece, and the order below is roughly the
// order a reader wants them.
//
//   `place`    what a rule is about -- a root and a way in from it -- and how
//              an expression the source wrote turns into one.
//   `copies`   which types copy and which have something to release. The one
//              table here anything outside this pass reads.
//   `state`    what the walk carries: what is still in a place, which borrows
//              are in hand, and whether the path came back at all.
//   `walk`     every expression in the order it was written, joining at an
//              `if` and going round a loop twice.
//   `rules`    the two refusals, and the words they are refused in.
//   `holds`    what a type holds, as far as a reference is concerned.
//   `regions`  how long a thing is good for, checked at the call.
//   `escape`   where a value points, and whether it may go there.
//
// The `Checker` is one type spread over all of them, so its methods are
// `pub(super)` where a sibling calls them. Its fields are not: a private field
// is visible to the files below this one, which is exactly the reach it should
// have and the reason the struct stays here.

#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::tir::tir_nodes::TIRRefOp;
use crate::tir::ttir_nodes::{
    TTIRBodyId, TTIRExprId, TTIRExprKind, TTIRFn, TTIRGeneric,
    TTIRItemKind, TTIRLocalId, TTIRProgram, TTIRStmt,
};

mod copies;
mod escape;
mod holds;
mod place;
mod regions;
mod rules;
mod state;
mod walk;

#[cfg(test)]
mod tests;

use copies::name_of;
pub use copies::Copies;
use state::{Gone, Held};

pub struct Checker<'a> {
    p:       &'a TTIRProgram,
    copies:  Copies,
    errors:  Diagnostics,
    // The body being walked, and the declaration it belongs to: a `Ty::Param`
    // is answered by the second.
    body:    TTIRBodyId,
    generic: Vec<TTIRGeneric>,
    gone:    Gone,
    // Every borrow in hand, and where each block's own began -- popping to that
    // mark is what ends a borrow's extent.
    held:    Vec<Held>,
    marks:   Vec<usize>,
    // Where a `break` left from, so what follows the loop is the join of every
    // way out of it.
    breaks:  Vec<Vec<Gone>>,
    // Off while a loop is being settled, so going round it twice does not say
    // the same thing twice.
    quiet:   bool,
    // Whether what this body gives back holds a reference standing in a region
    // of the signature. If it does not, nothing it gives back can outstay
    // anything, and the escape check has nothing to ask.
    leaves:  bool,
    // How deeply nested the block that declared each slot is. A parameter is 0,
    // since it came from outside and outlives everything the body declares; a
    // local of the body's own block is 1, one inside a block inside that is 2,
    // and a bigger number is a shorter life. Comparing two of them is the whole
    // of the ordering this pass has, and it is the ordering the language has:
    // "a local at the end of its block" (§2) is what a block being nested in
    // another one comes to.
    depth:   HashMap<TTIRLocalId, usize>,
    // Which locals have already been refused for outstaying something. One
    // mistake is one message: a reference put in a slot that outlives it and
    // then given back out of the body is one thing gone wrong in two places,
    // and the first place is the one worth reading.
    said_of: Vec<TTIRLocalId>,
    // Where the value a pattern is being taken apart points. A pattern binds
    // names out of something, and this is that something's roots, held while
    // `binds` walks -- a pattern has no expression of its own to ask.
    from_of: Vec<(TTIRLocalId, TTIRExprId)>,
    // When each expression of this body stands, in the order they were
    // written, and the last moment each slot is read. Worked out before the
    // walk: a borrow's extent is a fact about the whole body and the walk is
    // where it is used, not where it is found out.
    when:    HashMap<TTIRExprId, usize>,
    last:    HashMap<TTIRLocalId, usize>,
    // Where the walk is now, so a borrow whose slot is done with can be told
    // from one still in hand.
    now:     usize,
    // The slots of *this* body that hold a name the closure it belongs to
    // captured by reference. Inside the body such a slot has the captured
    // type and not a reference type -- `catch` gives it the type it found --
    // so nothing about the slot itself says the value is somebody else's.
    caught:  HashMap<TTIRLocalId, TIRRefOp>,
    // What each slot's value points into, where it points into this body at
    // all. `let r = &x` makes r point into x, and `let s = r` makes s point
    // where r did -- so a reference is followed however many names it is
    // handed through.
    from:    HashMap<TTIRLocalId, Vec<(TTIRLocalId, TTIRExprId)>>,
}

impl<'a> Checker<'a> {
    pub fn new(p: &'a TTIRProgram) -> Checker<'a> {
        Checker {
            p,
            copies: Copies::of(p),
            errors: Diagnostics::new(),
            body: 0,
            generic: Vec::new(),
            gone: Gone::default(),
            held: Vec::new(),
            marks: Vec::new(),
            breaks: Vec::new(),
            quiet: false,
            leaves: false,
            depth: HashMap::new(),
            said_of: Vec::new(),
            from_of: Vec::new(),
            when: HashMap::new(),
            last: HashMap::new(),
            now: 0,
            caught: HashMap::new(),
            from: HashMap::new(),
        }
    }

    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    // Every fn of every module, and the two names the compiler knows.
    pub fn check(&mut self) -> &Diagnostics {
        for held in self.copies.both() {
            let item = &self.p.items[held];
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` is both `Copy` and `Drop`", name_of(held, self.p)),
                    Span::at(item.line, item.col),
                )
                .with_label("this is declared both")
                .with_help("a value that has something to release is a value there had better be one of"),
            );
        }

        for id in 0..self.p.items.len() {
            let TTIRItemKind::Fn(f) = &self.p.items[id].kind else { continue };
            if f.body.is_none() {
                continue;
            }
            self.walk_fn(&f.clone());
        }
        &self.errors
    }

    // One fn: its body, walked, and then what its body gives back.
    fn walk_fn(&mut self, f: &TTIRFn) {
        let Some(body) = f.body else { return };
        self.leaves = self.holds_ref(f.ret);
        let args: Vec<TTIRLocalId> = f.params.iter().filter_map(|p| p.slot).collect();
        self.walk_body_of(body, f.generics.clone(), &args, &[]);
    }

    // ---- How long a borrow is in hand ------------------------------------
    //
    // A borrow lasts from where it is taken to the last place anything can
    // reach through it, which is where the slot holding it is last read. That
    // is sharper than the end of the block and is the rule Rust reached with
    // NLL; the prose allows either, its own lifetime rule being "only ever
    // answered too conservatively", and the sharper one turns down less.
    //
    // Everything is numbered in the order it was written, so "later" is a
    // bigger number. A loop is the one place that is not enough: what is
    // written above a use runs below it on the next turn, so every slot last
    // read inside a loop is held to the loop's own end.

    fn measure(&mut self, body: TTIRBodyId) {
        self.when.clear();
        self.last.clear();
        let value = self.p.bodies[body].value;
        let mut clock = 0;
        self.number(value, &mut clock);
    }

    fn number(&mut self, id: TTIRExprId, clock: &mut usize) {
        *clock += 1;
        let at = *clock;
        self.when.insert(id, at);
        let inner = |held: &mut Self, kids: Vec<TTIRExprId>, clock: &mut usize| {
            for kid in kids {
                held.number(kid, clock);
            }
        };
        match self.p.exprs[id].kind.clone() {
            TTIRExprKind::Local(local) => {
                let held = self.last.entry(local).or_insert(at);
                *held = (*held).max(at);
            }
            TTIRExprKind::Literal(_) | TTIRExprKind::Item(_) | TTIRExprKind::SelfExpr => {}
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                inner(self, vec![base], clock)
            }
            TTIRExprKind::Index { base, index } => inner(self, vec![base, index], clock),
            TTIRExprKind::Call { callee, args } => {
                inner(self, std::iter::once(callee).chain(args).collect(), clock)
            }
            TTIRExprKind::Method { recv, args, .. } => {
                inner(self, std::iter::once(recv).chain(args).collect(), clock)
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => inner(self, fields, clock),
            TTIRExprKind::Map { entries, .. } => {
                inner(self, entries.iter().flat_map(|&(k, v)| [k, v]).collect(), clock)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => {
                inner(self, vec![operand], clock)
            }
            TTIRExprKind::Binary { lhs, rhs, .. } => inner(self, vec![lhs, rhs], clock),
            TTIRExprKind::Assign { place, value, .. } => inner(self, vec![value, place], clock),
            TTIRExprKind::Range { start, end, .. } => {
                inner(self, [start, end].into_iter().flatten().collect(), clock)
            }
            // A closure's body is a body of its own and is numbered with its
            // own fn. What belongs here is that it read every name it captured,
            // and it reads them for as long as the closure is in hand -- which
            // is the slot the closure went into, and that slot's last use is
            // what this numbering finds.
            TTIRExprKind::Closure { captures, .. } => {
                for held in captures {
                    let held = self.last.entry(held.outer).or_insert(at);
                    *held = (*held).max(at);
                }
            }
            TTIRExprKind::Block { stmts, tail } => {
                for stmt in &stmts {
                    match stmt {
                        TTIRStmt::Let { local, init, .. } => {
                            if let Some(init) = init {
                                self.number(*init, clock);
                            }
                            // Bound here and read nowhere: it still stands
                            // until something reads it, and nothing does.
                            self.last.entry(*local).or_insert(*clock);
                        }
                        TTIRStmt::Expr { expr, .. } => self.number(*expr, clock),
                        TTIRStmt::Item(_) => {}
                    }
                }
                if let Some(tail) = tail {
                    self.number(tail, clock);
                }
            }
            TTIRExprKind::If { cond, then, els } => {
                inner(self, [Some(cond), Some(then), els].into_iter().flatten().collect(), clock)
            }
            TTIRExprKind::Match { scrutinee, arms } => {
                self.number(scrutinee, clock);
                for arm in &arms {
                    self.number(arm.body, clock);
                }
            }
            // The two that come round again.
            TTIRExprKind::While { cond, body } => {
                let from = *clock;
                self.number(cond, clock);
                self.number(body, clock);
                self.round(from, *clock);
            }
            TTIRExprKind::For { local, iter, body } => {
                let from = *clock;
                self.number(iter, clock);
                self.number(body, clock);
                self.last.entry(local).or_insert(*clock);
                self.round(from, *clock);
            }
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                inner(self, value.into_iter().collect(), clock)
            }
            TTIRExprKind::Continue => {}
        }
    }

    // What is written above a use runs below it on the next turn, so a slot
    // last read anywhere inside a loop is in hand for all of it.
    fn round(&mut self, from: usize, to: usize) {
        for held in self.last.values_mut() {
            if *held > from && *held <= to {
                *held = to;
            }
        }
    }
}
