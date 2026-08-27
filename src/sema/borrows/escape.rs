// Where a value points, and whether it may go there.
//
// A reference is only good while what it refers to is, so the question every
// rule here asks is the same one: does this value reach a local of this body,
// and is it going somewhere that outlives that local. Giving it back out of
// the body is the sharpest case -- the caller outlives everything the body
// declared -- and putting it in a slot declared further out is the same
// question with a nearer answer.
//
// The ordering is the whole of what this pass has, and it is deliberately
// crude: how deeply nested the block that declared a slot is. A parameter is
// nought, a local of the body's own block is one, and a bigger number is a
// shorter life. "A local at the end of its block" (§2) is what that comes to,
// and nothing finer is needed because nothing finer is promised.
//
// A reference is followed through however many names it is handed through:
// `let r = &x` makes `r` point into `x`, and `let s = r` makes `s` point where
// `r` did. That is what `roots` walks, and it is why a refusal can point at
// the `&x` somebody wrote rather than at whatever is holding it by then.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::TIRUnaryOp;
use crate::tir::ttir_nodes::{
    TTIRCaptureMode, TTIRExprId, TTIRExprKind, TTIRLocalId,
};

use super::place::Place;
use super::Checker;

impl<'a> Checker<'a> {
    // The locals of *this* body that a value points into. Empty is the answer
    // for anything that came from outside, which is why a parameter has no
    // entry in `from` and a literal contributes nothing.
    // Each root paired with the expression that reached it, so a refusal points
    // at the `&x` the reader wrote and not at whatever holds it.
    pub(super) fn roots(&self, id: TTIRExprId) -> Vec<(TTIRLocalId, TTIRExprId)> {
        let mut out = Vec::new();
        self.walk_roots(id, &mut out);
        out
    }

    fn walk_roots(&self, id: TTIRExprId, out: &mut Vec<(TTIRLocalId, TTIRExprId)>) {
        let add = |root: TTIRLocalId, out: &mut Vec<(TTIRLocalId, TTIRExprId)>| {
            if !out.iter().any(|&(held, _)| held == root) {
                out.push((root, id));
            }
        };
        match &self.p.exprs[id].kind {
            // `&x` and `*x` both point at the place x names.
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), operand } => {
                if let Some(place) = self.place(*operand) {
                    add(place.root, out);
                }
            }
            // A name points where whatever was put in it pointed. A parameter
            // has no entry, which is the answer: it points outside.
            TTIRExprKind::Local(local) => {
                for &(root, took) in self.from.get(local).into_iter().flatten() {
                    if !out.iter().any(|&(held, _)| held == root) {
                        // The `&` that took it, however many names it has been
                        // handed through since -- which is the line to show.
                        out.push((root, took));
                    }
                }
            }
            // Reaching into a place does not change which place it is rooted
            // at, and a reference is reached through as the place it refers to.
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.walk_roots(*base, out),
            TTIRExprKind::Cast(inner) => self.walk_roots(*inner, out),
            // "a reference in the return type gets the shortest-lived of the
            // ones the parameters brought in" -- the callee's rule read from
            // this side. What its result may point into is what was handed to
            // the parameters its result is tied to, and no more: a `'a` written
            // in the signature is what shortens that list, and this is where
            // the caller gets the precision it paid for.
            TTIRExprKind::Call { callee, args } => {
                let ties = self.callee(*callee).map(|item| self.tied(item));
                match ties {
                    // A fn whose result gives back no reference. Nothing that
                    // was handed in can be reached through what comes out.
                    Some(None) => {}
                    Some(Some(ties)) => {
                        for (i, &arg) in args.iter().enumerate() {
                            if ties.contains(&i) {
                                self.walk_roots(arg, out);
                            }
                        }
                    }
                    // A callee this cannot read -- a closure, or a fn in a
                    // slot. Every argument, which is the answer that is never
                    // wrong.
                    None => {
                        for &arg in args {
                            self.walk_roots(arg, out);
                        }
                    }
                }
            }
            // The same, with the receiver standing where parameter 0 does.
            TTIRExprKind::Method { recv, item, args } => match self.tied(*item) {
                None => {}
                Some(ties) => {
                    if ties.contains(&0) {
                        self.walk_roots(*recv, out);
                    }
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&(i + 1)) {
                            self.walk_roots(arg, out);
                        }
                    }
                }
            },
            // "a closure that captures by reference cannot outlive what it
            // captured, and `move` is the only thing that lets one be
            // returned" (§8). A closure is the one value here whose type says
            // nothing about what is inside it, so the captures are asked
            // instead: what it took by reference it points at, and what it took
            // by value it points at only as far as that value did.
            TTIRExprKind::Closure { captures, .. } => {
                for held in captures {
                    match held.mode {
                        TTIRCaptureMode::Ref(_) => {
                            // The slot itself, since the closure holds a
                            // reference to it -- and wherever that slot points,
                            // since reading through the one reaches the other.
                            add(held.outer, out);
                            for &(root, _) in self.from.get(&held.outer).into_iter().flatten() {
                                add(root, out);
                            }
                        }
                        // "By value is a copy where the name's type copies and
                        // a move where it does not": the slot is not pointed at
                        // either way, and what the value points at goes with it.
                        TTIRCaptureMode::Value => {
                            for &(root, _) in self.from.get(&held.outer).into_iter().flatten() {
                                add(root, out);
                            }
                        }
                    }
                }
            }
            // What is built out of references points where they did, whatever
            // was built: a struct and a variant carry them in named places and
            // an array, a tuple, a map, a set and a range in unnamed ones, and
            // none of that changes where the references came from.
            TTIRExprKind::ArrayLit(parts)
            | TTIRExprKind::TupleLit(parts)
            | TTIRExprKind::StructLit { fields: parts, .. }
            | TTIRExprKind::VariantLit { fields: parts, .. }
            | TTIRExprKind::Set { elems: parts, .. } => {
                for &part in parts {
                    self.walk_roots(part, out);
                }
            }
            TTIRExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.walk_roots(key, out);
                    self.walk_roots(value, out);
                }
            }
            TTIRExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.walk_roots(*held, out);
                }
            }
            // Every way out of a block or a branch is a way the value can come.
            TTIRExprKind::Block { tail, .. } => {
                if let Some(tail) = tail {
                    self.walk_roots(*tail, out);
                }
            }
            TTIRExprKind::If { then, els, .. } => {
                self.walk_roots(*then, out);
                if let Some(els) = els {
                    self.walk_roots(*els, out);
                }
            }
            TTIRExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.walk_roots(arm.body, out);
                }
            }
            _ => {}
        }
    }

    // What a body gives back, held to what its signature promised.
    // How long a slot is good for. An unrecorded one is treated as coming from
    // outside: a binding this pass never walked past is not a thing to refuse a
    // program over.
    pub(super) fn lives(&self, root: TTIRLocalId) -> usize {
        self.depth.get(&root).copied().unwrap_or(0)
    }

    // A block is where a value stands, not what it is: what comes out of one is
    // its tail, and the tail is the line a refusal points at.
    fn leaving(&self, id: TTIRExprId) -> TTIRExprId {
        let mut held = id;
        while let TTIRExprKind::Block { tail: Some(tail), .. } = &self.p.exprs[held].kind {
            held = *tail;
        }
        held
    }

    // A value put somewhere that outlives it. `held` is how long the place that
    // takes it is good for -- 0 for what a signature gives back, since every
    // region of a signature was brought in from outside and outlives the body.
    pub(super) fn outstays(&mut self, value: TTIRExprId, held: usize, what: &str, at: Span) {
        let leaves = self.leaving(value);
        let at = if leaves == value {
            at
        } else {
            Span::at(self.p.exprs[leaves].line, self.p.exprs[leaves].col)
        };
        for (root, took) in self.roots(value) {
            if self.lives(root) <= held || self.said_of.contains(&root) {
                continue;
            }
            if !self.quiet {
                self.said_of.push(root);
            }
            let local = &self.p.bodies[self.body].locals[root];
            let name = self.name(&Place::of(root));
            let mut said =
                Diagnostic::error(format!("`{}` does not live long enough", name), at)
                    .with_label(what);
            // Where the `&` was written, when that is not the line already
            // shown: a reference handed through a name leaves in one place and
            // was taken in another.
            let took = Span::at(self.p.exprs[took].line, self.p.exprs[took].col);
            if (took.line, took.col) != (at.line, at.col) {
                said = said.with_secondary(took, "the reference was taken");
            }
            said = said.with_secondary(Span::at(local.line, local.col), "it was bound");
            self.say(if held == 0 {
                said.with_note("what a signature gives back is good for as long as what its parameters brought in, and this was not one of them")
                    .with_help("give back the value itself, or a reference to something the caller handed in")
            } else {
                said.with_note("a reference is good until the end of the block that holds what it refers to")
                    .with_help("move what it refers to out to where it has to last, or keep the reference where it was taken")
            });
        }
    }

    pub(super) fn escaping(&mut self, value: TTIRExprId, line: usize, col: usize) {
        if !self.leaves {
            return;
        }
        self.outstays(value, 0, "this gives back a reference to it", Span::at(line, col));
    }

    // ---- Places ----------------------------------------------------------
}
