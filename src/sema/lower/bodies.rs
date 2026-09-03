// The third of the three passes: what each fn does.
//
// Every declaration is resolved by now, so a call can be looked up and a field
// can be found. What this adds is the inside: a slot for every local, a frame
// to hold what is in scope, and a type over every expression -- which is what
// makes the tree below this one the typed tree.
//
// The frame is the shape of the thing. A body is a stack of them, one per
// block, and a closure pushes one that remembers which body it came from, so
// that a name it did not declare can be found in the body outside and written
// down as a capture rather than resolved and forgotten.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::{Frame, Lowerer};

use super::resolve::type_names_of;

impl<'a> Lowerer<'a> {
    pub(super) fn bodies(&mut self, items: &[TIRItemId]) {
        for &id in items {
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    let Some(made) = self.made[self.at][id] else { continue };
                    let Some(value) = f.body else { continue };
                    self.here = self.span(id);
                    self.params = type_names_of(&f.generics);
                    self.open_regions(&f.generics);
                    self.close_regions();
                    let body = self.body(made, &f, value);
                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.body = Some(body);
                    self.params.clear();
                }
                TIRItemKind::Impl { generics, ty, for_ty, members, .. } => {
                    self.open_regions(&generics);
                    self.close_regions();
                    let subject = match for_ty {
                        Some(for_ty) => self.ty(for_ty),
                        None => self.ty(ty),
                    };
                    let held = self.subject.replace(subject);
                    self.bodies(&members);
                    self.subject = held;
                }
                TIRItemKind::Namespace { items, .. }
                | TIRItemKind::Trait { members: items, .. } => self.bodies(&items),
                _ => {}
            }
        }
    }

    // One fn's body: a slot for every parameter, then the expression, then the
    // two put together.
    fn body(&mut self, made: TTIRItemId, f: &TIRFn, value: TIRExprId) -> TTIRBodyId {
        self.frames.push(Frame::new(0, false));

        let (arg_tys, ret) = {
            let TTIRItemKind::Fn(held) = &self.out.items[made].kind else {
                return self.finish_body(0)
            };
            let Ty::Fn { params, ret, .. } = &self.types.get(held.ty).clone() else {
                return self.finish_body(0)
            };
            (params.clone(), *ret)
        };
        self.frames.last_mut().expect("a frame").ret = ret;

        // A parameter is a slot like any other, and the slot is what the body
        // names it by.
        let mut params = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            let ty = arg_tys.get(i).copied().unwrap_or_else(|| self.types.fresh());
            // A receiver binds under the word it was written with.
            let held = match p.name {
                TIRBinding::SelfRecv(..) => TIRBinding::Name("self".to_string()),
                _ => p.name.clone(),
            };
            let slot = self.bind(held, ty, crate::tir::tir_nodes::TIRIntro::Let, self.here);
            params.push(TTIRParam { name: p.name.clone(), slot: Some(slot) });
        }
        let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
            return self.finish_body(0)
        };
        held.params = params;

        let out = self.expr(value);
        // "a body that could fall off the end of a `never` is refused" is the
        // checker's; what is held here is that a body gives back what it said.
        let found = self.out.exprs[out].ty;
        if self.types.unify(found, ret).is_err() {
            let (found, ret) = (self.spell(found), self.spell(ret));
            self.errors.push(
                Diagnostic::error(
                    format!("this body gives back `{}` and the signature says `{}`", found, ret),
                    self.at(value),
                )
                .with_label("this is what it comes to"),
            );
        }
        let at = self.at(value);
        self.stands_as(found, ret, at);
        // Now that every hole in this body is as filled as it is going to
        // get, the parameters are held to what they were declared with.
        let held = std::mem::take(&mut self.pending);
        for (arg, bound, name, at) in held {
            self.holds(arg, &bound, &name, at);
        }
        self.finish_body(out)
    }

    pub(super) fn finish_body(&mut self, value: TTIRExprId) -> TTIRBodyId {
        let frame = self.frames.pop().expect("a frame");
        self.out.bodies.push(TTIRBody { locals: frame.locals, value });
        self.out.bodies.len() - 1
    }

    // `where` is where the name was bound. A slot is not an expression and had
    // none until the checker wanted one: "the value was moved here, and it was
    // bound there" is two places, and only one of them is a line anybody wrote
    // an expression on.
    pub(super) fn bind(
        &mut self,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
        where_: Span,
    ) -> TTIRLocalId {
        let at = self.frames.len() - 1;
        self.into_frame(at, name, ty, intro, where_)
    }

    fn into_frame(
        &mut self,
        at: usize,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
        where_: Span,
    ) -> TTIRLocalId {
        let frame = &mut self.frames[at];
        frame.locals.push(TTIRLocal {
            name: name.clone(),
            ty,
            intro,
            line: where_.line,
            col: where_.col,
        });
        let slot = frame.locals.len() - 1;
        if let TIRBinding::Name(name) = name {
            if let Some(scope) = frame.scopes.last_mut() {
                scope.insert(name, slot);
            }
        }
        slot
    }

    // The slot a name stands for, seen from the innermost body. A name of a
    // frame further out is captured on the way in -- once per frame it has to
    // cross, so a closure inside a closure takes it from the one that took it.
    pub(super) fn slot(&mut self, name: &str, used: Span) -> Option<TTIRLocalId> {
        let depth = self.frames.len();
        for at in (0..depth).rev() {
            let found = self.frames[at]
                .scopes
                .iter()
                .rev()
                .find_map(|scope| scope.get(name).copied());
            let Some(mut held) = found else { continue };
            for inner in at + 1..depth {
                held = self.catch(inner, held, name, used);
            }
            return Some(held);
        }
        None
    }

    // One name of the frame outside `at`, given a slot inside it. "A name the
    // body uses but did not declare is captured, and how is worked out per
    // name, each taking the least the body asks of it" -- so it starts at a
    // `&` and is sharpened to a `*` where the body assigns to it.
    fn catch(
        &mut self,
        at: usize,
        outer: TTIRLocalId,
        name: &str,
        used: Span,
    ) -> TTIRLocalId {
        if let Some(&held) = self.frames[at].caught.get(&outer) {
            return self.frames[at].captures[held].slot;
        }
        let held = &self.frames[at - 1].locals[outer];
        let (ty, intro) = (held.ty, held.intro);
        let where_ = Span::at(held.line, held.col);
        let slot = self.into_frame(at, TIRBinding::Name(name.to_string()), ty, intro, where_);
        let mode = if self.frames[at].is_move {
            TTIRCaptureMode::Value
        } else {
            TTIRCaptureMode::Ref(TIRRefOp::Imm)
        };
        let frame = &mut self.frames[at];
        // Where the body first named it, which is the line a refusal about
        // the borrow it takes has to point at.
        frame.captures.push(TTIRCapture { outer, slot, mode, line: used.line, col: used.col });
        let held = frame.captures.len() - 1;
        frame.caught.insert(outer, held);
        slot
    }

    // "assigning to one takes a `*`" -- the least the body asks of it, once it
    // turns out to ask that much. A `move` closure is already by value and
    // there is nothing to sharpen.
    pub(super) fn assigns_to(&mut self, slot: TTIRLocalId) {
        let Some(frame) = self.frames.last_mut() else { return };
        if frame.is_move {
            return;
        }
        if let Some(held) = frame.captures.iter_mut().find(|c| c.slot == slot) {
            held.mode = TTIRCaptureMode::Ref(TIRRefOp::Mut);
        }
    }

    pub(super) fn locals(&self) -> &[TTIRLocal] {
        &self.frames[self.frames.len() - 1].locals
    }

    pub(super) fn make(&mut self, kind: TTIRExprKind, ty: TyId, at: TIRExprId) -> TTIRExprId {
        let held = &self.tir.exprs[at];
        self.out.exprs.push(TTIRExpr { kind, ty, line: held.line, col: held.col });
        self.out.exprs.len() - 1
    }

    pub(super) fn spell(&self, ty: TyId) -> String {
        let items = &self.out.items;
        self.types.spell(ty, &|item| match &items[item].kind {
            TTIRItemKind::Struct { name, .. }
            | TTIRItemKind::Enum { name, .. }
            | TTIRItemKind::Trait { name, .. } => name.clone(),
            _ => "?".to_string(),
        })
    }

    // What this pass cannot work out yet. One message and an `Error`, which is
    // what keeps the rest of the body being checked.
    pub(super) fn not_yet(&mut self, what: &str, at: TIRExprId) -> TTIRExprId {
        self.errors.push(
            Diagnostic::error(format!("`sema` cannot type {} yet", what), self.at(at))
                .with_label("this is not worked out")
                .with_note("the tree below this holds an `Error` where its type would be"),
        );
        let ty = self.types.error();
        self.make(TTIRExprKind::Literal(TIRLit::Null), ty, at)
    }
}
