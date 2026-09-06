// A body inside a body, and what it took with it.
//
// A closure's parameters are slots of its own body and its captures are not:
// a name it uses but did not declare is found in the body outside, and what is
// written down is how it was taken rather than what it resolved to. Which of
// the three ways it was taken -- read, written to, taken -- is worked out per
// name from what the body asks of it, and it is what tells `fn`, `var fn` and
// `once fn` apart.
//
// A method call is here for the same reason a closure is: both need a receiver
// found before anything else can be looked up, and both are the place where
// what is in scope stops being a list of names in this body.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::{Frame, Lowerer};

impl<'a> Lowerer<'a> {
    // A closure is a body inside a body. Its parameters are slots of its own,
    // and every name it uses but did not declare is taken from the frame it was
    // written in -- which is what `catch` does as each name is met.
    pub(super) fn closure(
        &mut self,
        is_move: bool,
        params: &[crate::tir::tir_nodes::TIRParam],
        body: TIRExprId,
        at: TIRExprId,
    ) -> TTIRExprId {
        // What it gives back is worked out from what its body comes to: a
        // closure writes no return type, there being nowhere to write one.
        let ret = self.types.fresh();
        self.frames.push(Frame::new(ret, is_move));

        let mut arg_tys = Vec::new();
        let mut slots = Vec::new();
        for p in params {
            let ty = match p.ty {
                Some(ty) => self.ty(ty),
                None => self.types.fresh(),
            };
            arg_tys.push(ty);
            let slot =
                self.bind(p.name.clone(), ty, crate::tir::tir_nodes::TIRIntro::Let, self.at(at));
            slots.push(slot);
        }

        let value = self.expr(body);
        let found = self.out.exprs[value].ty;
        if self.types.unify(found, ret).is_err() {
            let (found, ret) = (self.spell(found), self.spell(ret));
            self.errors.push(
                Diagnostic::error(
                    format!("this closure gives back `{}` and `{}` at once", found, ret),
                    self.at(at),
                )
                .with_label("it is worth one type"),
            );
        }

        // The frame comes off, and what it caught comes with it.
        let captures = self.frames.last().expect("a frame").captures.clone();
        // Where they will be found when it runs. A capture is a name of the
        // frame outside and the closure may outlive that frame, so what the
        // body reads is not the slot but an address handed to it -- one per
        // capture, in a run the caller builds and passes as a parameter
        // nobody wrote. `ptr ptr u8` is what that run is: a pointer to
        // addresses, each of which is an address and none of which the
        // language ever gives a type to.
        //
        // A closure that captured nothing takes none: there would be nothing
        // in it to point at, and the parameter would be one more thing every
        // caller had to pass to a fn value that may be a declared fn.
        let env = if captures.is_empty() {
            None
        } else {
            let byte = self.types.intern(Ty::Prim(crate::tir::tir_nodes::TIRPrim::U8));
            let one = self.types.intern(Ty::Ptr(byte));
            let run = self.types.intern(Ty::Ptr(one));
            Some(self.bind(
                TIRBinding::Name("$env".to_string()),
                run,
                crate::tir::tir_nodes::TIRIntro::Let,
                self.at(at),
            ))
        };
        // What calling it does to what it captured, which is the most any one
        // capture asks: "worked out per name, each taking the least the body
        // asks of it" (§5), and the closure is the most of those.
        //
        // A `move` capture is what takes: the closure owns the value, so a
        // second call would hand away what the first already did. A capture
        // the body assigns to is what writes. Everything else only reads, and
        // a closure that captured nothing reads nothing.
        let made = self.finish_body(value);
        let uses = captures
            .iter()
            .map(|c| match c.mode {
                // "By value is a copy where the name's type copies and a move
                // where it does not": a copy is the closure's own and calling
                // it changes nothing, and one that moved is only given away
                // where the body gives it away.
                TTIRCaptureMode::Value => {
                    let ty = self.out.bodies[made].locals[c.slot].ty;
                    if !self.copies(ty) && self.hands_away(made, c.slot) {
                        TIRFnUses::Takes
                    } else if self.writes_to(made, c.slot) {
                        // A `move` closure with a copy of its own that it
                        // writes to has state, and state is what one holder at
                        // a time is for.
                        TIRFnUses::Writes
                    } else {
                        TIRFnUses::Reads
                    }
                }
                TTIRCaptureMode::Ref(TIRRefOp::Mut) => TIRFnUses::Writes,
                TTIRCaptureMode::Ref(TIRRefOp::Imm) => TIRFnUses::Reads,
            })
            .max()
            .unwrap_or(TIRFnUses::Reads);
        let ty = self.types.intern(Ty::Fn { uses, params: arg_tys, ret, is_unsafe: false });
        self.make(TTIRExprKind::Closure { params: slots, captures, env, body: made }, ty, at)
    }

    // A call of a field, where the field turns out to be a method. `None` where
    // it is not one -- a field holding a fn is called like anything else, and
    // that is a `Call` of a `Field`.
    pub(super) fn method(
        &mut self,
        base: TIRExprId,
        name: &str,
        args: &[TIRExprId],
        at: TIRExprId,
    ) -> Option<TTIRExprId> {
        let recv = self.expr(base);
        let held = self.out.exprs[recv].ty;
        // A field of the same name wins: it is the nearer thing, and a struct
        // holding a fn is reached before an impl is looked in.
        if self.field_of(held, name).is_some() {
            return None;
        }
        let item = self.method_of(held, name)?;

        let made: Vec<TTIRExprId> = args.iter().map(|&a| self.expr(a)).collect();
        let TTIRItemKind::Fn(f) = &self.out.items[item].kind else { return None };
        let (fn_ty, takes_self) = (
            f.ty,
            matches!(f.params.first().map(|p| &p.name), Some(TIRBinding::SelfRecv(..))),
        );
        let Ty::Fn { params, ret, .. } = self.types.get(fn_ty).clone() else { return None };

        // The receiver is the first parameter, so what is left is what the call
        // was handed.
        let wanted: Vec<TyId> = if takes_self { params[1..].to_vec() } else { params.clone() };
        if wanted.len() != made.len() {
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` takes {} and was handed {}", name, wanted.len(), made.len()),
                    self.at(at),
                )
                .with_label("the wrong number of arguments"),
            );
        } else {
            for (i, (&want, &got)) in wanted.iter().zip(made.iter()).enumerate() {
                let found = self.out.exprs[got].ty;
                if self.types.unify(found, want).is_err() && !self.weakens(found, want) {
                    let (found, want) = (self.spell(found), self.spell(want));
                    self.errors.push(
                        Diagnostic::error(
                            format!("argument {} is `{}` and it takes `{}`", i + 1, found, want),
                            self.at(at),
                        )
                        .with_label("this is what it was handed"),
                    );
                }
                let at = self.at(at);
                self.stands_as(found, want, at);
            }
        }
        Some(self.make(TTIRExprKind::Method { recv, item, args: made }, ret, at))
    }

    // The method of that name written for that type. "an impl makes methods for
    // its type and holds nothing else" (§8), so this is every impl whose
    // subject is the type, and the member of it with that name.
    fn method_of(&mut self, ty: TyId, name: &str) -> Option<TTIRItemId> {
        // A reference stands for the place it refers to, so a method of the
        // referent is a method of the reference.
        let held = match self.types.get(ty).clone() {
            Ty::Ref { inner, .. } => inner,
            _ => ty,
        };
        let of = match self.types.get(held).clone() {
            Ty::Named { item, .. } => item,
            // A parameter of the declaration being walked. There is no impl to
            // find -- what the parameter will turn out to be is the caller's to
            // say -- so what answers is the trait a bound named, and the member
            // is the trait's. Which impl that becomes is settled where the
            // caller's type is known, in `mir::mono`.
            Ty::Param { index, .. } => return self.bound_method(index, name, ty),
            _ => return None,
        };
        for item in &self.out.items {
            let TTIRItemKind::Impl { ty: subject, members, .. } = &item.kind else { continue };
            let Ty::Named { item: written, .. } = self.types.get(*subject).clone() else {
                continue;
            };
            if written != of {
                continue;
            }
            for &member in members {
                if let TTIRItemKind::Fn(f) = &self.out.items[member].kind {
                    if f.name == name {
                        return Some(member);
                    }
                }
            }
        }
        None
    }

    // The method of that name among the traits this parameter is held to.
    //
    // Every bound is asked and not just the first, so that a parameter held to
    // two traits that each declare the name is a mistake said out loud rather
    // than one of them silently winning. There is no rule anywhere for choosing
    // between them, and the reader has a spelling for saying which they meant
    // once there is: none of this is reached for a concrete type.
    fn bound_method(&mut self, index: usize, name: &str, ty: TyId) -> Option<TTIRItemId> {
        let mut found: Vec<(TTIRItemId, String)> = Vec::new();
        for bound in self.param_bounds(index) {
            let TTIRBound::Trait(held) = bound else { continue };
            let Ty::Named { item, .. } = self.types.get(held).clone() else { continue };
            let TTIRItemKind::Trait { members, name: trait_name, .. } =
                self.out.items[item].kind.clone()
            else {
                continue;
            };
            for member in members {
                if let TTIRItemKind::Fn(f) = &self.out.items[member].kind {
                    if f.name == name {
                        found.push((member, trait_name.clone()));
                    }
                }
            }
        }
        match found.len() {
            0 => None,
            1 => Some(found[0].0),
            _ => {
                let names: Vec<String> =
                    found.iter().map(|(_, held)| format!("`{}`", held)).collect();
                let held = self.spell(ty);
                self.errors.push(
                    Diagnostic::error(
                        format!("`{}` has more than one `{}`", held, name),
                        self.here,
                    )
                    .with_label("which of them was meant is not said")
                    .with_note(format!("{} each declare one", names.join(" and "))),
                );
                None
            }
        }
    }
}
