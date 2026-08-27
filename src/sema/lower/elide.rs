// The regions a signature did not write.
//
//     Every reference in a signature with no lifetime of its own gets one, and
//     a reference in the return type gets the shortest-lived of the ones the
//     parameters brought in.                            (docs/prose.txt, §3)
//
// That is the elision rule, and this is all of it. A fresh region for every
// reference a parameter brought in; the return's references tied to every one
// of them, which is what "the shortest-lived" comes to when nothing says which
// is shorter; and a written `'a` sharpening it by naming one region in two
// places, after which only what was written stands.
//
// What comes out is `TTIRFn::outlives`, and holding a caller to it is
// `sema::borrows`. Nothing here refuses anything: a region is worked out at
// the declaration and checked at the call, which is where §3 spends its
// precision and why there is no solver in either place.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;
use super::resolve::names_of;
use super::resolve::lifetimes_of;

impl<'a> Lowerer<'a> {
    // Every region standing anywhere in these types.
    pub(super) fn regions_of(&self, tys: &[TyId]) -> Vec<RegionId> {
        let mut out = Vec::new();
        for &ty in tys {
            self.walk_regions(ty, &mut out);
        }
        out
    }

    fn walk_regions(&self, ty: TyId, out: &mut Vec<RegionId>) {
        match self.types.get(ty).clone() {
            Ty::Ref { life, inner, .. } => {
                if life != 0 && !out.contains(&life) {
                    out.push(life);
                }
                self.walk_regions(inner, out);
            }
            Ty::Named { args, regions, .. } => {
                for r in regions {
                    if r != 0 && !out.contains(&r) {
                        out.push(r);
                    }
                }
                for a in args {
                    self.walk_regions(a, out);
                }
            }
            Ty::Ptr(inner) | Ty::GC(inner) => self.walk_regions(inner, out),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.walk_regions(elem, out),
            Ty::Tuple(members) => {
                for m in members {
                    self.walk_regions(m, out);
                }
            }
            Ty::Fn { params, ret, .. } => {
                for p in params {
                    self.walk_regions(p, out);
                }
                self.walk_regions(ret, out);
            }
            _ => {}
        }
    }

    // What `self` is. An impl names the type it is written for, and that is the
    // whole of what a receiver's type comes from.
    //
    // A trait's is another matter: the type is whatever answers the trait, and
    // `Ty` has no way to say "the one this is about". It is a parameter in all
    // but name -- what it stands for is settled by whoever answers the trait,
    // exactly as a `T` is settled by whoever calls -- so it is written as one,
    // named `Self` and placed after the method's own. A `Ty::SelfTy` would say
    // it more plainly and is what to add if this starts costing anything.
    pub(super) fn receiver_ty(&mut self, name: &TIRBinding, at: Span) -> TyId {
        let TIRBinding::SelfRecv(how, life) = name else { return self.types.fresh() };
        let subject = match self.subject {
            Some(subject) => subject,
            None => {
                let index = self.params.len();
                self.types.intern(Ty::Param { name: "Self".to_string(), index })
            }
        };
        let op = match how {
            // "A bare `self` takes the value whole and so moves it." Nothing is
            // taken, so there is no region to give it.
            crate::tir::tir_nodes::TIRSelf::Value => return subject,
            crate::tir::tir_nodes::TIRSelf::Ref => TIRRefOp::Imm,
            crate::tir::tir_nodes::TIRSelf::Mut => TIRRefOp::Mut,
        };
        // A receiver is a reference in a signature like any other, so it gets a
        // region like any other -- and `&'a self` names one, which is the whole
        // point of letting it be written.
        let life = match life {
            Some(name) => {
                let name = name.clone();
                self.life(&name, at)
            }
            None => self.region(),
        };
        self.types.intern(Ty::Ref { op, life, inner: subject })
    }

    // The parameters a declaration was written with, and what each is held to.
    // A `where` predicate about one of them is folded into that one's bounds:
    // "`fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing", and this
    // tree is what a declaration is rather than how it was written.
    pub(super) fn generics(&mut self, held: &[TIRGeneric], wheres: &[TIRWherePred]) -> Vec<TTIRGeneric> {
        let names = names_of(held);
        let mut made: Vec<TTIRGeneric> = held
            .iter()
            .map(|g| match g {
                TIRGeneric::Type { name, bounds } => TTIRGeneric::Type {
                    name:   name.clone(),
                    bounds: self.bounds(bounds),
                },
                TIRGeneric::Life { name, bounds } => TTIRGeneric::Life {
                    name:   name.clone(),
                    region: self.lifetimes.get(name).copied().unwrap_or(0),
                    // "Regions only -- a lifetime implements nothing": a `'a: T`
                    // is written the same way and is dropped here rather than
                    // refused, the rule about it being section 3's and not this
                    // list's shape.
                    bounds: bounds
                        .iter()
                        .filter_map(|b| match b {
                            TIRBound::Life(name) => Some(name.clone()),
                            TIRBound::Trait(_) => None,
                        })
                        .collect::<Vec<String>>()
                        .into_iter()
                        .map(|name| {
                            let at = self.here;
                            self.life(&name, at)
                        })
                        .collect(),
                },
            })
            .collect();

        for pred in wheres {
            let TIRBound::Trait(ty) = &pred.subject else { continue };
            let TIRTypeKind::Named { path, .. } = &self.tir.types[*ty].kind else { continue };
            if path.len() != 1 {
                continue;
            }
            let Some(index) = names.iter().position(|n| *n == path[0]) else { continue };
            let held = self.bounds(&pred.bounds);
            if let TTIRGeneric::Type { bounds, .. } = &mut made[index] {
                bounds.extend(held);
            }
        }
        made
    }

    // A region of its own. Numbered from 1: a reference outside a signature
    // gets region 0, how long it is good for being nobody's question yet.
    // The region a written `'a` names. There is no such thing as a lifetime
    // that names no region: one nothing declares is refused where it stands,
    // and a fresh region stands in its place so that one mistake is one message.
    pub(super) fn life(&mut self, name: &str, at: Span) -> RegionId {
        if let Some(held) = self.lifetimes.get(name).copied() {
            return held;
        }
        self.errors.push(
            Diagnostic::error(format!("no lifetime is called `'{}`", name), at)
                .with_label("nothing declares it")
                .with_help("a lifetime is declared among the parameters, `<'a>`"),
        );
        // Fresh even outside a signature, where `region` hands out 0: two
        // undeclared lifetimes are not thereby one.
        self.regions += 1;
        self.regions
    }

    // The regions a named type is handed, one per lifetime its declaration
    // takes. A written `'a` names a region the declaration declared; where none
    // was written, "every reference in a signature with no lifetime of its own
    // gets one" (§3) reaches here too, and a fresh one is made -- so a `Held`
    // and a `Held<'a>` carry the same promise and only one of them says which.
    // How many regions each declaration ends up with: one per lifetime it
    // declares, and one more per reference in it that named none -- "every
    // reference in a signature with no lifetime of its own gets one" (§3),
    // which a declaration carrying references answers to as much as a
    // signature does. Numbered in that order, which is the order
    // `open_regions` and the field walk hand them out in.
    //
    // Worked out once every name is known, since a declaration may name one
    // written below it.
    pub(super) fn count_regions(&mut self) {
        for made in 0..self.out.items.len() {
            let takes = self.takes_of(made, &mut Vec::new());
            if self.lifes.len() <= made {
                self.lifes.resize(made + 1, 0);
            }
            self.lifes[made] = takes;
        }
    }

    fn takes_of(&self, made: TTIRItemId, seen: &mut Vec<TTIRItemId>) -> usize {
        // A declaration reached from itself has no finite count -- each turn
        // round adds the last one's -- and there is nothing to give but 0.
        // `holds_ref` still sees the reference, so what comes of such a type is
        // held to every parameter, which is the answer that is never wrong.
        if seen.contains(&made) {
            return 0;
        }
        let Some(&Some(id)) = self.from_item.get(made) else { return 0 };
        seen.push(made);
        let takes = match &self.tir.items[id].kind {
            TIRItemKind::Struct { generics, fields, .. } => {
                lifetimes_of(generics)
                    + fields.iter().map(|f| self.elided_in(f.ty, seen)).sum::<usize>()
            }
            TIRItemKind::Enum { generics, variants, .. } => {
                lifetimes_of(generics)
                    + variants
                        .iter()
                        .map(|v| match &v.payload {
                            // A discriminant is a constant and holds no type,
                            // so it carries no reference either.
                            TIRPayload::None | TIRPayload::Discriminant(_) => 0,
                            TIRPayload::Tuple(tys) => {
                                tys.iter().map(|&t| self.elided_in(t, seen)).sum()
                            }
                            TIRPayload::Named(fields) => {
                                fields.iter().map(|f| self.elided_in(f.ty, seen)).sum()
                            }
                        })
                        .sum::<usize>()
            }
            TIRItemKind::TypeAlias { generics, ty, .. } => {
                lifetimes_of(generics) + self.elided_in(*ty, seen)
            }
            _ => 0,
        };
        seen.pop();
        takes
    }

    // References in a written type that named no lifetime, and the regions of
    // any declaration it names and hands no lifetime to -- a `struct Outer {
    // inner: Inner }` carries whatever `Inner` does, since the regions its
    // fields stand in have to come from somewhere.
    fn elided_in(&self, ty: TIRTypeId, seen: &mut Vec<TTIRItemId>) -> usize {
        match &self.tir.types[ty].kind {
            TIRTypeKind::Ref { life, inner, .. } => {
                usize::from(life.is_none()) + self.elided_in(*inner, seen)
            }
            TIRTypeKind::Ptr(inner) => self.elided_in(*inner, seen),
            TIRTypeKind::Array { elem, .. } | TIRTypeKind::Run(elem) => {
                self.elided_in(*elem, seen)
            }
            TIRTypeKind::Tuple(members) => {
                members.iter().map(|&m| self.elided_in(m, seen)).sum()
            }
            TIRTypeKind::Fn { params, ret, .. } => {
                params.iter().map(|&p| self.elided_in(p, seen)).sum::<usize>()
                    + ret.map(|r| self.elided_in(r, seen)).unwrap_or(0)
            }
            TIRTypeKind::Named { path, args } => {
                let written = args.iter().filter(|a| matches!(a, TIRGenericArg::Life(_))).count();
                let inner: usize = args
                    .iter()
                    .map(|a| match a {
                        TIRGenericArg::Type(ty) => self.elided_in(*ty, seen),
                        TIRGenericArg::Life(_) => 0,
                    })
                    .sum();
                let named = match self.names.get(&path.join("::")).copied() {
                    Some(item) => self.takes_of(item, seen).saturating_sub(written),
                    None => 0,
                };
                inner + named
            }
            _ => 0,
        }
    }

    pub(super) fn named_regions(&mut self, item: TTIRItemId, written: &[String], at: Span) -> Vec<RegionId> {
        let takes = self.lifes.get(item).copied().unwrap_or(0);
        let mut out = Vec::with_capacity(takes.max(written.len()));
        for name in written {
            let name = name.clone();
            out.push(self.life(&name, at));
        }
        while out.len() < takes {
            out.push(self.region());
        }
        out
    }

    pub(super) fn region(&mut self) -> RegionId {
        if !self.in_sig {
            return 0;
        }
        self.regions += 1;
        self.regions
    }

    // The regions a declaration begins with: one for each lifetime it declared,
    // so a `'a` written in two places is one region twice.
    pub(super) fn open_regions(&mut self, generics: &[TIRGeneric]) {
        self.regions = 0;
        self.lifetimes.clear();
        self.in_sig = true;
        for g in generics {
            if let TIRGeneric::Life { name, .. } = g {
                let held = self.region();
                self.lifetimes.insert(name.clone(), held);
            }
        }
    }

    // The signature is behind us. A `'a` written in the body still names the
    // region the declaration declared -- the numbering `open_regions` hands out
    // is by order of declaration, so it is the same region both times -- but a
    // reference written with no lifetime of its own gets region 0 from here on.
    pub(super) fn close_regions(&mut self) {
        self.in_sig = false;
    }
}
