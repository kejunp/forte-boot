// The second of the three passes: the types each declaration wrote.
//
// By the time this runs every declaration exists, which is the whole reason it
// is a pass of its own -- a struct may name one declared below it, and a fn may
// take one declared in another file, so nothing can be resolved until every
// name is findable. What it settles is the outside of each declaration: a
// struct's fields, a fn's signature, a global's type, and the bounds either
// wrote. What is inside a fn is `bodies`, one pass later still.
//
// `ty` is the piece the rest of the compiler leans on hardest. A type in the
// TIR is how it was spelled; a `TyId` is what it is, and the two are not the
// same thing -- `Vec<T>` written twice is one type here, and a name that
// resolves to nothing is `Ty::Error` rather than a refusal, so that one
// mistake stays one message.


use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn resolve(&mut self, items: &[TIRItemId]) {
        for &id in items {
            let Some(made) = self.made[self.at][id] else { continue };
            self.here = self.span(id);
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    self.params = type_names_of(&f.generics);
                    self.open_regions(&f.generics);
                    let generics = self.generics(&f.generics, &f.wheres);
                    let made_wheres = self.wheres(&f.wheres, &f.generics);
                    let params: Vec<TTIRParam> = f
                        .params
                        .iter()
                        .map(|p| TTIRParam { name: p.name.clone(), slot: None })
                        .collect();
                    let arg_tys: Vec<TyId> = f
                        .params
                        .iter()
                        .map(|p| match p.ty {
                            Some(ty) => self.ty(ty),
                            // "there is no `self: T`: the type is the one the
                            // impl names, so the annotation only ever repeated
                            // it" (§3). So the impl is asked instead.
                            None => self.receiver_ty(&p.name, self.here),
                        })
                        .collect();
                    let ret = match f.ret {
                        Some(ret) => self.ty(ret),
                        // "A `<return_type_opt>` left out is `null`" (§2).
                        None => self.types.null(),
                    };
                    let ty = self.types.intern(Ty::Fn {
                        // A declared fn captures nothing, so calling it does
                        // nothing to what it captured, however many times.
                        uses: TIRFnUses::Reads,
                        params: arg_tys.clone(),
                        ret,
                        is_unsafe: f.is_unsafe,
                    });
                    // "a reference in the return type gets the shortest-lived
                    // of the ones the parameters brought in" -- every region a
                    // parameter brought outlives every region the return has
                    // that nothing named. A region the writer named is left
                    // alone: naming it is what sharpens the answer.
                    let brought = self.regions_of(&arg_tys);
                    let given = self.regions_of(&[ret]);
                    let named: Vec<RegionId> = self.lifetimes.values().copied().collect();
                    let mut outlives = Vec::new();
                    for &shorter in &given {
                        if named.contains(&shorter) {
                            continue;
                        }
                        for &longer in &brought {
                            if longer != shorter {
                                outlives.push((longer, shorter));
                            }
                        }
                    }

                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.generics = generics;
                    held.wheres = made_wheres;
                    held.outlives = outlives;
                    held.params = params;
                    held.ret = ret;
                    held.ty = ty;
                    self.params.clear();
                }

                TIRItemKind::Struct { name: _, generics, fields, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let made_fields: Vec<TTIRFieldDecl> = fields
                        .iter()
                        .map(|f| TTIRFieldDecl {
                            vis:   f.vis,
                            attrs: f.attrs.clone(),
                            name:  f.name.clone(),
                            ty:    self.ty(f.ty),
                        })
                        .collect();
                    let TTIRItemKind::Struct { generics, fields, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *fields = made_fields;
                    self.params.clear();
                }

                TIRItemKind::Enum { generics, variants, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let made_variants: Vec<TTIRVariant> = variants
                        .iter()
                        .enumerate()
                        .map(|(i, v)| TTIRVariant {
                            attrs:   v.attrs.clone(),
                            name:    v.name.clone(),
                            payload: self.payload(&v.payload),
                            // Counted. What a written `D = 4` comes to wants
                            // the const evaluator, and there is none -- so one
                            // is counted like any other, which is wrong and is
                            // said out loud rather than hidden.
                            value:   i as i64,
                        })
                        .collect();
                    for v in &variants {
                        if let crate::tir::tir_nodes::TIRPayload::Discriminant(at) = v.payload {
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`{}` is given a number and it is counted instead", v.name),
                                    self.at(at),
                                )
                                .with_label("this is not worked out")
                                .with_note("working out a constant is the const evaluator's, and there is none yet"),
                            );
                        }
                    }
                    let TTIRItemKind::Enum { generics, variants, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *variants = made_variants;
                    self.params.clear();
                }

                TIRItemKind::TypeAlias { generics, ty, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let named = self.ty(ty);
                    let TTIRItemKind::TypeAlias { generics, ty, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *ty = named;
                    self.params.clear();
                }

                TIRItemKind::Const { ty, value, .. } => {
                    let held = self.ty(ty);
                    // What it is worth. A const is the compile-time constant,
                    // so a use of the name is the value and not a place
                    // holding it -- and this is the only place the value is
                    // still to hand, `TTIRItemKind::Const`'s own `value` being
                    // an expression id nothing fills in.
                    //
                    // Whatever it was written as and not a bare literal only:
                    // see `consts`, which is what §8 asked for. A const this
                    // cannot read is left out of the map, and a use of it stays
                    // the symbol it was -- which links against nothing, and is
                    // the same failure as before for a shrinking set of
                    // programs rather than a new one for any.
                    if let Some(lit) = self.const_value(value, 0) {
                        self.consts.insert(made, lit);
                    }
                    let TTIRItemKind::Const { ty, .. } = &mut self.out.items[made].kind else {
                        continue;
                    };
                    *ty = held;
                }

                TIRItemKind::Global { ty, init: written, .. } => {
                    let held = match ty {
                        Some(ty) => self.ty(ty),
                        None => self.types.fresh(),
                    };
                    // What it starts as, where that can be worked out. A global
                    // is a place and the back end has to put bytes somewhere
                    // for it (§8); which bytes is this, and a global with no
                    // initialiser -- or one this cannot read -- starts as
                    // nought, which is what an unwritten `var` means anywhere
                    // else and what a data segment costs nothing to give.
                    //
                    // Kept on the item rather than in a map beside it, because
                    // `TTIRItemKind::Global` has an `init` for exactly this and
                    // has been carrying `None` since it was written.
                    let start = written
                        .and_then(|at| Some((self.const_value(at, 0)?, at)))
                        .map(|(lit, at)| self.make(TTIRExprKind::Literal(lit), held, at));
                    let TTIRItemKind::Global { ty, init, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *ty = held;
                    *init = start;
                }

                TIRItemKind::Namespace { items, .. } => {
                    let inner: Vec<TTIRItemId> =
                        items.iter().filter_map(|&i| self.made[self.at][i]).collect();
                    self.resolve(&items);
                    let TTIRItemKind::Namespace { items, .. } = &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *items = inner;
                }

                TIRItemKind::Trait { members, .. } => {
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[self.at][i]).collect();
                    self.resolve(&members);
                    let TTIRItemKind::Trait { members, .. } = &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *members = inner;
                }

                TIRItemKind::Impl { generics, wheres, ty, for_ty, members, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &wheres);
                    let made_wheres = self.wheres(&wheres, &generics);
                    // "`for_ty` is `Some` where a `for` was written, and then
                    // `ty` is the trait" -- so the two swap round here.
                    let (subject, of) = match for_ty {
                        Some(for_ty) => (self.ty(for_ty), self.item_of(ty)),
                        None => (self.ty(ty), None),
                    };
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[self.at][i]).collect();
                    let held = self.subject.replace(subject);
                    self.resolve(&members);
                    self.subject = held;
                    let TTIRItemKind::Impl { generics, wheres, ty, of: written, members, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *wheres = made_wheres;
                    *ty = subject;
                    *written = of;
                    *members = inner;
                    self.params.clear();
                }

                TIRItemKind::Import { .. } => {}
            }
        }
    }

    // What stands on the right of a bound's colon, resolved. A trait is the
    // type it names; a lifetime is a region, and regions are another pass's.
    pub(super) fn bounds(&mut self, held: &[TIRBound]) -> Vec<TTIRBound> {
        held.iter()
            .map(|bound| match bound {
                TIRBound::Trait(ty) => TTIRBound::Trait(self.ty(*ty)),
                TIRBound::Life(name) => {
                    let name = name.clone();
                    let at = self.here;
                    TTIRBound::Life(self.life(&name, at))
                }
            })
            .collect()
    }

    // Every predicate with no parameter to fold into: "`where Vec<T>: Show` is
    // about a type that was built rather than declared".
    fn wheres(&mut self, held: &[TIRWherePred], generics: &[TIRGeneric]) -> Vec<TTIRWherePred> {
        let names = names_of(generics);
        held.iter()
            .filter(|pred| {
                let TIRBound::Trait(ty) = &pred.subject else { return true };
                let TIRTypeKind::Named { path, .. } = &self.tir.types[*ty].kind else {
                    return true;
                };
                !(path.len() == 1 && names.iter().any(|n| *n == path[0]))
            })
            .map(|pred| {
                let subject = match &pred.subject {
                    TIRBound::Trait(ty) => TTIRSubject::Type(self.ty(*ty)),
                    TIRBound::Life(name) => {
                        let name = name.clone();
                        let at = self.here;
                        TTIRSubject::Region(self.life(&name, at))
                    }
                };
                TTIRWherePred { subject, bounds: self.bounds(&pred.bounds) }
            })
            .collect()
    }

    fn payload(&mut self, held: &crate::tir::tir_nodes::TIRPayload) -> TTIRPayload {
        use crate::tir::tir_nodes::TIRPayload;
        match held {
            TIRPayload::None | TIRPayload::Discriminant(_) => TTIRPayload::None,
            TIRPayload::Tuple(tys) => {
                TTIRPayload::Tuple(tys.iter().map(|&t| self.ty(t)).collect())
            }
            TIRPayload::Named(fields) => TTIRPayload::Named(
                fields
                    .iter()
                    .map(|f| TTIRFieldDecl {
                        vis:   f.vis,
                        attrs: f.attrs.clone(),
                        name:  f.name.clone(),
                        ty:    self.ty(f.ty),
                    })
                    .collect(),
            ),
        }
    }

    // The declaration a type names, where it names one.
    fn item_of(&mut self, ty: TIRTypeId) -> Option<TTIRItemId> {
        let at = Span::at(self.tir.types[ty].line, self.tir.types[ty].col);
        let TIRTypeKind::Named { path, .. } = &self.tir.types[ty].kind else {
            self.errors.push(
                Diagnostic::error("a trait is what an `impl ... for` names".to_string(), at)
                    .with_label("this is a type and not a trait")
                    .with_help("`impl T { }` writes an impl of a type's own"),
            );
            return None;
        };
        let name = path.join("::");
        let Some(item) = self.look(&name) else {
            self.errors.push(
                Diagnostic::error(format!("no trait is called `{}`", name), at)
                    .with_label("nothing declares it")
                    // The two the compiler knows by name are the two most
                    // likely to be written without being declared.
                    .with_help(match name.as_str() {
                        "Copy" | "Drop" => {
                            "`Copy` and `Drop` are traits like any other and have to be declared"
                        }
                        _ => "a trait is declared with `trait`",
                    }),
            );
            return None;
        };
        if !matches!(self.out.items[item].kind, TTIRItemKind::Trait { .. }) {
            self.errors.push(
                Diagnostic::error(format!("`{}` is not a trait", name), at)
                    .with_label("this is what an impl answers")
                    .with_help("`impl T { }` writes an impl of a type's own"),
            );
            return None;
        }
        Some(item)
    }

    // ---- Types -----------------------------------------------------------

    // What a written type is. "`<grouped_type>` is gone, `_` is gone, and a
    // name has become the declaration it names."
    pub(super) fn ty(&mut self, id: TIRTypeId) -> TyId {
        let at = Span::at(self.tir.types[id].line, self.tir.types[id].col);
        match self.tir.types[id].kind.clone() {
            TIRTypeKind::Prim(prim) => self.types.prim(prim),

            TIRTypeKind::Named { path, args } => {
                // A parameter of the declaration this stands in, which is a
                // name that is not a declaration.
                if path.len() == 1 {
                    if let Some(index) = self.params.iter().position(|p| *p == path[0]) {
                        return self.types.intern(Ty::Param { name: path[0].clone(), index });
                    }
                }
                // Types and lifetimes are written in one list and kept in
                // two: a `Ty` is what unification works on and a region is what
                // it skips, so they cannot share a slot.
                let written: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        TIRGenericArg::Life(name) => Some(name.clone()),
                        TIRGenericArg::Type(_) => None,
                    })
                    .collect();
                let args: Vec<TyId> = args
                    .iter()
                    .filter_map(|a| match a {
                        TIRGenericArg::Type(ty) => Some(self.ty(*ty)),
                        TIRGenericArg::Life(_) => None,
                    })
                    .collect();
                match self.look(&path.join("::")) {
                    // "an alias is a name for a type and not a type, so once
                    // the resolver has followed it there is nothing left of it"
                    Some(item) => match &self.out.items[item].kind {
                        TTIRItemKind::TypeAlias { ty, .. } => *ty,
                        _ => {
                            let regions = self.named_regions(item, &written, at);
                            self.types.intern(Ty::Named { item, args, regions })
                        }
                    },
                    None => {
                        let name = path.join("::");
                        self.errors.push(
                            Diagnostic::error(format!("no type is called `{}`", name), at)
                                .with_label("nothing is declared under this name")
                                .with_help("a type is a struct, an enum, a trait or an alias"),
                        );
                        self.types.error()
                    }
                }
            }

            // "Every reference in a signature with no lifetime of its own gets
            // one" -- so one is made where none was written, and a written one
            // names the region its declaration declared.
            TIRTypeKind::Ref { op, life, inner } => {
                let life = match life {
                    Some(name) => self.life(&name, at),
                    None => self.region(),
                };
                let inner = self.ty(inner);
                self.types.intern(Ty::Ref { op, life, inner })
            }
            TIRTypeKind::Ptr(inner) => {
                let inner = self.ty(inner);
                self.types.intern(Ty::Ptr(inner))
            }
            TIRTypeKind::Run(elem) => {
                let elem = self.ty(elem);
                self.types.intern(Ty::Run(elem))
            }
            TIRTypeKind::Tuple(members) => {
                let members: Vec<TyId> = members.iter().map(|&m| self.ty(m)).collect();
                self.types.intern(Ty::Tuple(members))
            }
            // `fn(i32, str): bool`. Never unsafe: there is no spelling for one,
            // and "a `<return_type_opt>` left out is `null`" (§2) reaches a
            // written fn type as much as a written fn.
            TIRTypeKind::Fn { uses, params, ret } => {
                let params: Vec<TyId> = params.iter().map(|&p| self.ty(p)).collect();
                let ret = match ret {
                    Some(ret) => self.ty(ret),
                    None => self.types.null(),
                };
                self.types.intern(Ty::Fn { uses, params, ret, is_unsafe: false })
            }

            // "An `<array_suffix>` takes a `<const_expr>`, and evaluating one
            // is the checker's" -- which wants a const evaluator this pass has
            // not got. A written number is taken as it stands; anything else
            // has to wait.
            TIRTypeKind::Array { elem, len } => {
                let elem = self.ty(elem);
                match &self.tir.exprs[len].kind {
                    TIRExprKind::Literal { value: TIRLit::Int(n), .. } => {
                        self.types.intern(Ty::Array { elem, len: *n as u64 })
                    }
                    _ => {
                        self.errors.push(
                            Diagnostic::error(
                                "an array's length has to be a written number".to_string(),
                                self.at(len),
                            )
                            .with_label("this is not one")
                            .with_note("working out a constant is the const evaluator's, and there is none yet"),
                        );
                        self.types.error()
                    }
                }
            }

            // "`_`, a type argument left to be worked out" -- which is a hole,
            // and holes are what `Types` is for.
            TIRTypeKind::Infer => self.types.fresh(),
        }
    }
}

pub(super) fn names_of(generics: &[TIRGeneric]) -> Vec<String> {
    generics
        .iter()
        .map(|g| match g {
            TIRGeneric::Type { name, .. } | TIRGeneric::Life { name, .. } => name.clone(),
        })
        .collect()
}

// The type parameters alone, which is the index space a `Ty::Param` counts in.
// A lifetime is not a type: it takes no slot among them and gets no hole at a
// call, since nothing a call could work out would ever fill one.
pub(super) fn lifetimes_of(generics: &[TIRGeneric]) -> usize {
    generics.iter().filter(|g| matches!(g, TIRGeneric::Life { .. })).count()
}

pub(super) fn type_names_of(generics: &[TIRGeneric]) -> Vec<String> {
    generics
        .iter()
        .filter_map(|g| match g {
            TIRGeneric::Type { name, .. } => Some(name.clone()),
            TIRGeneric::Life { .. } => None,
        })
        .collect()
}
