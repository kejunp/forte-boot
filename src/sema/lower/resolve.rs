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
                    // The impl's parameters first, then its own: a member of
                    // `impl<T> Box<T>` writing `fn map<U>(..)` has `T` at 0 and
                    // `U` at 1, and the whole of what makes that work for every
                    // pass after this one is that the two lists are one list.
                    // See `Lowerer::outer`.
                    self.params = names_of_made(&self.outer);
                    // A member may not re-declare one of the impl's. Nothing
                    // would read the second: a `Ty::Param` is found by name and
                    // the first of that name answers, so the member's own would
                    // be a parameter nothing could write and every use of the
                    // name would mean the impl's. What came of that before it
                    // was said out loud was a type the checker never settled
                    // and a program that would not link.
                    for name in type_names_of(&f.generics) {
                        if self.params.contains(&name) {
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`{}` is already a parameter of this impl", name),
                                    self.here,
                                )
                                .with_label("it is declared twice over")
                                .with_help(
                                    "an impl's parameters stand in scope through its members, \
                                     so a member has to name its own something else",
                                ),
                            );
                        }
                        self.params.push(name);
                    }
                    self.open_regions(&f.generics);
                    let mut generics = self.outer.clone();
                    generics.extend(self.generics(&f.generics, &f.wheres));
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

                    // What the body declared, resolved in the scope the body
                    // is walked in -- the fn's, which is where a declaration
                    // written in a block stands. After the signature, so that
                    // one cannot name a type the body declares: what is
                    // written inside a fn is the fn's own and not the
                    // caller's business.
                    if let Some(value) = f.body {
                        let held = self.inside(value);
                        if !held.is_empty() {
                            self.inner.push(self.inner_scope(value));
                            let outer = std::mem::take(&mut self.outer);
                            self.resolve(&held);
                            self.outer = outer;
                            self.inner.pop();
                        }
                    }
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
                    let made_variants = self.numbered(&variants, made);
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
                    // Held to what it was declared as, here rather than at a
                    // use. A const's value becomes a `Literal` node where the
                    // name is written and not where the const is, so the walk
                    // that holds every literal to its type would point at a
                    // use -- and would say nothing at all about a const
                    // nobody used. Both are the wrong answer to "this value
                    // does not fit".
                    //
                    // One that does not fit is left out of the map as one this
                    // could not read is, so nothing puts it at a use either.
                    // Which link error that would be is not a question: a
                    // program with an error reported does not get as far as a
                    // linker.
                    match self.literal_of(value) {
                        Some(lit) => {
                            if self.fits_declared(&lit, held, self.span(id)) {
                                self.consts.insert(made, lit);
                            }
                        }
                        // Nothing folded. Where the reason is one worth saying,
                        // say it: a `1 / 0` written in a const is a mistake and
                        // not a shape the evaluator has not got to, and what it
                        // used to get was an undefined symbol at the link step.
                        None => self.no_nought(value),
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
                    if let Some(at) = written {
                        if self.literal_of(at).is_none() {
                            self.no_nought(at);
                        }
                    }
                    let start = written
                        .and_then(|at| Some((self.literal_of(at)?, at)))
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

                TIRItemKind::Trait { generics, members, .. } => {
                    // A member with a body is refused. The grammar admits one
                    // -- a `<trait_member>` is a `<fn_decl>` or a `<fn_sig>` --
                    // and nothing below reads it: what a trait declares is a
                    // *signature*, and the body it wrote was accepted, ignored,
                    // and then left the table with an entry nobody had filled,
                    // which is a call through a word nobody wrote.
                    //
                    // What it would take is a body written about `Self`, so
                    // that one body serves every impl that does not write its
                    // own. `Self` is a type now -- see below -- and this is
                    // what is left to do with it.
                    for &at in &members {
                        let TIRItemKind::Fn(f) = &self.tir.items[at].kind else { continue };
                        if f.body.is_none() {
                            continue;
                        }
                        let name = f.name.clone();
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` is declared with a body", name),
                                self.span(at),
                            )
                            .with_label("a trait declares a signature")
                            .with_note(
                                "a body here would be the one every impl that wrote none \
                                 fell back to, which wants a `Self` to write it about",
                            ),
                        );
                    }
                    // `Self` is the trait's first parameter, standing for the
                    // type that answers it -- so `fn same(&self, other: &Self)`
                    // is a signature the checker can hold an impl to, and a
                    // call through a bound fills it from the receiver by the
                    // same unification that fills an `impl<T>`'s `T`.
                    //
                    // It is a parameter and not a fresh idea: a member's
                    // generics are the declaration's followed by its own
                    // (`Lowerer::outer`), and putting `Self` at the front of
                    // the trait's makes every pass below treat it as the
                    // parameter it is. `instance_of` makes a hole for it at
                    // each use, and `mir::mono` substitutes the concrete type
                    // in, which is what a table for one type is.
                    self.receivers(&members, "a trait");
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let mut made_generics =
                        vec![TTIRGeneric::Type { name: SELF.to_string(), bounds: Vec::new() }];
                    made_generics.extend(self.generics(&generics, &[]));
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[self.at][i]).collect();
                    let outer = std::mem::replace(&mut self.outer, made_generics.clone());
                    self.resolve(&members);
                    self.outer = outer;
                    let TTIRItemKind::Trait { generics, members, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *members = inner;
                    self.params.clear();
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
                    self.receivers(&members, "an impl");
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[self.at][i]).collect();
                    let held = self.subject.replace(subject);
                    // What the members are walked with: the impl's parameters
                    // stand in scope through all of them, and nothing else
                    // nests, so this is a swap and not a stack.
                    let outer = std::mem::replace(&mut self.outer, made_generics.clone());
                    self.resolve(&members);
                    self.outer = outer;
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

    // Every member takes a receiver, because nothing can reach one that does
    // not.
    //
    // "An impl holds methods, and a method is reached through a value with a
    // `.` like any other member" (§5), and "an enum variant is what `::`
    // reaches in a type, and the only thing" -- so `P::zero()` names nothing
    // and there is no other spelling. One written without a receiver used to
    // be declared under its bare name in the file's scope, which made it a
    // free `zero()` callable anywhere in the file; with that gone it is a
    // declaration nothing at all can name, and a body nobody can call is
    // better turned down than compiled.
    fn receivers(&mut self, members: &[TIRItemId], what: &str) {
        for &at in members {
            let TIRItemKind::Fn(f) = &self.tir.items[at].kind else { continue };
            if matches!(f.params.first().map(|p| &p.name), Some(TIRBinding::SelfRecv(..))) {
                continue;
            }
            let name = f.name.clone();
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` takes no receiver", name),
                    self.span(at),
                )
                .with_label(format!("this is a member of {}", what))
                .with_help(
                    "a method is reached through a value with a `.`, so one that \
                     takes no `self` is one nothing can name -- a fn beside the \
                     declaration, or one in a `namespace`, is what to write instead",
                ),
            );
        }
    }

    // A divide by nought in something that had to fold, said where it stands.
    // Nothing where the expression is merely one the evaluator cannot read,
    // which is not a mistake and has never been reported as one.
    fn no_nought(&mut self, at: TIRExprId) {
        let Some(where_) = self.divides_by_nought(at, 0) else { return };
        self.errors.push(
            Diagnostic::error("this divides by nought".to_string(), where_)
                .with_label("the right side is nought")
                .with_note(
                    "a constant is worked out where it is written, so there is nowhere \
                     for this to happen but here",
                ),
        );
    }

    // Whether the value fits the type it was declared as, and a message where
    // it does not. `true` for everything this does not ask about, which is a
    // float, a string and every type that is not a whole number.
    fn fits_declared(&mut self, lit: &TIRLit, ty: TyId, at: Span) -> bool {
        let TIRLit::Int(n) = lit else { return true };
        let Ty::Prim(prim) = self.types.get(ty).clone() else { return true };
        let Some((low, high)) = crate::sema::lower::range_of(prim) else { return true };
        if *n >= low && *n <= high {
            return true;
        }
        let name = crate::sema::names::prim_name(prim);
        self.errors.push(
            Diagnostic::error(format!("{} does not fit in `{}`", n, name), at)
                .with_label("this is what it was declared as")
                .with_note(format!("a `{}` holds {} to {}", name, low, high)),
        );
        false
    }

    // What an expression is worth at compile time: what the evaluator folds
    // it to, or a string written as itself.
    //
    // The evaluator answers `None` for a string and is right to -- "a string
    // is bytes and null is no news; neither is arithmetic" -- but neither a
    // const nor a global is being folded *into* anything there; each is being
    // given a value, and a literal is a perfectly good one to be given. So the
    // one case the evaluator declines is taken here instead, and only where it
    // was written plainly: `"a" + "b"` is still nothing this can read, there
    // being no such operator.
    //
    // Both callers wanted it and each was wrong without it in its own way. A
    // global started as sixteen noughts and read back empty; a const was left
    // out of the map, so a use of it stayed the symbol it was and linked
    // against nothing -- which the comment above it calls "a shrinking set of
    // programs", and this is what shrinks it.
    fn literal_of(&self, at: TIRExprId) -> Option<TIRLit> {
        if let TIRExprKind::Literal { value: TIRLit::Str(text), .. } =
            &self.tir.exprs.get(at)?.kind
        {
            return Some(TIRLit::Str(text.clone()));
        }
        self.const_value(at, 0)
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

    // What number each variant is, and the payload beside it.
    //
    // "A variant with no payload may fix its discriminant instead, which is
    // what makes an enum of plain constants" (§2). It could not: what a
    // written `D = 4` comes to wanted a const evaluator and there was none, so
    // every variant was counted and the written number was refused out loud.
    // There is one now (`consts`), and it is the same one a `const` and an
    // array's length are worked out by.
    //
    // Counting carries on from whatever was last written, which is C's rule
    // and Rust's and the only one that makes `A = 4, B, C` mean what it looks
    // like. So a number is fixed where one is written and one more than the
    // last everywhere else, and the first variant is nought.
    //
    // Only backwards, as everything the evaluator reads is: `self.consts`
    // holds what has been worked out so far, so a discriminant naming a const
    // declared below it does not fold. That is the order a reader writes in
    // anyway.
    fn numbered(
        &mut self,
        variants: &[crate::tir::tir_nodes::TIRVariant],
        made: TTIRItemId,
    ) -> Vec<TTIRVariant> {
        // How wide the tag was fixed at, where `%repr` fixed one. Every number
        // below has to fit in it: a value that does not is one the tag cannot
        // hold, and quietly keeping the low bytes of it would be a variant
        // that reads back as another.
        let fixed = match &self.out.items[made].kind {
            TTIRItemKind::Enum { attrs, .. } => match attrs.repr {
                Some(crate::tir::tir_nodes::TIRRepr::C) => Some(4usize),
                Some(crate::tir::tir_nodes::TIRRepr::Tag(bytes)) => Some(bytes),
                None => None,
            },
            _ => None,
        };
        // `%repr(C)` says a value is laid out the way the platform's C would
        // lay it out, and C has no name for an enum that carries something: a
        // tagged union there is a struct holding an int and a union, which is
        // not this shape and not one a reader writing `%repr(C)` meant. So it
        // is refused, and `%repr(4)` is what fixes the tag of one that does
        // carry -- which is a promise this compiler makes about itself rather
        // than one about C.
        let carries = variants
            .iter()
            .any(|v| !matches!(v.payload, crate::tir::tir_nodes::TIRPayload::None
                                        | crate::tir::tir_nodes::TIRPayload::Discriminant(_)));
        let c = matches!(
            &self.out.items[made].kind,
            TTIRItemKind::Enum { attrs, .. }
                if attrs.repr == Some(crate::tir::tir_nodes::TIRRepr::C)
        );
        if c && carries {
            self.errors.push(
                Diagnostic::error(
                    "`%repr(C)` is written on an enum that carries nothing".to_string(),
                    self.here,
                )
                .with_label("a variant of this one carries something")
                .with_note(
                    "C has no name for an enum that carries: what it writes for one is a \
                     struct holding an int and a union, which is not this shape",
                )
                .with_help("`%repr(4)` fixes the tag of one that carries"),
            );
        }
        let mut out = Vec::with_capacity(variants.len());
        let mut next = 0i64;
        for v in variants {
            let value = match v.payload {
                crate::tir::tir_nodes::TIRPayload::Discriminant(at) => {
                    match self.const_value(at, 0) {
                        Some(TIRLit::Int(n)) => n,
                        // Worked out and not a whole number, or not worked out
                        // at all. Both are the same thing to say: a tag is an
                        // integer and this is not one yet.
                        _ => {
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`{}` is not given a whole number", v.name),
                                    self.at(at),
                                )
                                .with_label("this is what it was given")
                                .with_note(
                                    "a variant's number is worked out where it is written, \
                                     out of literals, the operators over them, and a const \
                                     already declared above it",
                                ),
                            );
                            next
                        }
                    }
                }
                _ => next,
            };
            // Two variants of one number are two names for one value, and a
            // `match` on the tag cannot tell them apart -- so the second arm
            // is unreachable and nothing would have said so.
            if let Some(held) = out.iter().position(|held: &TTIRVariant| held.value == value) {
                let first = variants[held].name.clone();
                self.errors.push(
                    Diagnostic::error(
                        format!("`{}` and `{}` are both {}", first, v.name, value),
                        self.here,
                    )
                    .with_label("two variants of one number")
                    .with_note(
                        "the tag is what a `match` reads, so two of one number are two \
                         names nothing can tell apart",
                    ),
                );
            }
            // Held to the width, where one was written. Signed, the tag
            // being a signed integer whatever the numbers are (§8).
            //
            // Eight bytes is every number there is, and asking the question
            // of it would be asking for `-(1 << 63)`, which is one more than
            // an `i64` holds.
            if let Some(bytes) = fixed.filter(|&held| held < 8) {
                let bits = bytes * 8;
                let (low, high) = (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1);
                if value < low || value > high {
                    self.errors.push(
                        Diagnostic::error(
                            format!("{} does not fit in a tag of {} bytes", value, bytes),
                            self.here,
                        )
                        .with_label(format!("`{}` is given this number", v.name))
                        .with_note(format!(
                            "a tag of {} bytes holds {} to {}, and `%repr` is what fixed it",
                            bytes, low, high
                        )),
                    );
                }
            }
            next = value.saturating_add(1);
            out.push(TTIRVariant {
                attrs:   v.attrs.clone(),
                name:    v.name.clone(),
                payload: self.payload(&v.payload),
                value,
            });
        }
        out
    }

    // ---- Types -----------------------------------------------------------

    // A type of no known size, said where something was asked to hold one.
    // `false` is "nothing to say", so it may be asked about any type at all.
    //
    // "`T[]` is a run of T whose length the type does not give. That makes it
    // a type of no known size, and nothing can hold one: no local, no field,
    // no parameter and no return may be a `T[]`. It exists only behind a
    // reference" (§2) -- and a `dyn` is that sentence again with a different
    // reason for the width being unknown.
    //
    // Two callers, and they reach different halves of the rule. `exprs` asks
    // it of a local's type however that was arrived at, which is the half a
    // written type cannot reach: `let x = a[1..3]` is a place of type `T[]`
    // and nobody wrote a type down. `ty` below asks it of every type that
    // *was* written, which is the half a local cannot reach -- a parameter, a
    // return, a field, a payload, a type argument.
    pub(super) fn unheld(&mut self, ty: TyId, at: Span) -> bool {
        let (what, knowing, borrows) = match self.types.get(ty) {
            Ty::Run(_) => ("a run", "how many there are", "a view of it, which carries the length"),
            Ty::Dyn(_) => {
                ("a trait object", "how wide it is", "one, which carries the table beside it")
            }
            _ => return false,
        };
        let held = self.spell(ty);
        self.errors.push(
            Diagnostic::error(format!("`{}` is {} and nothing holds one", held, what), at)
                .with_label(format!("holding it would mean knowing {}", knowing))
                .with_note("no local, no field, no parameter and no return is one of these")
                .with_help(format!("`&{}` borrows {}", held, borrows)),
        );
        true
    }

    // The same question asked of a type as it is resolved, and the one place
    // the answer may be no: what a reference refers to.
    //
    // Both shapes resolved and were let through before this. What the reader
    // got instead was a message at every *call* -- "argument 1 is `Sq` and it
    // takes `dyn Shape`" -- blaming a caller for a signature nobody could have
    // satisfied; and `mir::layout` says outright that a bare `dyn` is "a
    // program already turned down" by this pass, which it was not.
    //
    // A pointer counts as behind. It promises nothing about what it addresses
    // -- "the one type the checker has nothing to say about" (§2) -- so
    // `ptr u8[]` is an address in a run and `ptr dyn Shape` carries the table
    // beside it exactly as a `&dyn Shape` does.
    fn holdable(&mut self, behind: bool, held: Ty, at: Span) -> bool {
        if behind {
            return true;
        }
        let ty = self.types.intern(held);
        !self.unheld(ty, at)
    }

    // What a written type is. "`<grouped_type>` is gone, `_` is gone, and a
    // name has become the declaration it names."
    pub(super) fn ty(&mut self, id: TIRTypeId) -> TyId {
        let at = Span::at(self.tir.types[id].line, self.tir.types[id].col);
        // Taken, so it reaches this type and no other -- see `Lowerer::behind`.
        let behind = std::mem::take(&mut self.behind);
        match self.tir.types[id].kind.clone() {
            TIRTypeKind::Prim(prim) => self.types.prim(prim),

            TIRTypeKind::Named { path, args } => {
                // A parameter of the declaration this stands in, which is a
                // name that is not a declaration.
                if path.len() == 1 {
                    // Inside an impl `Self` is the type the impl is about,
                    // which is a type and not a parameter: it is written down
                    // in the header and there is nothing left to work out.
                    // Inside a trait it is the parameter put there above, and
                    // `self.params` holds it like any other.
                    if path[0] == SELF {
                        if let Some(subject) = self.subject {
                            return subject;
                        }
                        if !self.params.iter().any(|p| p == SELF) {
                            self.errors.push(
                                Diagnostic::error(
                                    "`Self` is written outside a trait or an impl".to_string(),
                                    at,
                                )
                                .with_label("there is nothing here for it to name")
                                .with_help(
                                    "`Self` is the type an impl is about, and the type \
                                     that answers a trait -- it names neither anywhere \
                                     else",
                                ),
                            );
                            return self.types.error();
                        }
                    }
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

            TIRTypeKind::Gc(inner) => {
                // A `gc` counts as behind for a trait object and not for a
                // run. What a `gc dyn Shape` is, is two words -- the handle
                // and the table -- exactly as a `&dyn Shape` is, so the width
                // the type has not got is supplied the same way; and it is the
                // owned form a container of objects wants, a `&dyn Shape`
                // living only as long as what it was made from.
                //
                // A run is refused because its second word is a *length*, and
                // a length is not something the collector hands out: what it
                // would take is an allocation that knows how many are in it,
                // which is a shape neither word has been asked to make.
                self.behind = true;
                let inner = self.ty(inner);
                if matches!(self.types.get(inner), Ty::Run(_)) && !self.unheld(inner, at) {
                    return self.types.error();
                }
                self.types.intern(Ty::GC(inner))
            }

            // `dyn Shape`: the name has to be a trait, and it is the one
            // place a type position takes one. A struct there would be a
            // `dyn` over something with no impls to dispatch between, which
            // is a mistake and not a shorthand.
            TIRTypeKind::Dyn(inner) => {
                let TIRTypeKind::Named { path, .. } = self.tir.types[inner].kind.clone() else {
                    self.errors.push(
                        Diagnostic::error(
                            "`dyn` takes the name of a trait".to_string(),
                            at,
                        )
                        .with_label("this is not a name"),
                    );
                    return self.types.error();
                };
                let name = path.join("::");
                let Some(item) = self.look(&name) else {
                    self.errors.push(
                        Diagnostic::error(format!("no trait is called `{}`", name), at)
                            .with_label("nothing is declared under this name"),
                    );
                    return self.types.error();
                };
                if !matches!(self.out.items[item].kind, TTIRItemKind::Trait { .. }) {
                    self.errors.push(
                        Diagnostic::error(format!("`{}` is not a trait", name), at)
                            .with_label("`dyn` stands in front of a trait")
                            .with_help(
                                "a `dyn` is what several types answer to, so what it \
                                 names has to be the thing they answer",
                            ),
                    );
                    return self.types.error();
                }
                if !self.holdable(behind, Ty::Dyn(item), at) {
                    return self.types.error();
                }
                self.types.intern(Ty::Dyn(item))
            }

            // "Every reference in a signature with no lifetime of its own gets
            // one" -- so one is made where none was written, and a written one
            // names the region its declaration declared.
            TIRTypeKind::Ref { op, life, inner } => {
                let life = match life {
                    Some(name) => self.life(&name, at),
                    None => self.region(),
                };
                // What a reference refers to is the one place a type of no
                // known size stands, and a pointer below says the same: both
                // supply the width the type itself has not got.
                self.behind = true;
                let inner = self.ty(inner);
                self.types.intern(Ty::Ref { op, life, inner })
            }
            TIRTypeKind::Ptr(inner) => {
                self.behind = true;
                let inner = self.ty(inner);
                self.types.intern(Ty::Ptr(inner))
            }
            TIRTypeKind::Run(elem) => {
                let elem = self.ty(elem);
                if !self.holdable(behind, Ty::Run(elem), at) {
                    return self.types.error();
                }
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

// The same over the ones already made, which is what an impl hands its members:
// by then the bounds have been resolved and there is no going back to the tree.
// The name of a trait's first parameter, and of the type an impl is about.
// Capitalised, so it is not `self`: one is a type and the other is a value,
// and the two stand in different positions.
pub(super) const SELF: &str = "Self";

pub(super) fn names_of_made(generics: &[TTIRGeneric]) -> Vec<String> {
    generics
        .iter()
        .filter_map(|g| match g {
            TTIRGeneric::Type { name, .. } => Some(name.clone()),
            TTIRGeneric::Life { .. } => None,
        })
        .collect()
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
