// What a `::` spells, and what it takes to answer it.
//
// A path is the one thing in the language that may name any of several kinds
// of thing -- a declaration, a variant of an enum, an associated name -- and
// which it is cannot be told from the spelling. So this is a lookup with a
// preference order rather than a rule, and the generic arguments hanging off
// it are resolved once the thing being named is known, since how many are
// wanted is a fact about what was found.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // The path an expression spells, where it spells one. A `::` chain of names
    // and nothing else: "`::` reaches into a namespace, a module or a type",
    // and all three are declarations rather than values.
    pub(super) fn flatten(&self, id: TIRExprId) -> Option<Vec<String>> {
        match &self.tir.exprs[id].kind {
            TIRExprKind::Name(path) => Some(path.clone()),
            TIRExprKind::Path { base, name } => {
                let mut held = self.flatten(*base)?;
                held.push(name.clone());
                Some(held)
            }
            _ => None,
        }
    }

    // A name, however it was spelled: a slot of this body, a variant of an
    // enum, or a declaration.
    pub(super) fn named(&mut self, path: &[String], id: TIRExprId) -> TTIRExprId {
        if path.len() == 1 {
            if let Some(slot) = self.slot(&path[0], self.at(id)) {
                let ty = self.locals()[slot].ty;
                return self.make(TTIRExprKind::Local(slot), ty, id);
            }
        }
        // `Color::Red`: a variant carrying nothing is a value on its own.
        if let Some((of, index)) = self.variant_path(path) {
            return self.variant_lit(of, index, &[], id);
        }
        match self.names.get(&path.join("::")).copied() {
            Some(item) => {
                let ty = self.item_ty(item);
                self.make(TTIRExprKind::Item(item), ty, id)
            }
            None => {
                let name = path.join("::");
                self.errors.push(
                    Diagnostic::error(format!("nothing is called `{}`", name), self.at(id))
                        .with_label("no such name here")
                        .with_help("a name is a local, a parameter, a variant, or something declared"),
                );
                self.errored(id)
            }
        }
    }

    // One variant, built. `Color::Red` carries nothing and `Shape::Line(5)`
    // carries what it was handed, and both are this.
    pub(super) fn variant_lit(
        &mut self,
        of: TTIRItemId,
        index: usize,
        args: &[TIRExprId],
        at: TIRExprId,
    ) -> TTIRExprId {
        let holes = self.holes_for(of);
        let carried = self.payload_tys(of, index);
        let carried = self.filled(&carried, &holes);
        let made: Vec<TTIRExprId> = args.iter().map(|&a| self.expr(a)).collect();
        let name = match &self.out.items[of].kind {
            TTIRItemKind::Enum { variants, .. } => variants[index].name.clone(),
            _ => String::new(),
        };

        if carried.len() != made.len() {
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` carries {} and was given {}", name, carried.len(), made.len()),
                    self.at(at),
                )
                .with_label("the wrong number of values"),
            );
        } else {
            for (i, (&want, &got)) in carried.iter().zip(made.iter()).enumerate() {
                let found = self.out.exprs[got].ty;
                if self.types.unify(found, want).is_err() {
                    let (found, want) = (self.spell(found), self.spell(want));
                    self.errors.push(
                        Diagnostic::error(
                            format!("value {} is `{}` and it carries `{}`", i + 1, found, want),
                            self.at(at),
                        )
                        .with_label("this is what it was given"),
                    );
                }
            }
        }

        let ty = self.types.intern(Ty::Named { item: of, args: holes, regions: Vec::new() });
        self.make(TTIRExprKind::VariantLit { item: of, variant: index, fields: made }, ty, at)
    }

    // One hole per type parameter a *type* declaration takes.
    //
    // `instantiate` below does this for a fn, where the arguments may also be
    // written out. A type is never given its arguments at a literal -- nobody
    // writes `Held::<i32> { v: 1 }` -- so every one of them is a hole, and what
    // fills it is what the fields turn out to hold.
    //
    // Without this a literal was typed as the bare declaration: `Held { v: 1 }`
    // came out as `Held` and not as `Held<i32>`, and the two do not unify. That
    // is why a generic struct could not be built at all, and it is the same
    // omission at all six places a named type is made -- a struct literal, a
    // variant, and the four patterns that test one.
    //
    // A bound on a type parameter is not held to anything here, because it is
    // held to nothing anywhere: `instantiate` registers them for a fn and
    // nothing does for a type. That is unchanged and is its own piece of work.
    pub(super) fn holes_for(&mut self, item: TTIRItemId) -> Vec<TyId> {
        let generics = match &self.out.items[item].kind {
            TTIRItemKind::Struct { generics, .. } | TTIRItemKind::Enum { generics, .. } => {
                generics.clone()
            }
            _ => Vec::new(),
        };
        generics
            .iter()
            .filter(|g| matches!(g, TTIRGeneric::Type { .. }))
            .map(|_| self.types.fresh())
            .collect()
    }

    // Every one of a declaration's types with the arguments put in place of its
    // parameters -- a field's, a variant's payload's -- so that what a literal
    // is held to is what it really carries.
    pub(super) fn filled(&mut self, tys: &[TyId], args: &[TyId]) -> Vec<TyId> {
        tys.iter().map(|&ty| self.types.substitute(ty, args)).collect()
    }

    // What a declaration's type comes to at one use of it. A generic is written
    // once and used many times, so every parameter is put out of the way before
    // anything is held to it -- with the arguments where they were written, and
    // with a hole for each where they were not.
    //
    // "what it stands for is settled at the call and not at the declaration",
    // which is the whole of why this happens here and not in `resolve`.
    pub(super) fn instantiate(
        &mut self,
        callee: TTIRExprId,
        written: Option<Vec<TyId>>,
        at: TIRExprId,
    ) -> TyId {
        let held = self.out.exprs[callee].ty;
        // Already settled: a `TypeArgs` puts the arguments in before the call
        // is reached, and putting more in would make holes nobody fills. Only
        // where none were written -- arguments written on something with no
        // parameters still have to be answered for.
        if written.is_none() && !self.types.has_param(held) {
            return held;
        }
        let TTIRExprKind::Item(item) = self.out.exprs[callee].kind else { return held };
        let TTIRItemKind::Fn(f) = &self.out.items[item].kind else { return held };
        // One per type parameter. A lifetime takes no argument here: what it
        // stands for is a region, and regions are worked out by the pass that
        // compares them and not by unification.
        let wanted = f.generics.iter().filter(|g| matches!(g, TTIRGeneric::Type { .. })).count();
        if wanted == 0 {
            if let Some(written) = written {
                if !written.is_empty() {
                    self.errors.push(
                        Diagnostic::error(
                            "this takes no type arguments".to_string(),
                            self.at(at),
                        )
                        .with_label("nothing here is generic"),
                    );
                }
            }
            return held;
        }

        let args: Vec<TyId> = match written {
            Some(written) if written.len() == wanted => written,
            Some(written) => {
                self.errors.push(
                    Diagnostic::error(
                        format!(
                            "this takes {} type arguments and was given {}",
                            wanted,
                            written.len()
                        ),
                        self.at(at),
                    )
                    .with_label("the wrong number"),
                );
                (0..wanted).map(|_| self.types.error()).collect()
            }
            // Nothing written, so every one is worked out.
            None => (0..wanted).map(|_| self.types.fresh()).collect(),
        };

        // Every parameter is held to what it was declared with. A hole cannot
        // be held to anything yet -- what fills it is settled by the call, and
        // the call is not over -- so only what is known is asked.
        let TTIRItemKind::Fn(f) = &self.out.items[item].kind else { return held };
        let bounds: Vec<(String, Vec<TTIRBound>)> = f
            .generics
            .iter()
            .filter_map(|g| match g {
                TTIRGeneric::Type { name, bounds } => Some((name.clone(), bounds.clone())),
                TTIRGeneric::Life { .. } => None,
            })
            .collect();
        for (arg, (name, held)) in args.iter().zip(bounds.iter()) {
            for bound in held {
                self.pending.push((*arg, bound.clone(), name.clone(), at));
            }
        }

        self.types.substitute(held, &args)
    }
}
