// `match`, and the patterns it is written out of.
//
// A pattern is two things at once and both are settled here. It is a test --
// which values reach this arm -- and it is a set of names, bound out of what
// the test found. The first has to agree with the type of the subject and the
// second has to agree between arms, since every arm binds into the same slots.
//
// What a pattern *does* to what it matched is the other half, and it is in
// `binds.rs`: taking a name out of a value moves it, which is a question about
// ownership rather than about types and is much the longer story.

use std::collections::HashMap;

use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn matching(
        &mut self,
        scrutinee: TIRExprId,
        arms: &[crate::tir::tir_nodes::TIRArm],
        // What was expected of the `match`, which is what is expected of each
        // arm. See `Lowerer::want`.
        wanted: Option<TyId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        let s = self.expr(scrutinee);
        let want = self.out.exprs[s].ty;

        let mut made = Vec::new();
        let mut ty: Option<TyId> = None;
        for arm in arms {
            // The alternatives of one arm bind into one scope: `P(x) | Q(x)` is
            // one `x` and one body.
            self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
            let pats: Vec<TTIRPatId> = arm.pats.iter().map(|&p| self.pat(p, want)).collect();
            // Each arm is handed what was wanted of the `match`, an arm
            // being a value the whole is worth exactly as an `if`'s branch
            // is. `want` here is the *scrutinee's*, which is a different
            // question and is `self.want`'s to answer.
            self.want = wanted;
            let body = self.expr(arm.body);
            let body = self.held_to(body, wanted);
            self.frames.last_mut().expect("a frame").scopes.pop();

            let found = self.out.exprs[body].ty;
            ty = Some(match ty {
                None => found,
                Some(held) => match self.types.unify(held, found) {
                    Ok(one) => one,
                    Err(_) => {
                        let (held, found) = (self.spell(held), self.spell(found));
                        self.errors.push(
                            Diagnostic::error(
                                format!("one arm gives `{}` and another `{}`", held, found),
                                self.at(arm.body),
                            )
                            .with_label("a `match` is worth one type")
                            .with_help("`never` agrees with anything, which is what a `panic` arm is for"),
                        );
                        self.types.error()
                    }
                },
            });
            made.push(crate::tir::ttir_nodes::TTIRArm { pats, body });
        }

        self.exhaustive(want, arms, at);

        // "a match with no arms" is a match on `never`, which is worth nothing
        // and reaches nothing.
        let ty = ty.unwrap_or_else(|| self.types.never());
        self.make(TTIRExprKind::Match { scrutinee: s, arms: made }, ty, at)
    }

    pub(super) fn make_pat(&mut self, kind: TTIRPatKind, ty: TyId, at: TIRPatId) -> TTIRPatId {
        let held = &self.tir.pats[at];
        self.out.pats.push(crate::tir::ttir_nodes::TTIRPat {
            kind,
            ty,
            line: held.line,
            col: held.col,
        });
        self.out.pats.len() - 1
    }

    pub(super) fn pat_at(&self, at: TIRPatId) -> Span {
        Span::at(self.tir.pats[at].line, self.tir.pats[at].col)
    }

    // One pattern, tested against `want`. A name is the interesting one:
    // "A `<const_pattern>` tests and any other name binds, which makes what a
    // pattern means depend on what is in scope" (§5.2).
    fn pat(&mut self, id: TIRPatId, want: TyId) -> TTIRPatId {
        match self.tir.pats[id].kind.clone() {
            TIRPatKind::Wildcard => self.make_pat(TTIRPatKind::Wildcard, want, id),

            TIRPatKind::Name(path) => {
                // It names a constant, so it tests against one.
                let named = self.look(&path.join("::"));
                if let Some(item) = named {
                    if matches!(self.out.items[item].kind, TTIRItemKind::Const { .. }) {
                        let held = self.item_ty(item);
                        self.hold(held, want, id);
                        return self.make_pat(TTIRPatKind::Const(item), want, id);
                    }
                }
                // Or a variant carrying nothing: `Color::Red`, reached through
                // the enum that holds it.
                if let Some((of, index)) = self.variant_path(&path) {
                    let holes = self.holes_for(of);
                    let ty =
                        self.types.intern(Ty::Named { item: of, args: holes, regions: Vec::new() });
                    self.hold(ty, want, id);
                    return self.make_pat(
                        TTIRPatKind::Variant { item: of, variant: index, elems: Vec::new() },
                        want,
                        id,
                    );
                }
                // Anything else binds.
                self.binding(&path, want, id)
            }

            TIRPatKind::Lit { negated, value, suffix } => {
                let ty = match (&value, suffix) {
                    (_, Some(prim)) => self.types.prim(prim),
                    (TIRLit::Int(_), None) => self.types.fresh_whole(),
                    (TIRLit::Float(_), None) => self.types.fresh_fractional(),
                    (TIRLit::Str(_), None) => self.types.prim(TIRPrim::Str),
                    (TIRLit::Char(_), None) => self.types.prim(TIRPrim::Char),
                    (TIRLit::Bool(_), None) => self.types.prim(TIRPrim::Bool),
                    (TIRLit::Null, None) => self.types.null(),
                };
                self.hold(ty, want, id);
                self.make_pat(TTIRPatKind::Lit { negated, value }, want, id)
            }

            TIRPatKind::Range { op, lo, hi } => {
                let lo = self.pat(lo, want);
                let hi = self.pat(hi, want);
                self.make_pat(TTIRPatKind::Range { op, lo, hi }, want, id)
            }

            TIRPatKind::Tuple(elems) => {
                let members = match self.types.get(want).clone() {
                    Ty::Tuple(members) if members.len() == elems.len() => members,
                    Ty::Tuple(members) => {
                        self.errors.push(
                            Diagnostic::error(
                                format!(
                                    "this tuple has {} members and the pattern has {}",
                                    members.len(),
                                    elems.len()
                                ),
                                self.pat_at(id),
                            )
                            .with_label("the two are not the same length"),
                        );
                        return self.errored_pat(id, want);
                    }
                    _ => {
                        let held = self.spell(want);
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` is not a tuple", held),
                                self.pat_at(id),
                            )
                            .with_label("this tests one"),
                        );
                        return self.errored_pat(id, want);
                    }
                };
                let made: Vec<TTIRPatId> = elems
                    .iter()
                    .zip(members.iter())
                    .map(|(&e, &m)| self.pat(e, m))
                    .collect();
                self.make_pat(TTIRPatKind::Tuple(made), want, id)
            }

            TIRPatKind::Variant { path, elems } => {
                let Some((of, index)) = self.variant_path(&path) else {
                    let name = path.join("::");
                    self.errors.push(
                        Diagnostic::error(format!("`{}` is not a variant", name), self.pat_at(id))
                            .with_label("this tests one")
                            .with_help("a variant is reached through the enum that holds it"),
                    );
                    return self.errored_pat(id, want);
                };
                let holes = self.holes_for(of);
                let ty =
                    self.types.intern(Ty::Named { item: of, args: holes.clone(), regions: Vec::new() });
                self.hold(ty, want, id);
                let carried = self.payload_tys(of, index);
                let carried = self.filled(&carried, &holes);
                let made: Vec<TTIRPatId> = elems
                    .iter()
                    .enumerate()
                    .map(|(i, &e)| {
                        let want = carried.get(i).copied().unwrap_or_else(|| self.types.error());
                        self.pat(e, want)
                    })
                    .collect();
                self.make_pat(
                    TTIRPatKind::Variant { item: of, variant: index, elems: made },
                    want,
                    id,
                )
            }

            TIRPatKind::Struct { path, fields } => {
                // A variant may be struct-shaped too: `Shape::Box { w, h }` is
                // written like a struct and is a variant, and which it is is
                // what the path names.
                if let Some((of, index)) = self.variant_path(&path) {
                    let holes = self.holes_for(of);
                    let ty = self
                        .types
                        .intern(Ty::Named { item: of, args: holes.clone(), regions: Vec::new() });
                    self.hold(ty, want, id);
                    let named = self.payload_names(of, index);
                    let named: Vec<(String, TyId)> = {
                        let (ns, tys): (Vec<String>, Vec<TyId>) = named.into_iter().unzip();
                        let tys = self.filled(&tys, &holes);
                        ns.into_iter().zip(tys).collect()
                    };
                    let mut placed: Vec<Option<TTIRPatId>> = vec![None; named.len()];
                    for field in &fields {
                        let Some(index) = named.iter().position(|(n, _)| *n == field.name) else {
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`{}` carries no `{}`", path.join("::"), field.name),
                                    self.pat_at(id),
                                )
                                .with_label("no such field"),
                            );
                            continue;
                        };
                        let want = named[index].1;
                        placed[index] = Some(match field.pat {
                            Some(pat) => self.pat(pat, want),
                            None => {
                                let slot = self.bind(
                                    TIRBinding::Name(field.name.clone()),
                                    want,
                                    crate::tir::tir_nodes::TIRIntro::Let,
                                    self.pat_at(id),
                                );
                                self.make_pat(TTIRPatKind::Bind(slot), want, id)
                            }
                        });
                    }
                    // A variant's fields are held by place, so one the pattern
                    // did not name is a wildcard rather than a hole.
                    let elems: Vec<TTIRPatId> = placed
                        .into_iter()
                        .enumerate()
                        .map(|(i, held)| match held {
                            Some(pat) => pat,
                            None => {
                                let ty = named[i].1;
                                self.make_pat(TTIRPatKind::Wildcard, ty, id)
                            }
                        })
                        .collect();
                    return self.make_pat(
                        TTIRPatKind::Variant { item: of, variant: index, elems },
                        want,
                        id,
                    );
                }
                let Some(item) = self.look(&path.join("::")) else {
                    let name = path.join("::");
                    self.errors.push(
                        Diagnostic::error(format!("no type is called `{}`", name), self.pat_at(id))
                            .with_label("nothing is declared under this name"),
                    );
                    return self.errored_pat(id, want);
                };
                let TTIRItemKind::Struct { name, fields: declared, .. } =
                    &self.out.items[item].kind
                else {
                    let name = path.join("::");
                    self.errors.push(
                        Diagnostic::error(format!("`{}` is not a struct", name), self.pat_at(id))
                            .with_label("this tests one"),
                    );
                    return self.errored_pat(id, want);
                };
                let held = name.clone();
                let declared: Vec<(String, TyId)> =
                    declared.iter().map(|f| (f.name.clone(), f.ty)).collect();
                let holes = self.holes_for(item);
                let declared: Vec<(String, TyId)> = {
                    let (ns, tys): (Vec<String>, Vec<TyId>) = declared.into_iter().unzip();
                    let tys = self.filled(&tys, &holes);
                    ns.into_iter().zip(tys).collect()
                };
                let regions = self.named_regions(item, &[], self.pat_at(id));
                let ty = self.types.intern(Ty::Named { item, args: holes, regions });
                self.hold(ty, want, id);

                // "Fields in declaration order, `None` where the pattern named
                // none" -- so a pattern may test some and leave the rest.
                let mut placed: Vec<Option<TTIRPatId>> = vec![None; declared.len()];
                for field in &fields {
                    let Some(index) = declared.iter().position(|(n, _)| *n == field.name) else {
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` has no field `{}`", held, field.name),
                                self.pat_at(id),
                            )
                            .with_label("no such field"),
                        );
                        continue;
                    };
                    let want = declared[index].1;
                    // `P { x }` is the shorthand: the field's own name binds.
                    placed[index] = Some(match field.pat {
                        Some(pat) => self.pat(pat, want),
                        None => {
                            let slot = self.bind(
                                TIRBinding::Name(field.name.clone()),
                                want,
                                crate::tir::tir_nodes::TIRIntro::Let,
                                self.pat_at(id),
                            );
                            self.make_pat(TTIRPatKind::Bind(slot), want, id)
                        }
                    });
                }
                self.make_pat(TTIRPatKind::Struct { item, fields: placed }, want, id)
            }
        }
    }
}
