// Whether a `match` leaves anything out.
//
// The check is the usual one and the shape it takes here is worth saying: what
// is left is carried as a set of things not yet matched, each arm takes some
// of it away, and what remains at the end is what the match does not cover.
// An arm that takes nothing away is an arm nothing reaches, which is the other
// message this can give.
//
// It is separate from the pattern lowering because it is a different question
// asked of the same trees: `pats.rs` says what one pattern means, and this
// says what a list of them comes to between them.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

//
// A `match` is worth "the arm taken" (§5.1), so a match where no arm is taken
// is worth nothing at all -- and every other expression in the language is
// worth something. That is the whole argument for this rule, and it is an
// argument rather than a quotation: the prose does not state it.
//
// What is checked, and what is not:
//
//   - A name or a `_` at the top of an arm takes everything, and one arm of
//     those settles it.
//   - An enum is settled by naming every variant, and what a variant carries is
//     followed where it carries one thing. Where it carries several, an arm
//     naming it settles it only if every sub-pattern takes everything -- so
//     `E::Pair(true, x)` and `E::Pair(false, x)` together are *not* read as
//     covering `E::Pair`, and a `_` or an `E::Pair(_, _)` is wanted. That is
//     the one place this asks for more than it has to.
//   - A `bool` is settled by `true` and `false`.
//   - Everything else -- a number, a `str`, a tuple -- is settled only by a
//     name or a `_`. There is no counting the i32s.

// What a run of patterns leaves out, where anything.
enum Left {
    Nothing,
    // The shapes nobody wrote, for the message: `Color::Blue`, `false`. Never
    // empty -- `These(vec![])` and `Nothing` would be two ways to say one
    // thing, and `some` is what keeps there being one.
    These(Vec<String>),
}

impl Left {
    fn some(missing: Vec<String>) -> Left {
        if missing.is_empty() {
            Left::Nothing
        } else {
            Left::These(missing)
        }
    }

    fn nothing(&self) -> bool {
        matches!(self, Left::Nothing)
    }
}

impl<'a> Lowerer<'a> {
    pub(super) fn exhaustive(
        &mut self,
        want: TyId,
        arms: &[crate::tir::tir_nodes::TIRArm],
        at: TIRExprId,
    ) {
        // Every alternative of every arm is a way in: `P | Q => ..` is two.
        let pats: Vec<TIRPatId> = arms.iter().flat_map(|arm| arm.pats.clone()).collect();
        // An arm after one that takes everything is never reached. Said as a
        // warning: the program means something, and what it means is that the
        // arm is dead.
        if let Some(first) = pats.iter().position(|&p| self.takes_everything(p)) {
            if first + 1 < pats.len() {
                self.errors.push(
                    Diagnostic::warning(
                        "this arm is never reached".to_string(),
                        self.pat_at(pats[first + 1]),
                    )
                    .with_label("an arm above takes everything")
                    .with_secondary(self.pat_at(pats[first]), "the one that does is"),
                );
            }
        }

        let Left::These(missing) = self.left_over(want, &pats) else { return };
        let list = missing.iter().map(|m| format!("`{}`", m)).collect::<Vec<_>>().join(", ");
        self.errors.push(
            Diagnostic::error("this `match` does not take everything".to_string(), self.at(at))
                .with_label(format!("{} is not taken", list))
                .with_note("a `match` is worth the arm taken, and there is no arm for these")
                .with_help("a `_` arm takes whatever is left"),
        );
    }

    // Whether a pattern takes every value of what it is tested on. A name and a
    // `_` are the two that do: "The two differ only in that the wildcard binds
    // nothing" (§5.2).
    fn takes_everything(&self, id: TIRPatId) -> bool {
        match &self.tir.pats[id].kind {
            TIRPatKind::Wildcard => true,
            // A name that names a constant tests; any other binds. Which it is
            // was settled when the pattern was lowered, and asking `names` here
            // asks the same question the same way.
            TIRPatKind::Name(path) => {
                path.len() == 1 && self.look(&path[0]).is_none()
            }
            // A tuple has one shape, so a pattern that takes everything in
            // every place takes the whole of it: `(x, y)` matches every pair.
            TIRPatKind::Tuple(elems) => elems.iter().all(|&e| self.takes_everything(e)),
            // A struct has one shape too, and a field the pattern left out is
            // a `_` in all but writing. A *variant* written this way does not:
            // there are others beside it.
            TIRPatKind::Struct { path, fields } => {
                self.variant_path(path).is_none()
                    && fields
                        .iter()
                        .all(|f| f.pat.map_or(true, |p| self.takes_everything(p)))
            }
            _ => false,
        }
    }

    fn left_over(&mut self, want: TyId, pats: &[TIRPatId]) -> Left {
        if pats.iter().any(|&p| self.takes_everything(p)) {
            return Left::Nothing;
        }
        let held = self.types.shallow(want);
        match self.types.get(held).clone() {
            // Two values, and both have to be written.
            Ty::Prim(TIRPrim::Bool) => {
                let mut missing = Vec::new();
                for want in [true, false] {
                    let found = pats.iter().any(|&p| {
                        matches!(&self.tir.pats[p].kind,
                            TIRPatKind::Lit { value: TIRLit::Bool(held), .. } if *held == want)
                    });
                    if !found {
                        missing.push(want.to_string());
                    }
                }
                Left::some(missing)
            }

            Ty::Named { item, .. } => {
                let TTIRItemKind::Enum { name, variants, .. } = &self.out.items[item].kind
                else {
                    // A struct has one shape and no way to write it as a
                    // pattern that tests, so nothing but a name settles it --
                    // and there was none, or we would have left already.
                    return Left::These(vec![self.spell(held)]);
                };
                let (held_name, count) = (name.clone(), variants.len());
                let mut missing = Vec::new();
                for index in 0..count {
                    if self.variant_taken(item, index, pats) {
                        continue;
                    }
                    let TTIRItemKind::Enum { variants, .. } = &self.out.items[item].kind else {
                        break;
                    };
                    missing.push(format!("{}::{}", held_name, variants[index].name));
                }
                Left::some(missing)
            }

            // "There is no counting the i32s": nothing but a name takes them
            // all, and there was none.
            _ => Left::These(vec![self.spell(held)]),
        }
    }

    // Whether every value of one variant is taken by some arm.
    fn variant_taken(&mut self, of: TTIRItemId, index: usize, pats: &[TIRPatId]) -> bool {
        // The arms that name this variant, and what each of them says about
        // what it carries.
        let mut carried: Vec<Vec<TIRPatId>> = Vec::new();
        for &p in pats {
            let named = match &self.tir.pats[p].kind {
                TIRPatKind::Name(path) => self.variant_path(path).map(|held| (held, Vec::new())),
                TIRPatKind::Variant { path, elems } => {
                    self.variant_path(path).map(|held| (held, elems.clone()))
                }
                TIRPatKind::Struct { path, fields } => self.variant_path(path).map(|held| {
                    (held, fields.iter().filter_map(|f| f.pat).collect())
                }),
                _ => None,
            };
            let Some(((held_of, held_index), elems)) = named else { continue };
            if held_of == of && held_index == index {
                carried.push(elems);
            }
        }
        if carried.is_empty() {
            return false;
        }

        let tys = self.payload_tys(of, index);
        match tys.len() {
            // Nothing to carry: naming it is the whole of taking it.
            0 => true,
            // One thing, so what is left of the variant is what is left of the
            // one thing -- and that is the same question again.
            1 => {
                let inner: Vec<TIRPatId> = carried.iter().filter_map(|e| e.first().copied()).collect();
                // A named field the pattern left out takes everything there.
                if carried.iter().any(|e| e.is_empty()) {
                    return true;
                }
                self.left_over(tys[0], &inner).nothing()
            }
            // Several, and this does not put them side by side: one arm that
            // takes everything in every place is what settles it.
            _ => carried.iter().any(|elems| {
                elems.len() < tys.len() || elems.iter().all(|&e| self.takes_everything(e))
            }),
        }
    }
}
