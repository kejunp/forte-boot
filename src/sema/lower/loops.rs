// `while` and `for`, and the one thing that makes them more than a block.
//
// A `for` binds a name per turn, which is a slot of the body like any other
// and a scope of its own -- so what the loop declares goes when the loop does.
// And a `break` may carry a value, which makes a loop an expression with a
// type: every `break` out of one has to agree with every other, and a loop
// nothing breaks out of with a value is `null`.

use std::collections::HashMap;

use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // `for x in it`. The loop variable is a slot of the body, bound afresh each
    // turn, and what it holds is what the iterable holds.
    pub(super) fn for_each(
        &mut self,
        name: &TIRBinding,
        iter: TIRExprId,
        body: TIRExprId,
        at: TIRExprId,
    ) -> TTIRExprId {
        let it = self.expr(iter);
        let over = self.out.exprs[it].ty;
        let elem = match self.elem_of(over) {
            Some(elem) => elem,
            None => {
                if !matches!(self.types.get(over), Ty::Error) {
                    let held = self.spell(over);
                    self.errors.push(
                        Diagnostic::error(
                            format!("there is no running through a `{}`", held),
                            self.at(iter),
                        )
                        .with_label("this is what the loop is over")
                        .with_note("an array, a view of one, a `Range`, a `Set` or a `HashSet`")
                        .with_help("the language has no iterator protocol, so what may be run through is a closed set"),
                    );
                }
                self.types.error()
            }
        };

        // The loop variable stands in the body and nowhere else.
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
        let local =
            self.bind(name.clone(), elem, crate::tir::tir_nodes::TIRIntro::Let, self.at(at));
        self.breaks.push(Vec::new());
        let b = self.expr(body);
        let ty = self.loop_value(at);
        self.frames.last_mut().expect("a frame").scopes.pop();

        self.make(TTIRExprKind::For { local, iter: it, body: b }, ty, at)
    }

    // What a loop is worth: "the operand of the `break` that leaves it... and
    // where none is given the loop is `null`". A loop that can end by itself
    // has `null` among the values it yields, which is the same rule asked of
    // the loop -- and `null` belongs to every type, so a loop with a `break x`
    // is worth what `x` is.
    pub(super) fn loop_value(&mut self, at: TIRExprId) -> TyId {
        let held = self.breaks.pop().unwrap_or_default();
        let mut ty = self.types.null();
        for found in held {
            match self.types.unify(ty, found) {
                Ok(one) => ty = one,
                Err(_) => {
                    let (ty, found) = (self.spell(ty), self.spell(found));
                    self.errors.push(
                        Diagnostic::error(
                            format!("one `break` gives `{}` and another `{}`", ty, found),
                            self.at(at),
                        )
                        .with_label("a loop is worth one type"),
                    );
                    return self.types.error();
                }
            }
        }
        ty
    }

    // What running through a thing hands out, one at a time.
    //
    // A closed set, and it has to be: the language has no trait with code
    // behind it, so there is no protocol for a library to answer and no way to
    // ask one. These are the sequences the language itself has -- and when a
    // protocol exists, this is the function that goes.
    fn elem_of(&mut self, ty: TyId) -> Option<TyId> {
        match self.types.get(ty).clone() {
            // "T[8]" owns and "T[]" is a run only a reference can hold.
            Ty::Array { elem, .. } | Ty::Run(elem) => Some(elem),
            // "A reference to a fixed array is a view of it" (§3), and a view
            // is what is run through.
            Ty::Ref { inner, .. } => self.elem_of(inner),
            Ty::Named { item, args, .. } => {
                let held = match &self.out.items[item].kind {
                    TTIRItemKind::Struct { name, .. } | TTIRItemKind::Enum { name, .. } => {
                        name.as_str()
                    }
                    _ => return None,
                };
                // A map is not here: it hands out a pair, and a `for` takes a
                // `<binding_name>` and not a pattern (§8), so there is nowhere
                // to put one.
                match held {
                    "Range" | "Set" | "HashSet" => args.first().copied(),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
