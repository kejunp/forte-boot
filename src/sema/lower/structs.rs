// `Point { x: 1, y: 2 }`, and what has to be true of it.
//
// A struct literal is the one expression that has to be checked against a
// declaration field by field, which is three separate questions: that every
// field the declaration wrote is filled, that no field was filled twice, and
// that none was filled that the declaration never wrote. Each has its own
// message, because "this literal is wrong" is not something a reader can act
// on.
//
// The fields come out in the order the declaration wrote them and not the
// order the literal did, so that everything below this pass can index a
// structure by number and never look at a name again.


use crate::error::Diagnostic;
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    // `Point { x: 1, y: 2 }`. The fields come out in the order they were
    // declared and not the order they were written -- "In declaration order,
    // whatever order they were written in" -- so everything below this reads
    // one shape whatever the writer chose.
    pub(super) fn struct_lit(
        &mut self,
        base: TIRExprId,
        written: &[crate::tir::tir_nodes::TIRFieldInit],
        at: TIRExprId,
    ) -> TTIRExprId {
        // The name in front of the brace is a declaration and not a value, so
        // it is looked up rather than typed.
        let TIRExprKind::Name(path) = self.tir.exprs[base].kind.clone() else {
            return self.not_yet("a struct literal whose head is not a name", at);
        };
        let Some(item) = self.names.get(&path.join("::")).copied() else {
            let name = path.join("::");
            self.errors.push(
                Diagnostic::error(format!("no type is called `{}`", name), self.at(base))
                    .with_label("nothing is declared under this name"),
            );
            return self.errored(at);
        };
        let TTIRItemKind::Struct { name, fields, .. } = &self.out.items[item].kind else {
            let name = path.join("::");
            self.errors.push(
                Diagnostic::error(format!("`{}` is not a struct", name), self.at(base))
                    .with_label("this is written as one")
                    .with_help("only a struct is built with a `{ .. }` after its name"),
            );
            return self.errored(at);
        };
        let declared: Vec<(String, TyId)> =
            fields.iter().map(|f| (f.name.clone(), f.ty)).collect();
        let held = name.clone();

        // Each written field put where its declaration stands.
        let mut placed: Vec<Option<TTIRExprId>> = vec![None; declared.len()];
        for field in written {
            let Some(index) = declared.iter().position(|(n, _)| *n == field.name) else {
                self.errors.push(
                    Diagnostic::error(
                        format!("`{}` has no field `{}`", held, field.name),
                        self.at(field.value),
                    )
                    .with_label("no such field"),
                );
                self.expr(field.value);
                continue;
            };
            let value = self.expr(field.value);
            let (found, want) = (self.out.exprs[value].ty, declared[index].1);
            if self.types.unify(found, want).is_err() {
                let (found, want) = (self.spell(found), self.spell(want));
                self.errors.push(
                    Diagnostic::error(
                        format!("`{}` is `{}` and the field is `{}`", field.name, found, want),
                        self.at(field.value),
                    )
                    .with_label("this is what is put there"),
                );
            }
            if placed[index].is_some() {
                self.errors.push(
                    Diagnostic::error(
                        format!("`{}` is given twice", field.name),
                        self.at(field.value),
                    )
                    .with_label("it was already given"),
                );
            }
            placed[index] = Some(value);
        }

        // A field nobody gave: a struct goes whole or not at all.
        let missing: Vec<&str> = declared
            .iter()
            .zip(placed.iter())
            .filter(|(_, given)| given.is_none())
            .map(|((name, _), _)| name.as_str())
            .collect();
        if !missing.is_empty() {
            let list = missing.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", ");
            self.errors.push(
                Diagnostic::error(format!("`{}` is not whole", held), self.at(at))
                    .with_label(format!("{} left out", list))
                    .with_help("a struct is built with every field it declares"),
            );
            return self.errored(at);
        }

        let fields: Vec<TTIRExprId> = placed.into_iter().flatten().collect();
        let regions = self.named_regions(item, &[], self.at(at));
        let ty = self.types.intern(Ty::Named { item, args: Vec::new(), regions });
        self.make(TTIRExprKind::StructLit { item, fields }, ty, at)
    }

    pub(super) fn errored(&mut self, at: TIRExprId) -> TTIRExprId {
        let ty = self.types.error();
        self.make(TTIRExprKind::Literal(TIRLit::Null), ty, at)
    }
}
