// Which types copy and which have something to release.
//
// Two questions, one table, and the table is worked out once for the whole
// program because both are asked of every type the walk meets. A move is only
// a move where the value does not copy, so `is_copy` is what stands between
// `let b = a` and a refusal; and a release is only placed where there is
// something to release, which is what `gir::drops` asks this the same
// question for one pass later.
//
// The answers reach past the two declarations that name them. A structure
// whose fields hold something to release has something to release, whether or
// not anybody wrote `impl Drop` for it, and a type that reaches itself is
// walked once and then remembered -- which is what `seen` is for.


use crate::tir::tir_nodes::{TIRBinding, TIRFnUses};
use crate::tir::ttir_nodes::{
    TTIRGeneric, TTIRItemId, TTIRItemKind,
    TTIRPayload, TTIRProgram, Ty, TyId,
};


// The two names the compiler knows, as it knows the six attributes. A type with
// an `impl Copy` copies where it would otherwise move; one with an `impl Drop`
// says what releasing it comes to, and §2 says a type may not have both.
pub struct Copies {
    copy: Vec<bool>,
    drop: Vec<bool>,
}

impl Copies {
    // Found by name: an `impl` whose trait is the item called `Copy` says its
    // type copies. Nothing else in the compiler resolves a trait by name, and
    // §2 is explicit that these two are known by theirs.
    pub fn of(p: &TTIRProgram) -> Copies {
        let mut copy = vec![false; p.items.len()];
        let mut drop = vec![false; p.items.len()];
        for item in &p.items {
            let TTIRItemKind::Impl { ty, of: Some(trait_item), .. } = &item.kind else {
                continue;
            };
            // The type it is written for, where that names a declaration: an
            // `impl Copy for i32` says nothing this needs, the primitives
            // copying without asking.
            let Ty::Named { item: named, .. } = &p.types[*ty] else { continue };
            match name_of(*trait_item, p).as_str() {
                "Copy" => copy[*named] = true,
                "Drop" => drop[*named] = true,
                _ => {}
            }
        }
        Copies { copy, drop }
    }

    // The body of every `Drop::drop`, by the id the graph gave it.
    //
    // A release inside one of these is what makes the glue recurse: the glue
    // for `T` calls `Drop::drop`, and `drop(self)` taking its receiver by
    // value means the receiver goes out of scope at the end of the body --
    // which places a release, which is the glue again. Nothing is left to
    // release there in any case: the glue runs the fields after the call, so
    // the receiver's parts are already accounted for.
    pub fn drop_bodies(p: &TTIRProgram) -> Vec<usize> {
        let mut out = Vec::new();
        for item in &p.items {
            let TTIRItemKind::Impl { of: Some(held), members, .. } = &item.kind else {
                continue;
            };
            if name_of(*held, p) != "Drop" {
                continue;
            }
            for &member in members {
                if let TTIRItemKind::Fn(f) = &p.items[member].kind {
                    if f.name == "drop" {
                        out.extend(f.body);
                    }
                }
            }
        }
        out
    }

    // Whether a value of this type has anything to release. An `impl Drop`
    // says so outright; a struct or an enum holding one says so because its
    // fields go when it does -- "a field when the value holding it goes" (§2).
    //
    // A `Ty::Param` is answered by whether it moves at all: what it turns out
    // to be is the caller's, and a fn is checked once for every caller there
    // will ever be. So anything that is not known to copy is treated as having
    // something to release, which costs a release that does nothing where it
    // has not.
    pub fn drops(&self, ty: TyId, p: &TTIRProgram, generics: &[TTIRGeneric]) -> bool {
        self.drops_past(ty, p, generics, &mut Vec::new())
    }

    fn drops_past(
        &self,
        ty: TyId,
        p: &TTIRProgram,
        generics: &[TTIRGeneric],
        seen: &mut Vec<TTIRItemId>,
    ) -> bool {
        match &p.types[ty] {
            // Nothing a primitive holds is anybody's to release, and what a
            // reference or a pointer refers to is owned somewhere else.
            // A trait object is only ever behind a reference, and what a
            // reference refers to is owned somewhere else -- so it is in this
            // list for the same reason the two beside it are.
            Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Run(_) | Ty::Dyn(_) => false,
            // A closure that took what it captured is holding it, and what it
            // holds goes when the closure does. Which types those were is not
            // in the fn type, so this is the blunt answer: a `once fn` has
            // something to release and the other two have not.
            Ty::Fn { uses, .. } => *uses == TIRFnUses::Takes,
            Ty::Named { item, args, .. } => {
                if self.drop[*item] {
                    return true;
                }
                if args.iter().any(|&a| self.drops_past(a, p, generics, seen)) {
                    return true;
                }
                if seen.contains(item) {
                    return false;
                }
                seen.push(*item);
                let held = match &p.items[*item].kind {
                    TTIRItemKind::Struct { fields, .. } => {
                        fields.iter().any(|f| self.drops_past(f.ty, p, generics, seen))
                    }
                    TTIRItemKind::Enum { variants, .. } => {
                        variants.iter().any(|v| match &v.payload {
                            TTIRPayload::None => false,
                            TTIRPayload::Tuple(tys) => {
                                tys.iter().any(|&t| self.drops_past(t, p, generics, seen))
                            }
                            TTIRPayload::Named(fields) => {
                                fields.iter().any(|f| self.drops_past(f.ty, p, generics, seen))
                            }
                        })
                    }
                    _ => false,
                };
                seen.pop();
                held
            }
            Ty::Array { elem, .. } => self.drops_past(*elem, p, generics, seen),
            // Nothing releases one where it stands: what the collector holds,
            // the collector releases, which is the whole of what a `gc` is
            // instead of a scope. How that meets a written `Drop` is the half
            // of §8's question this does not answer.
            Ty::GC(_) => false,
            Ty::Tuple(members) => {
                members.iter().any(|&m| self.drops_past(m, p, generics, seen))
            }
            Ty::Param { .. } => !self.is_copy(ty, p, generics),
            Ty::Var(_) | Ty::Error => false,
        }
    }

    // Whether a value of this type is copied where it is handed over, rather
    // than moved out of where it was.
    //
    //     The primitives copy without asking, and so do `null`, a reference,
    //     and a fixed array or tuple every part of which copies; everything
    //     else moves until it says otherwise.                            (§2)
    // `generics` is the declaration the type stands in, which a `Ty::Param`
    // needs: it names its parameter by place, and whose list that is is not in
    // the type. An empty list answers `false` for one, which is the half that
    // turns more down.
    pub fn is_copy(&self, ty: TyId, p: &TTIRProgram, generics: &[TTIRGeneric]) -> bool {
        match &p.types[ty] {
            // `null` is among the primitives, and is in the list by name too.
            Ty::Prim(_) => true,
            // A reference copies; what it refers to is owned somewhere else.
            // So does a `gc` value, and for exactly that reason: the collector
            // owns what is at the far end, and the word in hand is an address
            // like any other. §8 asked "whether a `gc` binding may be moved
            // out of or handed to a function", and this is the answer -- it is
            // handed over as a reference is, and a binding it was handed from
            // still holds it. Moving instead would make a collected value one
            // that could be used once, which is worse than a reference and not
            // what a collector is for.
            Ty::Ref { .. } | Ty::Ptr(_) | Ty::GC(_) => true,
            // Nothing holds a bare one, so nothing copies or moves one: what
            // copies is the reference in front of it, which is above.
            Ty::Dyn(_) => false,
            // A closure copies where calling it does nothing to what it
            // captured. A `once fn` gives away what it holds when it is
            // called, so it has one owner and one call like any other value
            // that moves -- which is what makes the second call a use of
            // something that has gone, and needs no rule of its own.
            Ty::Fn { uses, .. } => *uses != TIRFnUses::Takes,

            Ty::Named { item, .. } => self.copy[*item],

            // "An array copies exactly when its element does, so an `i32[8]`
            // copies and a `Buf[8]` moves" (§3).
            Ty::Array { elem, .. } => self.is_copy(*elem, p, generics),
            // A run is only ever reached behind a reference, and the reference
            // is what is handed over.
            Ty::Run(_) => true,
            // "copying where every member copies and moving otherwise" (§3).
            Ty::Tuple(members) => members.iter().all(|&m| self.is_copy(m, p, generics)),

            // A parameter copies where it was declared to. `<T: Copy>` is how a
            // fn says so, and the bound is the only thing that can say it: what
            // `T` turns out to be is the caller's, and a fn is checked once for
            // every caller there will ever be.
            Ty::Param { index, .. } => match generics.get(*index) {
                Some(TTIRGeneric::Type { bounds, .. }) => bounds.iter().any(|bound| {
                    let crate::tir::ttir_nodes::TTIRBound::Trait(held) = bound else {
                        return false;
                    };
                    matches!(&p.types[*held], Ty::Named { item, .. } if name_of(*item, p) == "Copy")
                }),
                _ => false,
            },


            // Neither says anything, and a type nobody worked out has already
            // been reported once.
            Ty::Var(_) | Ty::Error => true,
        }
    }

    pub fn is_drop(&self, item: TTIRItemId) -> bool {
        self.drop[item]
    }

    // "A type cannot have both a `Copy` and a `Drop`: a value that has
    // something to release is a value there had better be one of" (§2).
    pub fn both(&self) -> Vec<TTIRItemId> {
        (0..self.copy.len()).filter(|&i| self.copy[i] && self.drop[i]).collect()
    }
}

// What an item is called. `sema::names` has one of these and it is private to
// that module; a trait is asked its name in one place here and the two are the
// same question.
// `pub(crate)` for `gir::drops`, which has the same question about the same
// two names: an `impl Drop` is found by the name of the trait it is written
// for and by nothing else, here and there alike.
pub(crate) fn name_of(id: TTIRItemId, p: &TTIRProgram) -> String {
    match &p.items[id].kind {
        TTIRItemKind::Fn(f) => f.name.clone(),
        TTIRItemKind::Struct { name, .. }
        | TTIRItemKind::Enum { name, .. }
        | TTIRItemKind::Trait { name, .. }
        | TTIRItemKind::Namespace { name, .. }
        | TTIRItemKind::TypeAlias { name, .. }
        | TTIRItemKind::Const { name, .. } => name.clone(),
        TTIRItemKind::Global { name: TIRBinding::Name(name), .. } => name.clone(),
        _ => String::new(),
    }
}
