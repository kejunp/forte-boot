// What a type holds, as far as a reference is concerned.
//
// Four questions asked of a `TyId` and nothing else, which is what makes them
// worth having together: none of them looks at an expression, a place or the
// walk's state, so none of them can be wrong about *where* -- only about what
// a type is made of.
//
// They are what decides whether a rule has anything to ask at all. A value
// with no reference in it cannot outstay anything and cannot point anywhere,
// so `holds_ref` standing at the top of a check is what keeps the expensive
// half of this pass off the programs that do not need it.
//
// A declaration that reaches itself has no finite number of regions and is
// given nought, which is the header's second bullet: `holds_ref` still sees
// the reference, so what comes of one is held to every parameter -- the
// elision rule's own answer, and never wrong.


use crate::tir::ttir_nodes::{
    RegionId, TTIRItemId, TTIRItemKind,
    TTIRPayload, Ty, TyId,
};

use super::Checker;

impl<'a> Checker<'a> {
    // Does this type hold a reference standing in a region of the signature?
    // Region 0 is what a reference in a body gets, where how long it is good
    // for was nobody's question -- so it does not count.
    pub(super) fn holds_ref(&self, ty: TyId) -> bool {
        self.holds_ref_past(ty, true, &mut Vec::new())
    }

    // The same question asked of a closure's result rather than a signature's.
    // Every reference a body takes stands in region 0 -- how long one held in a
    // local is good for is not what a signature promises -- so `holds_ref` can
    // see none of them, and what a closure gives back is worked out in a body.
    pub(super) fn holds_any_ref(&self, ty: TyId) -> bool {
        self.holds_ref_past(ty, false, &mut Vec::new())
    }

    // `seen` is the declarations already being looked through. A struct cannot
    // hold itself by value, so a cycle is not reachable today -- but this walks
    // declarations rather than types, and a walk over declarations that cannot
    // be stopped is a hang waiting for a language change.
    fn holds_ref_past(&self, ty: TyId, signature: bool, seen: &mut Vec<TTIRItemId>) -> bool {
        match &self.p.types[ty] {
            Ty::Ref { life, inner, .. } => {
                (!signature || *life != 0) || self.holds_ref_past(*inner, signature, seen)
            }
            // A named type holds a reference where what it was declared to hold
            // does. The regions are the declaration's and not the use's -- a
            // `Held` written bare carries the same reference a `Held<'a>` does,
            // and it is the declaration that says so.
            Ty::Named { item, args, .. } => {
                if args.iter().any(|&a| self.holds_ref_past(a, signature, seen)) {
                    return true;
                }
                if seen.contains(item) {
                    return false;
                }
                seen.push(*item);
                let held = match &self.p.items[*item].kind {
                    TTIRItemKind::Struct { fields, .. } => {
                        fields.iter().any(|f| self.holds_ref_past(f.ty, signature, seen))
                    }
                    TTIRItemKind::Enum { variants, .. } => {
                        variants.iter().any(|v| match &v.payload {
                            TTIRPayload::None => false,
                            TTIRPayload::Tuple(tys) => {
                                tys.iter().any(|&t| self.holds_ref_past(t, signature, seen))
                            }
                            TTIRPayload::Named(fields) => {
                                fields.iter().any(|f| self.holds_ref_past(f.ty, signature, seen))
                            }
                        })
                    }
                    _ => false,
                };
                seen.pop();
                held
            }
            // A fn type says nothing about what a closure behind it captured,
            // so the question cannot be answered here and is left to the value:
            // `roots` returns nothing for a `move` closure or a plain fn, and
            // what it returns for one that captured by reference is what this
            // would have wanted to know.
            Ty::Fn { .. } => true,
            Ty::Tuple(members) => members.iter().any(|&m| self.holds_ref_past(m, signature, seen)),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.holds_ref_past(*elem, signature, seen),
            Ty::GC(inner) => self.holds_ref_past(*inner, signature, seen),
            _ => false,
        }
    }

    // Every region standing anywhere in a type.
    pub(super) fn regions_in(&self, ty: TyId, out: &mut Vec<RegionId>) {
        match &self.p.types[ty] {
            Ty::Ref { life, inner, .. } => {
                if *life != 0 && !out.contains(life) {
                    out.push(*life);
                }
                self.regions_in(*inner, out);
            }
            Ty::Tuple(members) => {
                for &m in members {
                    self.regions_in(m, out);
                }
            }
            Ty::Array { elem, .. } | Ty::Run(elem) => self.regions_in(*elem, out),
            Ty::Ptr(inner) | Ty::GC(inner) => self.regions_in(*inner, out),
            Ty::Named { args, regions, .. } => {
                for &r in regions {
                    if r != 0 && !out.contains(&r) {
                        out.push(r);
                    }
                }
                for &a in args {
                    self.regions_in(a, out);
                }
            }
            _ => {}
        }
    }
}
