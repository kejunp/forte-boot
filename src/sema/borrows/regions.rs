// How long a thing is good for, checked where it is used.
//
// This is the half of the pass the prose in `borrows.rs` is about when it says
// there is no second frame and no constraint solver:
//
//     What the rule costs is precision, and it spends it at the call rather
//     than at the declaration ... the program that cannot be proved is turned
//     down where it is used and not where the thing that could not be proved
//     was written.                                      (docs/prose.txt, §3)
//
// So what is here is not an inference. A signature says which of its
// parameters its result is tied to; a call says what was handed to each of
// them; and the check is that what comes back does not outlive what went in.
// The bounds a declaration wrote -- a `'a: 'b`, a `T: 'a` -- are promises the
// *caller* keeps, so they are held to at the call as well, which is what
// `bounds_at_call` is.
//
// The names are for the message. A region has no name of its own until
// somebody wrote one, and a refusal that cannot say which `'a` it means is a
// refusal nobody can act on.

use std::collections::HashMap;

use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::TIRUnaryOp;
use crate::tir::ttir_nodes::{
    RegionId, TTIRBound, TTIRCaptureMode, TTIRExprId, TTIRExprKind, TTIRGeneric, TTIRItemId, TTIRItemKind, TTIRLocalId, TTIRSubject, Ty, TyId,
};

use super::copies::name_of;
use super::Checker;

impl<'a> Checker<'a> {
    // Which of a fn's parameters its result is tied to, or `None` where its
    // result is tied to nothing because it gives back no reference.
    //
    // This is the other half of the bargain §3 strikes. The declaration was
    // never refused for want of a lifetime -- every reference in it got a
    // region and the return was held to all of them -- and here is where that
    // is paid for: a caller is held to every parameter the return's region can
    // be reached from. Writing `'a` is what buys the precision back, and it
    // buys it exactly here, by leaving a parameter out of this list.
    pub(super) fn tied(&self, item: TTIRItemId) -> Option<Vec<usize>> {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return None };
        let mut reach = Vec::new();
        self.regions_in(f.ret, &mut reach);
        if reach.is_empty() {
            // A named type carries references without carrying their regions:
            // `Ty::Named` holds types, and a `Held<'a>` loses the `'a` on the
            // way in. So the regions cannot be compared and the answer is the
            // one the elision rule would have given before anybody wrote a
            // lifetime -- tied to everything, which is never wrong and is what
            // §3 means by spending precision at the call.
            if self.holds_ref(f.ret) {
                let Ty::Fn { params, .. } = &self.p.types[f.ty] else { return None };
                return Some((0..params.len()).collect());
            }
            return None;
        }
        // Everything that outlives something already reached, until nothing
        // more is. A `(longer, shorter)` pair says the caller has to make
        // `longer` last at least as long, so `longer` is one more region the
        // result stands or falls with.
        loop {
            let grown: Vec<RegionId> = f
                .outlives
                .iter()
                .filter(|(longer, shorter)| reach.contains(shorter) && !reach.contains(longer))
                .map(|&(longer, _)| longer)
                .collect();
            if grown.is_empty() {
                break;
            }
            reach.extend(grown);
        }
        let Ty::Fn { params, .. } = &self.p.types[f.ty] else { return None };
        Some(
            params
                .iter()
                .enumerate()
                .filter(|(_, p)| {
                    let mut held = Vec::new();
                    self.regions_in(**p, &mut held);
                    held.iter().any(|r| reach.contains(r))
                })
                .map(|(i, _)| i)
                .collect(),
        )
    }

    // ---- Bounds at the call ----------------------------------------------
    //
    //     Too conservative a signature is turned down at the call and not at
    //     the declaration.                                (docs/prose.txt, §3)
    //
    // A `'a: 'b` and a `T: 'a` say nothing a declaration can be refused for --
    // they are what a *caller* is held to. So they are checked here, and what
    // they are checked against is a region substitution: what each of the
    // callee's regions stands for on this side, worked out from what was handed
    // to the parameters it appears in.
    //
    // A caller-side lifetime is a depth, the same ordering everything else in
    // this pass uses, and 0 means "came from outside and outlives the body".

    // What one callee region or type parameter was handed: how long the value
    // is good for, and the slot that made it so, for the message.
    fn supplied(
        &self,
        declared: TyId,
        held: (usize, Option<TTIRLocalId>),
        regions: &mut HashMap<RegionId, (usize, Option<TTIRLocalId>)>,
        params: &mut HashMap<usize, (usize, Option<TTIRLocalId>)>,
    ) {
        // The shortest life wins: a region standing in two places is good for
        // no longer than the shorter of them.
        let keep = |at: &mut HashMap<_, (usize, Option<TTIRLocalId>)>, key| {
            let entry = at.entry(key).or_insert(held);
            if held.0 > entry.0 {
                *entry = held;
            }
        };
        match &self.p.types[declared] {
            Ty::Ref { life, inner, .. } => {
                if *life != 0 {
                    keep(regions, *life);
                }
                self.supplied(*inner, held, regions, params);
            }
            Ty::Named { args, regions: rs, .. } => {
                for &r in rs {
                    if r != 0 {
                        keep(regions, r);
                    }
                }
                for &a in args {
                    self.supplied(a, held, regions, params);
                }
            }
            Ty::Param { index, .. } => keep(params, *index),
            Ty::Tuple(members) => {
                for &m in members {
                    self.supplied(m, held, regions, params);
                }
            }
            Ty::Array { elem, .. } | Ty::Run(elem) => {
                self.supplied(*elem, held, regions, params)
            }
            Ty::Ptr(inner) | Ty::GC(inner) => self.supplied(*inner, held, regions, params),
            Ty::Fn { params: ps, ret, .. } => {
                let (ps, ret) = (ps.clone(), *ret);
                for p in ps {
                    self.supplied(p, held, regions, params);
                }
                self.supplied(ret, held, regions, params);
            }
            _ => {}
        }
    }

    // Which borrows taken working a value out get as far as the value. The
    // same walk `roots` is, asking the other half of the question: `roots` says
    // what a value points into, and this says which `&` put it there.
    //
    // What it turns on at a call is the callee's own signature -- `len(&x)`
    // gives back an `i32` and can hold nothing, so the `&x` is a temporary and
    // goes with the statement; `pick(&x, &y)` gives back a reference tied to
    // both, so both get as far as whatever the result is bound to.
    pub(super) fn reaching(&self, id: TTIRExprId) -> Vec<TTIRExprId> {
        let mut out = Vec::new();
        self.walk_reaching(id, &mut out);
        out
    }

    fn walk_reaching(&self, id: TTIRExprId, out: &mut Vec<TTIRExprId>) {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), .. } => out.push(id),
            // A closure holds what it captured by reference for as long as it
            // is in hand, so the closure is what took those borrows.
            TTIRExprKind::Closure { captures, .. } => {
                if captures.iter().any(|c| matches!(c.mode, TTIRCaptureMode::Ref(_))) {
                    out.push(id);
                }
            }
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.walk_reaching(*base, out),
            TTIRExprKind::Cast(inner) => self.walk_reaching(*inner, out),
            TTIRExprKind::Call { callee, args } => match self.callee(*callee).map(|i| self.tied(i)) {
                Some(None) => {}
                Some(Some(ties)) => {
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&i) {
                            self.walk_reaching(arg, out);
                        }
                    }
                }
                None => {
                    for &arg in args {
                        self.walk_reaching(arg, out);
                    }
                }
            },
            TTIRExprKind::Method { recv, item, args } => {
                if let Some(ties) = self.tied(*item) {
                    if ties.contains(&0) {
                        self.walk_reaching(*recv, out);
                    }
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&(i + 1)) {
                            self.walk_reaching(arg, out);
                        }
                    }
                }
            }
            TTIRExprKind::ArrayLit(parts)
            | TTIRExprKind::TupleLit(parts)
            | TTIRExprKind::StructLit { fields: parts, .. }
            | TTIRExprKind::VariantLit { fields: parts, .. }
            | TTIRExprKind::Set { elems: parts, .. } => {
                for &part in parts {
                    self.walk_reaching(part, out);
                }
            }
            TTIRExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.walk_reaching(key, out);
                    self.walk_reaching(value, out);
                }
            }
            TTIRExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.walk_reaching(*held, out);
                }
            }
            TTIRExprKind::Block { tail, .. } => {
                if let Some(tail) = tail {
                    self.walk_reaching(*tail, out);
                }
            }
            TTIRExprKind::If { then, els, .. } => {
                self.walk_reaching(*then, out);
                if let Some(els) = els {
                    self.walk_reaching(*els, out);
                }
            }
            TTIRExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.walk_reaching(arm.body, out);
                }
            }
            _ => {}
        }
    }

    // What a parameter's regions were handed, worked out against the argument
    // as it was written. A `(&'a i32, &'b i32)` given a tuple written on the
    // spot answers for each half on its own; anything this cannot take apart
    // answers for the argument whole, which is the blunt end of the same rule.
    fn supplied_from(
        &self,
        declared: TyId,
        arg: TTIRExprId,
        regions: &mut HashMap<RegionId, (usize, Option<TTIRLocalId>)>,
        params: &mut HashMap<usize, (usize, Option<TTIRLocalId>)>,
    ) {
        // A block stands for its tail and a cast for what it casts.
        let arg = match &self.p.exprs[arg].kind {
            TTIRExprKind::Cast(inner) => *inner,
            TTIRExprKind::Block { tail: Some(tail), .. } => *tail,
            _ => arg,
        };
        match (&self.p.types[declared], &self.p.exprs[arg].kind) {
            (Ty::Tuple(members), TTIRExprKind::TupleLit(parts))
                if members.len() == parts.len() =>
            {
                let (members, parts) = (members.clone(), parts.clone());
                for (want, part) in members.iter().zip(parts.iter()) {
                    self.supplied_from(*want, *part, regions, params);
                }
            }
            (Ty::Array { elem, .. }, TTIRExprKind::ArrayLit(parts)) => {
                let (elem, parts) = (*elem, parts.clone());
                for part in parts {
                    self.supplied_from(elem, part, regions, params);
                }
            }
            _ => self.supplied(declared, self.handed(arg), regions, params),
        }
    }

    // How long an argument's value is good for, and the slot that says so.
    fn handed(&self, arg: TTIRExprId) -> (usize, Option<TTIRLocalId>) {
        let mut worst = (0, None);
        for (root, _) in self.roots(arg) {
            let lives = self.lives(root);
            if lives >= worst.0 {
                worst = (lives, Some(root));
            }
        }
        worst
    }

    // The same, for a receiver a method borrows rather than takes. `&'a self`
    // is the one borrow nobody writes, so the region stands for how long the
    // receiver itself is good for and not for what it points into.
    pub(super) fn handed_borrowed(&self, recv: TTIRExprId) -> (usize, Option<TTIRLocalId>) {
        match self.place(recv) {
            Some(place) => (self.lives(place.root), Some(place.root)),
            // A receiver with no place of its own is a value the compiler gave
            // one, and one it gave lasts as long as the call.
            None => self.handed(recv),
        }
    }

    // Every bound a signature was written with, held against what this call
    // handed it. `given` is the arguments in declaration order, the receiver
    // standing where parameter 0 does.
    pub(super) fn bounds_at_call(
        &mut self,
        item: TTIRItemId,
        given: &[Handed],
        at: Span,
    ) {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return };
        let (generics, wheres) = (f.generics.clone(), f.wheres.clone());
        if generics.iter().all(|g| bounds_none(g)) && wheres.is_empty() {
            return;
        }
        let Ty::Fn { params: declared, .. } = &self.p.types[f.ty] else { return };
        let declared = declared.clone();

        let mut regions = HashMap::new();
        let mut params = HashMap::new();
        for (i, held) in given.iter().enumerate() {
            let Some(&want) = declared.get(i) else { continue };
            match held {
                // Taken apart where it was written as one thing built out of
                // several, so each region answers for its own half.
                Handed::Written(arg) => {
                    self.supplied_from(want, *arg, &mut regions, &mut params)
                }
                Handed::Whole(held) => self.supplied(want, *held, &mut regions, &mut params),
            }
        }

        // A region nothing was handed is one the caller may pick freely, and
        // the freest pick is the longest life. So: outlives everything.
        let of_region = |r: RegionId| regions.get(&r).copied().unwrap_or((0, None));

        let mut asked: Vec<(String, (usize, Option<TTIRLocalId>), RegionId)> = Vec::new();
        // A `Ty::Param` counts in the type parameters alone, so the position
        // among them is what a `T: 'a` is looked up by and not the position in
        // the list as written.
        let mut i = 0;
        for g in generics.iter() {
            match g {
                // `'a: 'b`, written among the parameters.
                TTIRGeneric::Life { name, region, bounds } => {
                    for &shorter in bounds {
                        asked.push((format!("`'{}`", name), of_region(*region), shorter));
                    }
                }
                // `T: 'a`. What T was handed is what has to outlive the region.
                TTIRGeneric::Type { name, bounds } => {
                    for bound in bounds {
                        if let TTIRBound::Life(shorter) = bound {
                            let held = params.get(&i).copied().unwrap_or((0, None));
                            asked.push((format!("`{}`", name), held, *shorter));
                        }
                    }
                    i += 1;
                }
            }
        }
        for pred in &wheres {
            // A predicate about a parameter was folded into that parameter's
            // bounds; what is left is a region or a type that was built.
            let held = match &pred.subject {
                TTIRSubject::Region(r) => {
                    (format!("`'{}`", self.life_name(&generics, *r)), of_region(*r))
                }
                TTIRSubject::Type(ty) => {
                    let mut regions_in = HashMap::new();
                    let mut params_in = HashMap::new();
                    self.supplied(*ty, (0, None), &mut regions_in, &mut params_in);
                    let worst = regions_in
                        .keys()
                        .map(|r| of_region(*r))
                        .chain(params_in.keys().map(|i| params.get(i).copied().unwrap_or((0, None))))
                        .max_by_key(|(lives, _)| *lives)
                        .unwrap_or((0, None));
                    (self.spell_subject(*ty), worst)
                }
            };
            for bound in &pred.bounds {
                if let TTIRBound::Life(shorter) = bound {
                    asked.push((held.0.clone(), held.1, *shorter));
                }
            }
        }

        for (what, (lives, blame), shorter) in asked {
            let (wanted, against) = of_region(shorter);
            // Longer-lived is a smaller depth. A bound that holds is one where
            // what was handed to the left outlives what was handed to the right.
            if lives <= wanted {
                continue;
            }
            let named = format!("`'{}`", self.life_name(&generics, shorter));
            let mut said = Diagnostic::error(
                format!("{} does not outlive {}", what, named),
                at,
            )
            .with_label("this call is where it has to");
            if let Some(blame) = blame {
                let local = &self.p.bodies[self.body].locals[blame];
                said = said.with_secondary(
                    Span::at(local.line, local.col),
                    format!("{} was handed this", what),
                );
            }
            if let Some(against) = against {
                let local = &self.p.bodies[self.body].locals[against];
                said = said.with_secondary(
                    Span::at(local.line, local.col),
                    format!("{} was handed this, which lasts longer", named),
                );
            }
            self.say(
                said.with_note(format!(
                    "the signature says {} outlives {}",
                    what, named
                ))
                .with_help("a bound is a promise the caller keeps, so what is handed in has to keep it"),
            );
        }
    }

    // What a region is called in the declaration that declared it.
    fn life_name(&self, generics: &[TTIRGeneric], region: RegionId) -> String {
        for g in generics {
            if let TTIRGeneric::Life { name, region: held, .. } = g {
                if *held == region {
                    return name.clone();
                }
            }
        }
        // A region with no name is one the rule made, and the rule makes one
        // per reference -- so this is a reference the reader did not name.
        "_".to_string()
    }

    fn spell_subject(&self, ty: TyId) -> String {
        match &self.p.types[ty] {
            Ty::Named { item, .. } => format!("`{}`", name_of(*item, self.p)),
            Ty::Param { name, .. } => format!("`{}`", name),
            _ => "what this `where` is about".to_string(),
        }
    }

    // The item a callee expression names, where it names one. A call through a
    // closure or a fn held in a variable names none, and then nothing is known
    // about what its result is tied to.
    pub(super) fn callee(&self, id: TTIRExprId) -> Option<TTIRItemId> {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Item(item) => Some(*item),
            _ => None,
        }
    }
}

// What a call handed one parameter: the expression, where there is one to take
// apart, and how long it lasts where there is not -- a method's receiver being
// borrowed rather than handed over, and the borrow lasting as long as the
// receiver itself.
pub(super) enum Handed {
    Written(TTIRExprId),
    Whole((usize, Option<TTIRLocalId>)),
}

// A parameter holding no region bound: `T: Show` is a trait's business and
// `<T>` on its own is nobody's, and neither is a promise a caller keeps.
fn bounds_none(g: &TTIRGeneric) -> bool {
    match g {
        TTIRGeneric::Life { bounds, .. } => bounds.is_empty(),
        TTIRGeneric::Type { bounds, .. } => {
            !bounds.iter().any(|b| matches!(b, TTIRBound::Life(_)))
        }
    }
}
