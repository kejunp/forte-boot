// Types: the arena every `TyId` points into, and the rules over it.
//
// `names` says what a name is and `scopes` says where to find it; this says
// what agrees with what. It is the half of the checker that has no opinion
// about the tree -- hand it two types and it will tell you whether they can be
// one type, and which -- so the pass that walks a TIR and emits a TTIR can be
// written against it without either knowing the other's shape.
//
// Three things it owns:
//
//   - The arena, which becomes `TTIRProgram::types`. Interned: two `i32`s are
//     one entry, so a handle comparison is a type comparison and the checker
//     never walks a type to ask whether it is the same as another.
//   - The holes. Inference builds a type before it knows all of it -- a
//     `Vec<_>` whose element is settled by what is put in it -- and a hole is a
//     `Ty::Var` that some later unification fills. `finish` is where any that
//     were never filled become an `Error` with a message against them.
//   - Two rules the language has that most do not, both of them section 3's.
//     `never` agrees with anything: it has no values, so there is nothing it
//     could disagree about, and `match c { 1 => 5, _ => panic("no") }` is an
//     i32. `null` belongs to every type: section 8 calls that the billion-dollar
//     bet and settles it, so a loop that nobody broke out of agrees with the
//     `break x` that would have.
//
//     The second of those is written down twice in the prose and not the same
//     way twice -- section 3 says a `null` arm beside an i32 arm "would be an
//     error", section 8 says every type admits one. What is implemented here is
//     section 8, being the one marked settled. `null_belongs` is the one place
//     it is decided, so the other reading is a line's worth of change.

// The checker that drives this is the pass still to write; until it exists the
// arena is filled by tests and by nothing else. The allow is for that.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::tir::tir_nodes::TIRFnUses;
use crate::tir::tir_nodes::TIRPrim;
use crate::tir::ttir_nodes::{TTIRItemId, Ty, TyId, VarId};

// Whether a `null` may stand where another type is wanted. See the note above:
// section 8 settles that it may, and this is where that is decided.
const NULL_BELONGS: bool = true;

// Two types that will not be one, innermost first: `Vec<i32>` against
// `Vec<str>` reports the `i32` and the `str`, since that is the disagreement
// and the rest is the same on both sides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Mismatch {
    pub found:  TyId,
    pub wanted: TyId,
}

// What may fill a hole. Most take anything; a number's takes numbers, which is
// what lets `let x: i64 = 5` put an i64 there and `if 5` be refused. Without
// the distinction a literal is either too fixed to be put anywhere or too free
// to be refused anywhere, and neither is what a reader means by `5`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fills {
    Anything,
    // `5`: any of the twelve numeric primitives, and `i32` where nothing says
    // otherwise -- which is the one place this guesses rather than works out.
    Whole,
    // `5.0`: the two floats, and `f64` by default.
    Fractional,
}

pub struct Types {
    arena: Vec<Ty>,
    // What is already in the arena, so an equal type is an equal handle.
    index: HashMap<Ty, TyId>,
    // What each hole was filled with, or `None` while it is still a hole.
    vars:  Vec<Option<TyId>>,
    // What each hole will take.
    fills: Vec<Fills>,
}

impl Types {
    pub fn new() -> Types {
        Types { arena: Vec::new(), index: HashMap::new(), vars: Vec::new(), fills: Vec::new() }
    }

    // ---- The arena -------------------------------------------------------

    // `ty`'s handle, which is the one it already had if it has been here
    // before. That is the whole of what interning buys: `a == b` on handles.
    pub fn intern(&mut self, ty: Ty) -> TyId {
        if let Some(&id) = self.index.get(&ty) {
            return id;
        }
        self.arena.push(ty.clone());
        let id = self.arena.len() - 1;
        self.index.insert(ty, id);
        id
    }

    pub fn get(&self, id: TyId) -> &Ty {
        &self.arena[id]
    }

    pub fn len(&self) -> usize {
        self.arena.len()
    }

    pub fn is_empty(&self) -> bool {
        self.arena.is_empty()
    }

    pub fn prim(&mut self, prim: TIRPrim) -> TyId {
        self.intern(Ty::Prim(prim))
    }

    pub fn null(&mut self) -> TyId {
        self.prim(TIRPrim::Null)
    }

    pub fn never(&mut self) -> TyId {
        self.prim(TIRPrim::Never)
    }

    pub fn error(&mut self) -> TyId {
        self.intern(Ty::Error)
    }

    // ---- Holes -----------------------------------------------------------

    // A type not worked out yet. Handed back as a `TyId` like any other, so
    // nothing downstream has to know whether it is looking at one.
    pub fn fresh(&mut self) -> TyId {
        self.hole(Fills::Anything)
    }

    // A hole a number goes in. What an unsuffixed literal is: `5` is not an
    // `i32` until something says so, and it is never a `str`.
    pub fn fresh_whole(&mut self) -> TyId {
        self.hole(Fills::Whole)
    }

    pub fn fresh_fractional(&mut self) -> TyId {
        self.hole(Fills::Fractional)
    }

    fn hole(&mut self, fills: Fills) -> TyId {
        self.vars.push(None);
        self.fills.push(fills);
        let var = self.vars.len() - 1;
        self.intern(Ty::Var(var))
    }

    // `id` with any filled hole at the top followed. Shallow on purpose: what
    // `unify` needs is the outermost shape, and following further would build
    // types nobody asked for.
    pub fn shallow(&self, id: TyId) -> TyId {
        let mut here = id;
        while let Ty::Var(var) = self.arena[here] {
            match self.vars[var] {
                Some(filled) => here = filled,
                None => return here,
            }
        }
        here
    }

    // `id` with every hole in it followed, all the way down. What `finish` and
    // a diagnostic want, and what `unify` deliberately does not.
    pub fn deep(&mut self, id: TyId) -> TyId {
        let here = self.shallow(id);
        let rebuilt = match self.arena[here].clone() {
            Ty::Var(_) | Ty::Prim(_) | Ty::Param { .. } | Ty::Error => return here,
            Ty::Named { item, args, regions } => Ty::Named {
                item,
                args: args.iter().map(|&a| self.deep(a)).collect(),
                regions,
            },
            Ty::Ref { op, life, inner } => Ty::Ref { op, life, inner: self.deep(inner) },
            Ty::Ptr(inner) => Ty::Ptr(self.deep(inner)),
            Ty::GC(inner) => Ty::GC(self.deep(inner)),
            Ty::Array { elem, len } => Ty::Array { elem: self.deep(elem), len },
            Ty::Run(elem) => Ty::Run(self.deep(elem)),
            Ty::Tuple(members) => {
                Ty::Tuple(members.iter().map(|&m| self.deep(m)).collect())
            }
            Ty::Fn { uses, params, ret, is_unsafe } => Ty::Fn {
                uses,
                params: params.iter().map(|&p| self.deep(p)).collect(),
                ret: self.deep(ret),
                is_unsafe,
            },
        };
        self.intern(rebuilt)
    }

    // Whether `var` is somewhere inside `id`. Without this, `T = Vec<T>` fills
    // a hole with a type that holds the hole, and every walk of it afterwards
    // runs forever.
    fn occurs(&self, var: VarId, id: TyId) -> bool {
        let here = self.shallow(id);
        match &self.arena[here] {
            Ty::Var(found) => *found == var,
            Ty::Named { args, .. } => args.iter().any(|&a| self.occurs(var, a)),
            Ty::Ref { inner, .. } | Ty::Ptr(inner) | Ty::GC(inner) => self.occurs(var, *inner),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.occurs(var, *elem),
            Ty::Tuple(members) => members.iter().any(|&m| self.occurs(var, m)),
            Ty::Fn { params, ret, .. } => {
                params.iter().any(|&p| self.occurs(var, p)) || self.occurs(var, *ret)
            }
            Ty::Prim(_) | Ty::Param { .. } | Ty::Error => false,
        }
    }

    // ---- Agreeing --------------------------------------------------------

    // The one type `found` and `wanted` both are, or what disagreed. Fills a
    // hole where one stands, which is the whole of how a type is inferred:
    // nothing here decides what a thing is, and everything here decides what a
    // thing has to be to sit where it was put.
    pub fn unify(&mut self, found: TyId, wanted: TyId) -> Result<TyId, Mismatch> {
        let a = self.shallow(found);
        let b = self.shallow(wanted);
        if a == b {
            return Ok(a);
        }

        // One mistake is one message: an `Error` agrees with anything so that
        // what was already reported does not report again further out.
        if matches!(self.arena[a], Ty::Error) || matches!(self.arena[b], Ty::Error) {
            return Ok(self.error());
        }

        // `never` has no values, so it has nothing to disagree about, and the
        // other side is what the pair is worth.
        //
        // Asked before the holes: `match c { 1 => 5, _ => panic() }` is worth
        // what the `5` is, and a hole that took `never` instead would make the
        // whole thing `never`.
        if self.is(a, TIRPrim::Never) {
            return Ok(b);
        }
        if self.is(b, TIRPrim::Never) {
            return Ok(a);
        }

        // A hole becomes whatever was put in it.
        //
        // Asked before `null` and not after, which is the other half of the
        // same care: `null` belongs to every type, so a hole meeting one and
        // nothing else *is* a `null` -- and a hole left open would be a type
        // the checker never worked out rather than one it did.
        if let Ty::Var(var) = self.arena[a] {
            return self.fill(var, b);
        }
        if let Ty::Var(var) = self.arena[b] {
            return self.fill(var, a);
        }

        // "`null` belongs to every type" (section 8): the billion-dollar bet,
        // taken in `NULL_BELONGS` and spent here.
        if NULL_BELONGS && self.is(a, TIRPrim::Null) {
            return Ok(b);
        }
        if NULL_BELONGS && self.is(b, TIRPrim::Null) {
            return Ok(a);
        }

        match (self.arena[a].clone(), self.arena[b].clone()) {
            (Ty::Prim(x), Ty::Prim(y)) if x == y => Ok(a),

            // The regions are not unified, for the same reason a `Ref`'s is
            // not: how long a thing is good for is a pass of its own, and a
            // type that agrees but for its regions is a type that agrees. The
            // left's are kept, `unify` giving back one type and not two.
            (
                Ty::Named { item: x, args: xs, regions },
                Ty::Named { item: y, args: ys, .. },
            ) if x == y && xs.len() == ys.len() => {
                let args = self.unify_all(&xs, &ys)?;
                Ok(self.intern(Ty::Named { item: x, args, regions }))
            }

            // The region is not unified here: how long a reference is good for
            // is worked out by a pass of its own, and a type that agrees but
            // for its region is a type that agrees.
            (Ty::Ref { op: x, life, inner: xi }, Ty::Ref { op: y, inner: yi, .. })
                if x == y =>
            {
                let inner = self.unify(xi, yi)?;
                Ok(self.intern(Ty::Ref { op: x, life, inner }))
            }

            (Ty::Ptr(xi), Ty::Ptr(yi)) => {
                let inner = self.unify(xi, yi)?;
                Ok(self.intern(Ty::Ptr(inner)))
            }
            (Ty::GC(xi), Ty::GC(yi)) => {
                let inner = self.unify(xi, yi)?;
                Ok(self.intern(Ty::GC(inner)))
            }

            // The length is part of the type: `i32[8]` and `i32[9]` are two
            // types, which is what makes an array's size something the checker
            // can hold anyone to.
            (Ty::Array { elem: xe, len: xl }, Ty::Array { elem: ye, len: yl })
                if xl == yl =>
            {
                let elem = self.unify(xe, ye)?;
                Ok(self.intern(Ty::Array { elem, len: xl }))
            }
            (Ty::Run(xe), Ty::Run(ye)) => {
                let elem = self.unify(xe, ye)?;
                Ok(self.intern(Ty::Run(elem)))
            }

            (Ty::Tuple(xs), Ty::Tuple(ys)) if xs.len() == ys.len() => {
                let members = self.unify_all(&xs, &ys)?;
                Ok(self.intern(Ty::Tuple(members)))
            }

            // "reading is less than writing and writing is less than taking",
            // so a closure stands where a weaker one is wanted and the greater
            // of the two is what the pair comes to. That is the one place this
            // arena is not simply equality: a `fn()` handed to something that
            // wanted a `once fn()` is a `fn()` still, and calling it once is
            // all the caller promised to do.
            (
                Ty::Fn { uses: xk, params: xs, ret: xr, is_unsafe: xu },
                Ty::Fn { uses: yk, params: ys, ret: yr, is_unsafe: yu },
            ) if xs.len() == ys.len() && xu == yu => {
                let params = self.unify_all(&xs, &ys)?;
                let ret = self.unify(xr, yr)?;
                Ok(self.intern(Ty::Fn { uses: xk.max(yk), params, ret, is_unsafe: xu }))
            }

            // Two parameters agree where they are the same one. Which two are
            // the same is their place in the declaration's list, not their
            // name: `f<T>` and `g<U>` each have a first parameter.
            (Ty::Param { index: x, .. }, Ty::Param { index: y, .. }) if x == y => Ok(a),

            _ => Err(Mismatch { found: a, wanted: b }),
        }
    }

    fn is(&self, id: TyId, prim: TIRPrim) -> bool {
        matches!(&self.arena[id], Ty::Prim(held) if *held == prim)
    }

    fn fill(&mut self, var: VarId, with: TyId) -> Result<TyId, Mismatch> {
        // A hole filled with a type that holds it is a type with no bottom.
        if self.occurs(var, with) {
            let found = self.intern(Ty::Var(var));
            return Err(Mismatch { found, wanted: with });
        }
        // A number's hole takes numbers. Meeting another hole, the two agree on
        // what will fill them both -- a `5` beside a `5` is still a number and
        // still not settled.
        let wants = self.fills[var];
        if wants != Fills::Anything {
            let held = self.shallow(with);
            match self.arena[held].clone() {
                Ty::Var(other) => {
                    let theirs = self.fills[other];
                    let both = match (wants, theirs) {
                        (a, Fills::Anything) => a,
                        (Fills::Anything, b) => b,
                        (a, b) if a == b => a,
                        // A whole number and a fractional one are two things.
                        _ => {
                            let found = self.intern(Ty::Var(var));
                            return Err(Mismatch { found, wanted: with });
                        }
                    };
                    self.fills[other] = both;
                }
                Ty::Prim(prim) if takes(wants, prim) => {}
                Ty::Error => {}
                // "`null` belongs to every type", this one among them -- so it
                // neither says what the number is nor argues with it, and the
                // hole is left as open as it was. That is what lets a loop with
                // a `break 1` be worth an i32: the loop may end by itself and
                // be `null`, and `null` fits an i32 without being one.
                Ty::Prim(TIRPrim::Null) if NULL_BELONGS => {
                    return Ok(self.intern(Ty::Var(var)))
                }
                _ => {
                    let found = self.intern(Ty::Var(var));
                    return Err(Mismatch { found, wanted: with });
                }
            }
        }
        self.vars[var] = Some(with);
        Ok(with)
    }

    fn unify_all(&mut self, xs: &[TyId], ys: &[TyId]) -> Result<Vec<TyId>, Mismatch> {
        xs.iter()
            .zip(ys.iter())
            .map(|(&x, &y)| self.unify(x, y))
            .collect()
    }

    // Whether the two could be one, without filling anything in. What a check
    // that must not commit wants -- picking among overloads, say.
    pub fn agrees(&mut self, found: TyId, wanted: TyId) -> bool {
        let held = self.vars.clone();
        let out = self.unify(found, wanted).is_ok();
        self.vars = held;
        out
    }

    // ---- Putting arguments in --------------------------------------------

    // `ty` with each `Ty::Param` replaced by the argument at its place: what a
    // call to a generic does. An index with no argument is left standing, which
    // is what lets a partly-applied signature still be walked.
    pub fn substitute(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        let here = self.shallow(ty);
        let rebuilt = match self.arena[here].clone() {
            Ty::Param { index, .. } => return args.get(index).copied().unwrap_or(here),
            Ty::Prim(_) | Ty::Var(_) | Ty::Error => return here,
            Ty::Named { item, args: inner, regions } => Ty::Named {
                item,
                args: inner.iter().map(|&a| self.substitute(a, args)).collect(),
                regions,
            },
            Ty::Ref { op, life, inner } => {
                Ty::Ref { op, life, inner: self.substitute(inner, args) }
            }
            Ty::Ptr(inner) => Ty::Ptr(self.substitute(inner, args)),
            Ty::GC(inner) => Ty::GC(self.substitute(inner, args)),
            Ty::Array { elem, len } => Ty::Array { elem: self.substitute(elem, args), len },
            Ty::Run(elem) => Ty::Run(self.substitute(elem, args)),
            Ty::Tuple(members) => {
                Ty::Tuple(members.iter().map(|&m| self.substitute(m, args)).collect())
            }
            Ty::Fn { uses, params, ret, is_unsafe } => Ty::Fn {
                uses,
                params: params.iter().map(|&p| self.substitute(p, args)).collect(),
                ret: self.substitute(ret, args),
                is_unsafe,
            },
        };
        self.intern(rebuilt)
    }

    // Whether a parameter still stands anywhere in it -- which is whether it
    // is a declaration's type or one use's. A type with none has been settled
    // already and putting arguments in it again would make holes nobody fills.
    pub fn has_param(&self, id: TyId) -> bool {
        let here = self.shallow(id);
        match &self.arena[here] {
            Ty::Param { .. } => true,
            Ty::Named { args, .. } => args.iter().any(|&a| self.has_param(a)),
            Ty::Ref { inner, .. } | Ty::Ptr(inner) | Ty::GC(inner) => self.has_param(*inner),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.has_param(*elem),
            Ty::Tuple(members) => members.iter().any(|&m| self.has_param(m)),
            Ty::Fn { params, ret, .. } => {
                params.iter().any(|&p| self.has_param(p)) || self.has_param(*ret)
            }
            Ty::Prim(_) | Ty::Var(_) | Ty::Error => false,
        }
    }

    // ---- Finishing -------------------------------------------------------

    // The arena as the typed tree holds it, and every hole that was never
    // filled. A hole here is the checker having failed to work something out,
    // and it is the caller that has the spans to say where -- so what comes
    // back is the list, not a report.
    pub fn finish(mut self) -> (Vec<Ty>, Vec<VarId>) {
        // A number nobody said anything about is what it would have been
        // written as: `let n = 0` is an i32 and `let x = 0.0` an f64. That is
        // the one guess in here, and it is the one every language that lets a
        // number stand on its own has to make.
        let mut open = Vec::new();
        for var in 0..self.vars.len() {
            if self.vars[var].is_some() {
                continue;
            }
            match self.fills[var] {
                Fills::Whole => {
                    let held = self.prim(TIRPrim::I32);
                    self.vars[var] = Some(held);
                }
                Fills::Fractional => {
                    let held = self.prim(TIRPrim::F64);
                    self.vars[var] = Some(held);
                }
                // A hole that stands is an `Error`, so nothing below has to
                // carry a case for a type that was never settled.
                Fills::Anything => open.push(var),
            }
        }
        let error = self.error();
        for var in &open {
            self.vars[*var] = Some(error);
        }
        // Worked out before anything is written back. Resolving in place would
        // change an entry that another resolution still points at -- a hole
        // rewritten to `i32` stops looking like a hole, and the next type to
        // reach through it finds the hole's own handle instead of the `i32`'s.
        //
        // The arena grows while this runs, `deep` interning what it rebuilds.
        // The entries it adds are settled already, and walking them again
        // costs one lookup each.
        let mut settled: Vec<TyId> = Vec::new();
        let mut id = 0;
        while id < self.arena.len() {
            settled.push(self.deep(id));
            id += 1;
        }
        let forms: Vec<Ty> = settled.iter().map(|&s| self.arena[s].clone()).collect();
        for (id, form) in forms.into_iter().enumerate() {
            self.arena[id] = form;
        }
        (self.arena, open)
    }

    // ---- Saying what a type is -------------------------------------------

    // A type as a reader wrote it, for a message. `name` is asked what an item
    // is called, since a type names its declaration by handle and this module
    // holds no items.
    pub fn spell(&self, id: TyId, name: &dyn Fn(TTIRItemId) -> String) -> String {
        let here = self.shallow(id);
        match &self.arena[here] {
            Ty::Prim(prim) => prim_name(*prim).to_string(),
            Ty::Named { item, args, .. } => {
                let mut out = name(*item);
                if !args.is_empty() {
                    out.push('<');
                    out.push_str(&self.spell_all(args, name));
                    out.push('>');
                }
                out
            }
            Ty::Ref { op, inner, .. } => format!(
                "{}{}",
                match op {
                    crate::tir::tir_nodes::TIRRefOp::Imm => "&",
                    crate::tir::tir_nodes::TIRRefOp::Mut => "*",
                },
                self.spell(*inner, name)
            ),
            Ty::Ptr(inner) => format!("ptr {}", self.spell(*inner, name)),
            Ty::GC(inner) => format!("gc {}", self.spell(*inner, name)),
            Ty::Array { elem, len } => format!("{}[{}]", self.spell(*elem, name), len),
            Ty::Run(elem) => format!("{}[]", self.spell(*elem, name)),
            Ty::Tuple(members) => format!("({})", self.spell_all(members, name)),
            Ty::Fn { uses, params, ret, is_unsafe } => format!(
                "{}{}fn({}): {}",
                match uses {
                    TIRFnUses::Reads => "",
                    TIRFnUses::Writes => "var ",
                    TIRFnUses::Takes => "once ",
                },
                if *is_unsafe { "unsafe " } else { "" },
                self.spell_all(params, name),
                self.spell(*ret, name)
            ),
            // By its name here and not by its place: a reader wrote `T`, and a
            // message about it should say what they wrote.
            Ty::Param { name: written, .. } => written.clone(),
            // `_` is what a reader writes for one the checker works out, and
            // one it never worked out is what this is.
            Ty::Var(_) => "_".to_string(),
            Ty::Error => "?".to_string(),
        }
    }

    fn spell_all(&self, ids: &[TyId], name: &dyn Fn(TTIRItemId) -> String) -> String {
        ids.iter().map(|&i| self.spell(i, name)).collect::<Vec<_>>().join(", ")
    }
}

// Whether a hole of this kind takes that primitive.
fn takes(wants: Fills, prim: TIRPrim) -> bool {
    match wants {
        Fills::Anything => true,
        Fills::Whole => matches!(
            prim,
            TIRPrim::I8 | TIRPrim::I16 | TIRPrim::I32 | TIRPrim::I64 | TIRPrim::I128
                | TIRPrim::U8 | TIRPrim::U16 | TIRPrim::U32 | TIRPrim::U64 | TIRPrim::U128
                | TIRPrim::F32 | TIRPrim::F64
        ),
        // "A float suffix on a whole number makes a float of it", so a whole
        // number goes in a float; a fractional one does not go anywhere else.
        Fills::Fractional => matches!(prim, TIRPrim::F32 | TIRPrim::F64),
    }
}

impl Default for Types {
    fn default() -> Types {
        Types::new()
    }
}

fn prim_name(prim: TIRPrim) -> &'static str {
    match prim {
        TIRPrim::I8 => "i8",
        TIRPrim::I16 => "i16",
        TIRPrim::I32 => "i32",
        TIRPrim::I64 => "i64",
        TIRPrim::I128 => "i128",
        TIRPrim::U8 => "u8",
        TIRPrim::U16 => "u16",
        TIRPrim::U32 => "u32",
        TIRPrim::U64 => "u64",
        TIRPrim::U128 => "u128",
        TIRPrim::F32 => "f32",
        TIRPrim::F64 => "f64",
        TIRPrim::Bool => "bool",
        TIRPrim::Char => "char",
        TIRPrim::Str => "str",
        TIRPrim::Null => "null",
        TIRPrim::Never => "never",
    }
}

#[cfg(test)]
mod tests;
