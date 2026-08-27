// Lowering: the TIR to the TTIR.
//
//     prep -> lex -> parse -> expand -> lower -> TIR -> [ sema ] -> TTIR
//                                                        ^^^^^^
//
// Everything above this reads what was written; this is the first pass that
// answers questions about it. A name becomes the declaration it names, a type
// becomes what it is rather than how it was spelled, and every expression comes
// out with a type over it -- which is the whole of what makes the tree below
// this one the *typed* tree.
//
// It runs in three passes over the TIR, and it has to:
//
//   1. `declare`  -- a TTIR item for every declaration, with its name and
//      nothing else settled. A struct may name one declared after it, so
//      nothing can resolve a name until every name exists.
//   2. `resolve`  -- the types each declaration wrote: a struct's fields, a
//      fn's signature, a global's type. By now every name is findable.
//   3. `bodies`   -- what each fn does, with a type worked out for every
//      expression in it.
//
// Regions are worked out here too, which is the fourth thing and not a pass of
// its own: "every reference in a signature with no lifetime of its own gets
// one, and a reference in the return type gets the shortest-lived of the ones
// the parameters brought in" (§3). What comes of that is `TTIRFn::outlives`,
// and holding a caller to it is `borrows`.
//
// After the three passes it runs `borrows` over what it built -- moves,
// aliasing and regions -- but only where nothing has been turned down yet: a
// tree with a `Ty::Error` in it has holes where that pass would look, and one
// mistake is meant to be one message rather than the head of a list.
//
// One thing it gets wrong, and knowingly. A number with no suffix is a
// hole, so that `let x: i64 = 5` puts an i64 there and `let y: u8 = 5` a u8 --
// which is what a hole is for. The cost is that the hole will take *anything*:
// `if 5 { }` is accepted, the 5 having become a `bool`. What is wanted is a
// hole that only numbers fill, which is one more kind of hole than `Types` has.
// Until it has one, a number is too free rather than too fixed, and that is the
// direction that accepts a wrong program rather than refusing a right one.
//
// This file holds the `Lowerer`, the frame a body's scopes are kept in, and the
// first of the three passes -- `declare`, which is short because it settles
// nothing. The other two are spread over the files below, roughly in the order
// a reader wants them:
//
//   `resolve`     the types each declaration wrote, and what a written type
//                 resolves to.
//   `elide`       the regions a signature did not write (§3's elision rule).
//   `bodies`      the third pass: a slot per local, a frame per block.
//   `exprs`       every expression that fits in one paragraph.
//   `structs`     `Point { x: 1, y: 2 }`, field by field against the
//                 declaration.
//   `pats`        `match` and the patterns it is written out of.
//   `binds`       what taking a value apart does to it.
//   `closures`    a body inside a body, and what it took with it.
//   `containers`  the map, set and range literals.
//   `loops`       `while` and `for`, and the value a `break` may carry.
//   `paths`       what a `::` spells, and the arguments hanging off it.
//   `bounds`      which types answer which traits.
//   `covers`      whether a `match` leaves anything out.
//
// The `Lowerer` is one type spread over all of them, so its methods are
// `pub(super)` where a sibling calls them. Its fields are not: a private field
// is visible to the files below this one, which is the reason the struct stays
// here.

// The allow covers the parts of the surface no caller has reached yet.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::sema::types::Types;
use crate::tir::tir_nodes::{
    TIRAttrs, TIRBinding, TIRExprId, TIRFn, TIRItemId, TIRItemKind, TIRPrim, TIRProgram, TIRVis,
};
use crate::tir::ttir_nodes::{
    TTIRCapture, TTIRFn, TTIRItem, TTIRItemId, TTIRItemKind, TTIRLocal, TTIRLocalId, TTIRModule,
    RegionId, TTIRBound, TTIRProgram, TyId,
};

mod binds;
mod bodies;
mod bounds;
mod closures;
mod containers;
mod covers;
mod elide;
mod exprs;
mod loops;
mod paths;
mod pats;
mod resolve;
mod structs;

#[cfg(test)]
mod tests;

pub struct Lowerer<'a> {
    tir:    &'a TIRProgram,
    out:    TTIRProgram,
    types:  Types,
    errors: Diagnostics,

    // Every declaration by the name it is reached at: `limits::MAX` as well as
    // `MAX`, so a path finds what a bare name finds and no more.
    names:  HashMap<String, TTIRItemId>,
    // The TTIR item each TIR item became, so the second pass can find the first
    // pass's work.
    made:   Vec<Option<TTIRItemId>>,

    // The bodies being built, innermost last: a closure is a body inside a
    // body, and a name it uses but did not declare is one of the frame outside
    // it. That is the whole of why this is a stack and not a body.
    frames: Vec<Frame>,
    // The parameters of the declaration being walked, for a `Ty::Param`.
    params: Vec<String>,
    // Which types answer each trait: the `impl Trait for T` of the suite, by
    // the trait they answer. Built once, between resolving and the bodies --
    // every impl is in by then, and nothing before the bodies asks.
    answers: HashMap<TTIRItemId, Vec<TyId>>,
    // The regions of the declaration being resolved. Numbered from 1: region 0
    // is what a reference outside a signature gets, where how long it is good
    // for is nobody's question yet.
    regions: usize,
    // Its named lifetimes, so a `'a` written twice is one region twice.
    lifetimes: HashMap<String, RegionId>,
    // Whether what is being resolved is a signature. Only a signature hands out
    // regions: inside a body a reference gets region 0, since how long a
    // reference held in a local is good for is not what a signature promises.
    in_sig: bool,
    // The declaration being resolved, for a refusal about something written in
    // it that carries no position of its own -- a lifetime in a bound.
    here: Span,
    // How many lifetimes each declaration takes, by the item it became. Filled
    // while declaring, since a type may name a declaration that has not been
    // resolved yet and the count is the only thing about it this needs.
    lifes: Vec<usize>,
    // The declaration each item was made from, so the count above can be
    // worked out after every name is known and not while they are being found.
    from_item: Vec<Option<TIRItemId>>,
    // Bounds still to be asked. A parameter is a hole at the moment the call
    // is reached -- what fills it is what the call settles -- so asking there
    // asks nothing. They are put by until the body is walked and every hole is
    // as filled as it is going to get.
    pending: Vec<(TyId, TTIRBound, String, TIRExprId)>,
    // What the `break`s of each loop being walked were worth, innermost last.
    // A loop is worth "the operand of the `break` that leaves it" (§5.1), and
    // there is no telling which one until every one is in.
    breaks: Vec<Vec<TyId>>,
    // What `self` is in the declaration being walked: the type an impl is
    // written for. `None` outside one, and outside one there is no `self`.
    // A trait's is not this -- see `receiver_ty`.
    subject: Option<TyId>,
}

// One body under construction.
struct Frame {
    locals:   Vec<TTIRLocal>,
    // Slots by the name they were bound under, innermost scope last.
    scopes:   Vec<HashMap<String, TTIRLocalId>>,
    // What this body gives back, which is what a `return` in it is held to. A
    // `return` inside a closure returns from the closure.
    ret:      TyId,
    // What it took from the frame outside it. Empty for a fn: only a closure
    // reaches out of itself.
    captures: Vec<TTIRCapture>,
    // The capture each outer slot became, so a name used twice is caught once.
    caught:   HashMap<TTIRLocalId, usize>,
    // `move`, which "overrules all of that at once" (§5).
    is_move:  bool,
}

impl Frame {
    fn new(ret: TyId, is_move: bool) -> Frame {
        Frame {
            locals:   Vec::new(),
            scopes:   vec![HashMap::new()],
            ret,
            captures: Vec::new(),
            caught:   HashMap::new(),
            is_move,
        }
    }
}

impl<'a> Lowerer<'a> {
    pub fn new(tir: &'a TIRProgram) -> Lowerer<'a> {
        Lowerer {
            tir,
            out: TTIRProgram::default(),
            types: Types::new(),
            errors: Diagnostics::new(),
            names: HashMap::new(),
            made: vec![None; tir.items.len()],
            frames: Vec::new(),
            params: Vec::new(),
            answers: HashMap::new(),
            regions: 0,
            lifetimes: HashMap::new(),
            in_sig: false,
            here: Span::at(1, 1),
            lifes: Vec::new(),
            from_item: Vec::new(),
            pending: Vec::new(),
            breaks: Vec::new(),
            subject: None,
        }
    }

    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    // The three passes, and the arena at the end of them. Every hole the
    // checker left is settled by `Types::finish`, and one that was never filled
    // is an expression whose type was never worked out -- reported here,
    // because this is what has the spans.
    pub fn lower(mut self, at: Vec<String>) -> (TTIRProgram, Diagnostics) {
        // `bool` whether the program mentions one or not: `gir::drops` types a
        // release's flag with it, and a flag stands for a slot and not for
        // anything anybody wrote.
        self.types.prim(TIRPrim::Bool);
        let roots: Vec<TIRItemId> = self.tir.roots.clone();
        self.declare(&roots, &[]);
        self.count_regions();
        self.resolve(&roots);
        self.gather_impls();
        let made: Vec<TTIRItemId> = roots.iter().filter_map(|&r| self.made[r]).collect();
        self.bodies(&roots);

        self.out.modules = vec![TTIRModule { path: at, roots: made }];
        let (arena, open) = self.types.finish();
        if !open.is_empty() {
            // Nothing points at one of these any more -- `finish` turned each
            // into an `Error` -- but a type nobody worked out is a fact worth
            // one message.
            self.errors.push(
                Diagnostic::warning(
                    format!("{} types were never worked out", open.len()),
                    Span::at(1, 1),
                )
                .with_label("the checker did not settle everything")
                .with_note("an expression whose type is `?` is one of these"),
            );
        }
        self.out.types = arena;

        // Moves and borrows, over the tree this just built. Only where nothing
        // has been turned down yet: a tree with an `Ty::Error` in it has holes
        // where the checker would look, and one mistake is meant to be one
        // message rather than the head of a list.
        if !self.errors.has_errors() {
            let mut said = crate::sema::borrows::Checker::new(&self.out).check().clone();
            self.errors.absorb(&mut said);
        }
        (self.out, self.errors)
    }

    fn span(&self, item: TIRItemId) -> Span {
        Span::at(self.tir.items[item].line, self.tir.items[item].col)
    }

    fn at(&self, expr: TIRExprId) -> Span {
        Span::at(self.tir.exprs[expr].line, self.tir.exprs[expr].col)
    }

    fn push(&mut self, kind: TTIRItemKind, at: TIRItemId) -> TTIRItemId {
        let held = &self.tir.items[at];
        self.out.items.push(TTIRItem { kind, line: held.line, col: held.col });
        self.out.items.len() - 1
    }

    // ---- 1. Declaring ----------------------------------------------------

    // A TTIR item for every declaration, holding its name and nothing settled.
    // Two passes and not one because a declaration may name one written after
    // it, and a name cannot be followed before it exists.
    fn declare(&mut self, items: &[TIRItemId], within: &[String]) {
        for &id in items {
            let (name, kind) = match &self.tir.items[id].kind {
                TIRItemKind::Fn(f) => (f.name.clone(), self.blank_fn(f)),
                TIRItemKind::Struct { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Struct {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        generics: Vec::new(), fields: Vec::new(),
                    },
                ),
                TIRItemKind::Enum { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Enum {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        generics: Vec::new(), variants: Vec::new(),
                    },
                ),
                TIRItemKind::Trait { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Trait {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        generics: Vec::new(), wheres: Vec::new(), members: Vec::new(),
                    },
                ),
                TIRItemKind::TypeAlias { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::TypeAlias {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        generics: Vec::new(), wheres: Vec::new(), ty: 0,
                    },
                ),
                TIRItemKind::Const { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Const {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        ty: 0, value: 0,
                    },
                ),
                TIRItemKind::Global { vis, intro, name, .. } => {
                    let TIRBinding::Name(held) = name else { continue };
                    (
                        held.clone(),
                        TTIRItemKind::Global {
                            vis: *vis, attrs: TIRAttrs::default(), intro: *intro,
                            name: name.clone(), ty: 0, init: None,
                        },
                    )
                }
                TIRItemKind::Namespace { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Namespace {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        items: Vec::new(),
                    },
                ),
                // An impl declares no name of its own; its members do.
                TIRItemKind::Impl { .. } => (
                    String::new(),
                    TTIRItemKind::Impl {
                        vis: TIRVis::Unwritten, attrs: TIRAttrs::default(),
                        generics: Vec::new(), wheres: Vec::new(), ty: 0, of: None,
                        members: Vec::new(),
                    },
                ),
                // Gone by here: what it reached is the resolver's, and this
                // pass is handed one file at a time.
                TIRItemKind::Import { .. } => continue,
            };

            let made = self.push(kind, id);
            self.made[id] = Some(made);
            if self.from_item.len() <= made {
                self.from_item.resize(made + 1, None);
            }
            self.from_item[made] = Some(id);
            if !name.is_empty() {
                // By the bare name and by the path it is reached at, so
                // `limits::MAX` and a `MAX` inside `limits` are one entry each.
                let mut path = within.to_vec();
                path.push(name.clone());
                self.names.insert(path.join("::"), made);
                self.names.entry(name).or_insert(made);
            }

            // Down into whatever holds more declarations.
            match &self.tir.items[id].kind {
                TIRItemKind::Namespace { name, items, .. } => {
                    let mut inner = within.to_vec();
                    inner.push(name.clone());
                    let items = items.clone();
                    self.declare(&items, &inner);
                }
                TIRItemKind::Trait { members, .. } | TIRItemKind::Impl { members, .. } => {
                    let members = members.clone();
                    self.declare(&members, within);
                }
                _ => {}
            }
        }
    }

    // A fn with its name and nothing else: the signature is the second pass's.
    fn blank_fn(&self, f: &TIRFn) -> TTIRItemKind {
        TTIRItemKind::Fn(TTIRFn {
            vis: f.vis,
            attrs: f.attrs.clone(),
            is_const: f.is_const,
            is_unsafe: f.is_unsafe,
            name: f.name.clone(),
            symbol: String::new(),
            generics: Vec::new(),
            wheres: Vec::new(),
            ty: 0,
            params: Vec::new(),
            ret: 0,
            outlives: Vec::new(),
            body: None,
        })
    }
}
