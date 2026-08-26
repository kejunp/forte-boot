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

// The allow covers the parts of the surface no caller has reached yet.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::sema::types::Types;
use crate::tir::tir_nodes::{
    TIRFnUses,
    TIRAttrs, TIRBinOp, TIRBinding, TIRExprId, TIRExprKind, TIRFn, TIRGeneric, TIRItemId,
    TIRBound, TIRItemKind, TIRLit, TIRPatId, TIRPatKind, TIRPrim, TIRProgram, TIRRefOp,
    TIRGenericArg, TIRPayload, TIRStmt, TIRTypeId, TIRTypeKind, TIRUnaryOp, TIRVis, TIRWherePred,
};
use crate::tir::ttir_nodes::{
    TTIRBody, TTIRBodyId, TTIRCapture, TTIRCaptureMode, TTIRExpr, TTIRExprId, TTIRExprKind,
    TTIRFieldDecl, TTIRFn,
    TTIRGeneric, TTIRItem, TTIRItemId, TTIRItemKind, TTIRLocal, TTIRLocalId, TTIRModule,
    RegionId, TTIRBound, TTIRParam, TTIRPatId, TTIRPatKind, TTIRPayload, TTIRProgram, TTIRStmt,
    TTIRSubject, TTIRVariant, TTIRWherePred, Ty, TyId,
};

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

// ---- 2. Resolving what was written ----------------------------------------

impl<'a> Lowerer<'a> {
    fn resolve(&mut self, items: &[TIRItemId]) {
        for &id in items {
            let Some(made) = self.made[id] else { continue };
            self.here = self.span(id);
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    self.params = type_names_of(&f.generics);
                    self.open_regions(&f.generics);
                    let generics = self.generics(&f.generics, &f.wheres);
                    let made_wheres = self.wheres(&f.wheres, &f.generics);
                    let params: Vec<TTIRParam> = f
                        .params
                        .iter()
                        .map(|p| TTIRParam { name: p.name.clone(), slot: None })
                        .collect();
                    let arg_tys: Vec<TyId> = f
                        .params
                        .iter()
                        .map(|p| match p.ty {
                            Some(ty) => self.ty(ty),
                            // "there is no `self: T`: the type is the one the
                            // impl names, so the annotation only ever repeated
                            // it" (§3). So the impl is asked instead.
                            None => self.receiver_ty(&p.name, self.here),
                        })
                        .collect();
                    let ret = match f.ret {
                        Some(ret) => self.ty(ret),
                        // "A `<return_type_opt>` left out is `null`" (§2).
                        None => self.types.null(),
                    };
                    let ty = self.types.intern(Ty::Fn {
                        // A declared fn captures nothing, so calling it does
                        // nothing to what it captured, however many times.
                        uses: TIRFnUses::Reads,
                        params: arg_tys.clone(),
                        ret,
                        is_unsafe: f.is_unsafe,
                    });
                    // "a reference in the return type gets the shortest-lived
                    // of the ones the parameters brought in" -- every region a
                    // parameter brought outlives every region the return has
                    // that nothing named. A region the writer named is left
                    // alone: naming it is what sharpens the answer.
                    let brought = self.regions_of(&arg_tys);
                    let given = self.regions_of(&[ret]);
                    let named: Vec<RegionId> = self.lifetimes.values().copied().collect();
                    let mut outlives = Vec::new();
                    for &shorter in &given {
                        if named.contains(&shorter) {
                            continue;
                        }
                        for &longer in &brought {
                            if longer != shorter {
                                outlives.push((longer, shorter));
                            }
                        }
                    }

                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.generics = generics;
                    held.wheres = made_wheres;
                    held.outlives = outlives;
                    held.params = params;
                    held.ret = ret;
                    held.ty = ty;
                    self.params.clear();
                }

                TIRItemKind::Struct { name: _, generics, fields, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let made_fields: Vec<TTIRFieldDecl> = fields
                        .iter()
                        .map(|f| TTIRFieldDecl {
                            vis:   f.vis,
                            attrs: f.attrs.clone(),
                            name:  f.name.clone(),
                            ty:    self.ty(f.ty),
                        })
                        .collect();
                    let TTIRItemKind::Struct { generics, fields, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *fields = made_fields;
                    self.params.clear();
                }

                TIRItemKind::Enum { generics, variants, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let made_variants: Vec<TTIRVariant> = variants
                        .iter()
                        .enumerate()
                        .map(|(i, v)| TTIRVariant {
                            attrs:   v.attrs.clone(),
                            name:    v.name.clone(),
                            payload: self.payload(&v.payload),
                            // Counted. What a written `D = 4` comes to wants
                            // the const evaluator, and there is none -- so one
                            // is counted like any other, which is wrong and is
                            // said out loud rather than hidden.
                            value:   i as i64,
                        })
                        .collect();
                    for v in &variants {
                        if let crate::tir::tir_nodes::TIRPayload::Discriminant(at) = v.payload {
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`{}` is given a number and it is counted instead", v.name),
                                    self.at(at),
                                )
                                .with_label("this is not worked out")
                                .with_note("working out a constant is the const evaluator's, and there is none yet"),
                            );
                        }
                    }
                    let TTIRItemKind::Enum { generics, variants, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *variants = made_variants;
                    self.params.clear();
                }

                TIRItemKind::TypeAlias { generics, ty, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &[]);
                    let named = self.ty(ty);
                    let TTIRItemKind::TypeAlias { generics, ty, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *ty = named;
                    self.params.clear();
                }

                TIRItemKind::Const { ty, .. } => {
                    let held = self.ty(ty);
                    let TTIRItemKind::Const { ty, .. } = &mut self.out.items[made].kind else {
                        continue;
                    };
                    *ty = held;
                }

                TIRItemKind::Global { ty, .. } => {
                    let held = match ty {
                        Some(ty) => self.ty(ty),
                        None => self.types.fresh(),
                    };
                    let TTIRItemKind::Global { ty, .. } = &mut self.out.items[made].kind else {
                        continue;
                    };
                    *ty = held;
                }

                TIRItemKind::Namespace { items, .. } => {
                    let inner: Vec<TTIRItemId> =
                        items.iter().filter_map(|&i| self.made[i]).collect();
                    self.resolve(&items);
                    let TTIRItemKind::Namespace { items, .. } = &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *items = inner;
                }

                TIRItemKind::Trait { members, .. } => {
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[i]).collect();
                    self.resolve(&members);
                    let TTIRItemKind::Trait { members, .. } = &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *members = inner;
                }

                TIRItemKind::Impl { generics, wheres, ty, for_ty, members, .. } => {
                    self.params = type_names_of(&generics);
                    self.open_regions(&generics);
                    let made_generics = self.generics(&generics, &wheres);
                    let made_wheres = self.wheres(&wheres, &generics);
                    // "`for_ty` is `Some` where a `for` was written, and then
                    // `ty` is the trait" -- so the two swap round here.
                    let (subject, of) = match for_ty {
                        Some(for_ty) => (self.ty(for_ty), self.item_of(ty)),
                        None => (self.ty(ty), None),
                    };
                    let inner: Vec<TTIRItemId> =
                        members.iter().filter_map(|&i| self.made[i]).collect();
                    let held = self.subject.replace(subject);
                    self.resolve(&members);
                    self.subject = held;
                    let TTIRItemKind::Impl { generics, wheres, ty, of: written, members, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *wheres = made_wheres;
                    *ty = subject;
                    *written = of;
                    *members = inner;
                    self.params.clear();
                }

                TIRItemKind::Import { .. } => {}
            }
        }
    }

    // Every region standing anywhere in these types.
    fn regions_of(&self, tys: &[TyId]) -> Vec<RegionId> {
        let mut out = Vec::new();
        for &ty in tys {
            self.walk_regions(ty, &mut out);
        }
        out
    }

    fn walk_regions(&self, ty: TyId, out: &mut Vec<RegionId>) {
        match self.types.get(ty).clone() {
            Ty::Ref { life, inner, .. } => {
                if life != 0 && !out.contains(&life) {
                    out.push(life);
                }
                self.walk_regions(inner, out);
            }
            Ty::Named { args, regions, .. } => {
                for r in regions {
                    if r != 0 && !out.contains(&r) {
                        out.push(r);
                    }
                }
                for a in args {
                    self.walk_regions(a, out);
                }
            }
            Ty::Ptr(inner) | Ty::GC(inner) => self.walk_regions(inner, out),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.walk_regions(elem, out),
            Ty::Tuple(members) => {
                for m in members {
                    self.walk_regions(m, out);
                }
            }
            Ty::Fn { params, ret, .. } => {
                for p in params {
                    self.walk_regions(p, out);
                }
                self.walk_regions(ret, out);
            }
            _ => {}
        }
    }

    // What `self` is. An impl names the type it is written for, and that is the
    // whole of what a receiver's type comes from.
    //
    // A trait's is another matter: the type is whatever answers the trait, and
    // `Ty` has no way to say "the one this is about". It is a parameter in all
    // but name -- what it stands for is settled by whoever answers the trait,
    // exactly as a `T` is settled by whoever calls -- so it is written as one,
    // named `Self` and placed after the method's own. A `Ty::SelfTy` would say
    // it more plainly and is what to add if this starts costing anything.
    fn receiver_ty(&mut self, name: &TIRBinding, at: Span) -> TyId {
        let TIRBinding::SelfRecv(how, life) = name else { return self.types.fresh() };
        let subject = match self.subject {
            Some(subject) => subject,
            None => {
                let index = self.params.len();
                self.types.intern(Ty::Param { name: "Self".to_string(), index })
            }
        };
        let op = match how {
            // "A bare `self` takes the value whole and so moves it." Nothing is
            // taken, so there is no region to give it.
            crate::tir::tir_nodes::TIRSelf::Value => return subject,
            crate::tir::tir_nodes::TIRSelf::Ref => TIRRefOp::Imm,
            crate::tir::tir_nodes::TIRSelf::Mut => TIRRefOp::Mut,
        };
        // A receiver is a reference in a signature like any other, so it gets a
        // region like any other -- and `&'a self` names one, which is the whole
        // point of letting it be written.
        let life = match life {
            Some(name) => {
                let name = name.clone();
                self.life(&name, at)
            }
            None => self.region(),
        };
        self.types.intern(Ty::Ref { op, life, inner: subject })
    }

    // The parameters a declaration was written with, and what each is held to.
    // A `where` predicate about one of them is folded into that one's bounds:
    // "`fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing", and this
    // tree is what a declaration is rather than how it was written.
    fn generics(&mut self, held: &[TIRGeneric], wheres: &[TIRWherePred]) -> Vec<TTIRGeneric> {
        let names = names_of(held);
        let mut made: Vec<TTIRGeneric> = held
            .iter()
            .map(|g| match g {
                TIRGeneric::Type { name, bounds } => TTIRGeneric::Type {
                    name:   name.clone(),
                    bounds: self.bounds(bounds),
                },
                TIRGeneric::Life { name, bounds } => TTIRGeneric::Life {
                    name:   name.clone(),
                    region: self.lifetimes.get(name).copied().unwrap_or(0),
                    // "Regions only -- a lifetime implements nothing": a `'a: T`
                    // is written the same way and is dropped here rather than
                    // refused, the rule about it being section 3's and not this
                    // list's shape.
                    bounds: bounds
                        .iter()
                        .filter_map(|b| match b {
                            TIRBound::Life(name) => Some(name.clone()),
                            TIRBound::Trait(_) => None,
                        })
                        .collect::<Vec<String>>()
                        .into_iter()
                        .map(|name| {
                            let at = self.here;
                            self.life(&name, at)
                        })
                        .collect(),
                },
            })
            .collect();

        for pred in wheres {
            let TIRBound::Trait(ty) = &pred.subject else { continue };
            let TIRTypeKind::Named { path, .. } = &self.tir.types[*ty].kind else { continue };
            if path.len() != 1 {
                continue;
            }
            let Some(index) = names.iter().position(|n| *n == path[0]) else { continue };
            let held = self.bounds(&pred.bounds);
            if let TTIRGeneric::Type { bounds, .. } = &mut made[index] {
                bounds.extend(held);
            }
        }
        made
    }

    // A region of its own. Numbered from 1: a reference outside a signature
    // gets region 0, how long it is good for being nobody's question yet.
    // The region a written `'a` names. There is no such thing as a lifetime
    // that names no region: one nothing declares is refused where it stands,
    // and a fresh region stands in its place so that one mistake is one message.
    fn life(&mut self, name: &str, at: Span) -> RegionId {
        if let Some(held) = self.lifetimes.get(name).copied() {
            return held;
        }
        self.errors.push(
            Diagnostic::error(format!("no lifetime is called `'{}`", name), at)
                .with_label("nothing declares it")
                .with_help("a lifetime is declared among the parameters, `<'a>`"),
        );
        // Fresh even outside a signature, where `region` hands out 0: two
        // undeclared lifetimes are not thereby one.
        self.regions += 1;
        self.regions
    }

    // The regions a named type is handed, one per lifetime its declaration
    // takes. A written `'a` names a region the declaration declared; where none
    // was written, "every reference in a signature with no lifetime of its own
    // gets one" (§3) reaches here too, and a fresh one is made -- so a `Held`
    // and a `Held<'a>` carry the same promise and only one of them says which.
    // How many regions each declaration ends up with: one per lifetime it
    // declares, and one more per reference in it that named none -- "every
    // reference in a signature with no lifetime of its own gets one" (§3),
    // which a declaration carrying references answers to as much as a
    // signature does. Numbered in that order, which is the order
    // `open_regions` and the field walk hand them out in.
    //
    // Worked out once every name is known, since a declaration may name one
    // written below it.
    fn count_regions(&mut self) {
        for made in 0..self.out.items.len() {
            let takes = self.takes_of(made, &mut Vec::new());
            if self.lifes.len() <= made {
                self.lifes.resize(made + 1, 0);
            }
            self.lifes[made] = takes;
        }
    }

    fn takes_of(&self, made: TTIRItemId, seen: &mut Vec<TTIRItemId>) -> usize {
        // A declaration reached from itself has no finite count -- each turn
        // round adds the last one's -- and there is nothing to give but 0.
        // `holds_ref` still sees the reference, so what comes of such a type is
        // held to every parameter, which is the answer that is never wrong.
        if seen.contains(&made) {
            return 0;
        }
        let Some(&Some(id)) = self.from_item.get(made) else { return 0 };
        seen.push(made);
        let takes = match &self.tir.items[id].kind {
            TIRItemKind::Struct { generics, fields, .. } => {
                lifetimes_of(generics)
                    + fields.iter().map(|f| self.elided_in(f.ty, seen)).sum::<usize>()
            }
            TIRItemKind::Enum { generics, variants, .. } => {
                lifetimes_of(generics)
                    + variants
                        .iter()
                        .map(|v| match &v.payload {
                            // A discriminant is a constant and holds no type,
                            // so it carries no reference either.
                            TIRPayload::None | TIRPayload::Discriminant(_) => 0,
                            TIRPayload::Tuple(tys) => {
                                tys.iter().map(|&t| self.elided_in(t, seen)).sum()
                            }
                            TIRPayload::Named(fields) => {
                                fields.iter().map(|f| self.elided_in(f.ty, seen)).sum()
                            }
                        })
                        .sum::<usize>()
            }
            TIRItemKind::TypeAlias { generics, ty, .. } => {
                lifetimes_of(generics) + self.elided_in(*ty, seen)
            }
            _ => 0,
        };
        seen.pop();
        takes
    }

    // References in a written type that named no lifetime, and the regions of
    // any declaration it names and hands no lifetime to -- a `struct Outer {
    // inner: Inner }` carries whatever `Inner` does, since the regions its
    // fields stand in have to come from somewhere.
    fn elided_in(&self, ty: TIRTypeId, seen: &mut Vec<TTIRItemId>) -> usize {
        match &self.tir.types[ty].kind {
            TIRTypeKind::Ref { life, inner, .. } => {
                usize::from(life.is_none()) + self.elided_in(*inner, seen)
            }
            TIRTypeKind::Ptr(inner) => self.elided_in(*inner, seen),
            TIRTypeKind::Array { elem, .. } | TIRTypeKind::Run(elem) => {
                self.elided_in(*elem, seen)
            }
            TIRTypeKind::Tuple(members) => {
                members.iter().map(|&m| self.elided_in(m, seen)).sum()
            }
            TIRTypeKind::Fn { params, ret, .. } => {
                params.iter().map(|&p| self.elided_in(p, seen)).sum::<usize>()
                    + ret.map(|r| self.elided_in(r, seen)).unwrap_or(0)
            }
            TIRTypeKind::Named { path, args } => {
                let written = args.iter().filter(|a| matches!(a, TIRGenericArg::Life(_))).count();
                let inner: usize = args
                    .iter()
                    .map(|a| match a {
                        TIRGenericArg::Type(ty) => self.elided_in(*ty, seen),
                        TIRGenericArg::Life(_) => 0,
                    })
                    .sum();
                let named = match self.names.get(&path.join("::")).copied() {
                    Some(item) => self.takes_of(item, seen).saturating_sub(written),
                    None => 0,
                };
                inner + named
            }
            _ => 0,
        }
    }

    fn named_regions(&mut self, item: TTIRItemId, written: &[String], at: Span) -> Vec<RegionId> {
        let takes = self.lifes.get(item).copied().unwrap_or(0);
        let mut out = Vec::with_capacity(takes.max(written.len()));
        for name in written {
            let name = name.clone();
            out.push(self.life(&name, at));
        }
        while out.len() < takes {
            out.push(self.region());
        }
        out
    }

    fn region(&mut self) -> RegionId {
        if !self.in_sig {
            return 0;
        }
        self.regions += 1;
        self.regions
    }

    // The regions a declaration begins with: one for each lifetime it declared,
    // so a `'a` written in two places is one region twice.
    fn open_regions(&mut self, generics: &[TIRGeneric]) {
        self.regions = 0;
        self.lifetimes.clear();
        self.in_sig = true;
        for g in generics {
            if let TIRGeneric::Life { name, .. } = g {
                let held = self.region();
                self.lifetimes.insert(name.clone(), held);
            }
        }
    }

    // The signature is behind us. A `'a` written in the body still names the
    // region the declaration declared -- the numbering `open_regions` hands out
    // is by order of declaration, so it is the same region both times -- but a
    // reference written with no lifetime of its own gets region 0 from here on.
    fn close_regions(&mut self) {
        self.in_sig = false;
    }

    // What stands on the right of a bound's colon, resolved. A trait is the
    // type it names; a lifetime is a region, and regions are another pass's.
    fn bounds(&mut self, held: &[TIRBound]) -> Vec<TTIRBound> {
        held.iter()
            .map(|bound| match bound {
                TIRBound::Trait(ty) => TTIRBound::Trait(self.ty(*ty)),
                TIRBound::Life(name) => {
                    let name = name.clone();
                    let at = self.here;
                    TTIRBound::Life(self.life(&name, at))
                }
            })
            .collect()
    }

    // Every predicate with no parameter to fold into: "`where Vec<T>: Show` is
    // about a type that was built rather than declared".
    fn wheres(&mut self, held: &[TIRWherePred], generics: &[TIRGeneric]) -> Vec<TTIRWherePred> {
        let names = names_of(generics);
        held.iter()
            .filter(|pred| {
                let TIRBound::Trait(ty) = &pred.subject else { return true };
                let TIRTypeKind::Named { path, .. } = &self.tir.types[*ty].kind else {
                    return true;
                };
                !(path.len() == 1 && names.iter().any(|n| *n == path[0]))
            })
            .map(|pred| {
                let subject = match &pred.subject {
                    TIRBound::Trait(ty) => TTIRSubject::Type(self.ty(*ty)),
                    TIRBound::Life(name) => {
                        let name = name.clone();
                        let at = self.here;
                        TTIRSubject::Region(self.life(&name, at))
                    }
                };
                TTIRWherePred { subject, bounds: self.bounds(&pred.bounds) }
            })
            .collect()
    }

    fn payload(&mut self, held: &crate::tir::tir_nodes::TIRPayload) -> TTIRPayload {
        use crate::tir::tir_nodes::TIRPayload;
        match held {
            TIRPayload::None | TIRPayload::Discriminant(_) => TTIRPayload::None,
            TIRPayload::Tuple(tys) => {
                TTIRPayload::Tuple(tys.iter().map(|&t| self.ty(t)).collect())
            }
            TIRPayload::Named(fields) => TTIRPayload::Named(
                fields
                    .iter()
                    .map(|f| TTIRFieldDecl {
                        vis:   f.vis,
                        attrs: f.attrs.clone(),
                        name:  f.name.clone(),
                        ty:    self.ty(f.ty),
                    })
                    .collect(),
            ),
        }
    }

    // The declaration a type names, where it names one.
    fn item_of(&mut self, ty: TIRTypeId) -> Option<TTIRItemId> {
        let at = Span::at(self.tir.types[ty].line, self.tir.types[ty].col);
        let TIRTypeKind::Named { path, .. } = &self.tir.types[ty].kind else {
            self.errors.push(
                Diagnostic::error("a trait is what an `impl ... for` names".to_string(), at)
                    .with_label("this is a type and not a trait")
                    .with_help("`impl T { }` writes an impl of a type's own"),
            );
            return None;
        };
        let name = path.join("::");
        let Some(item) = self.names.get(&name).copied() else {
            self.errors.push(
                Diagnostic::error(format!("no trait is called `{}`", name), at)
                    .with_label("nothing declares it")
                    // The two the compiler knows by name are the two most
                    // likely to be written without being declared.
                    .with_help(match name.as_str() {
                        "Copy" | "Drop" => {
                            "`Copy` and `Drop` are traits like any other and have to be declared"
                        }
                        _ => "a trait is declared with `trait`",
                    }),
            );
            return None;
        };
        if !matches!(self.out.items[item].kind, TTIRItemKind::Trait { .. }) {
            self.errors.push(
                Diagnostic::error(format!("`{}` is not a trait", name), at)
                    .with_label("this is what an impl answers")
                    .with_help("`impl T { }` writes an impl of a type's own"),
            );
            return None;
        }
        Some(item)
    }

    // ---- Types -----------------------------------------------------------

    // What a written type is. "`<grouped_type>` is gone, `_` is gone, and a
    // name has become the declaration it names."
    fn ty(&mut self, id: TIRTypeId) -> TyId {
        let at = Span::at(self.tir.types[id].line, self.tir.types[id].col);
        match self.tir.types[id].kind.clone() {
            TIRTypeKind::Prim(prim) => self.types.prim(prim),

            TIRTypeKind::Named { path, args } => {
                // A parameter of the declaration this stands in, which is a
                // name that is not a declaration.
                if path.len() == 1 {
                    if let Some(index) = self.params.iter().position(|p| *p == path[0]) {
                        return self.types.intern(Ty::Param { name: path[0].clone(), index });
                    }
                }
                // Types and lifetimes are written in one list and kept in
                // two: a `Ty` is what unification works on and a region is what
                // it skips, so they cannot share a slot.
                let written: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        TIRGenericArg::Life(name) => Some(name.clone()),
                        TIRGenericArg::Type(_) => None,
                    })
                    .collect();
                let args: Vec<TyId> = args
                    .iter()
                    .filter_map(|a| match a {
                        TIRGenericArg::Type(ty) => Some(self.ty(*ty)),
                        TIRGenericArg::Life(_) => None,
                    })
                    .collect();
                match self.names.get(&path.join("::")).copied() {
                    // "an alias is a name for a type and not a type, so once
                    // the resolver has followed it there is nothing left of it"
                    Some(item) => match &self.out.items[item].kind {
                        TTIRItemKind::TypeAlias { ty, .. } => *ty,
                        _ => {
                            let regions = self.named_regions(item, &written, at);
                            self.types.intern(Ty::Named { item, args, regions })
                        }
                    },
                    None => {
                        let name = path.join("::");
                        self.errors.push(
                            Diagnostic::error(format!("no type is called `{}`", name), at)
                                .with_label("nothing is declared under this name")
                                .with_help("a type is a struct, an enum, a trait or an alias"),
                        );
                        self.types.error()
                    }
                }
            }

            // "Every reference in a signature with no lifetime of its own gets
            // one" -- so one is made where none was written, and a written one
            // names the region its declaration declared.
            TIRTypeKind::Ref { op, life, inner } => {
                let life = match life {
                    Some(name) => self.life(&name, at),
                    None => self.region(),
                };
                let inner = self.ty(inner);
                self.types.intern(Ty::Ref { op, life, inner })
            }
            TIRTypeKind::Ptr(inner) => {
                let inner = self.ty(inner);
                self.types.intern(Ty::Ptr(inner))
            }
            TIRTypeKind::Run(elem) => {
                let elem = self.ty(elem);
                self.types.intern(Ty::Run(elem))
            }
            TIRTypeKind::Tuple(members) => {
                let members: Vec<TyId> = members.iter().map(|&m| self.ty(m)).collect();
                self.types.intern(Ty::Tuple(members))
            }
            // `fn(i32, str): bool`. Never unsafe: there is no spelling for one,
            // and "a `<return_type_opt>` left out is `null`" (§2) reaches a
            // written fn type as much as a written fn.
            TIRTypeKind::Fn { uses, params, ret } => {
                let params: Vec<TyId> = params.iter().map(|&p| self.ty(p)).collect();
                let ret = match ret {
                    Some(ret) => self.ty(ret),
                    None => self.types.null(),
                };
                self.types.intern(Ty::Fn { uses, params, ret, is_unsafe: false })
            }

            // "An `<array_suffix>` takes a `<const_expr>`, and evaluating one
            // is the checker's" -- which wants a const evaluator this pass has
            // not got. A written number is taken as it stands; anything else
            // has to wait.
            TIRTypeKind::Array { elem, len } => {
                let elem = self.ty(elem);
                match &self.tir.exprs[len].kind {
                    TIRExprKind::Literal { value: TIRLit::Int(n), .. } => {
                        self.types.intern(Ty::Array { elem, len: *n as u64 })
                    }
                    _ => {
                        self.errors.push(
                            Diagnostic::error(
                                "an array's length has to be a written number".to_string(),
                                self.at(len),
                            )
                            .with_label("this is not one")
                            .with_note("working out a constant is the const evaluator's, and there is none yet"),
                        );
                        self.types.error()
                    }
                }
            }

            // "`_`, a type argument left to be worked out" -- which is a hole,
            // and holes are what `Types` is for.
            TIRTypeKind::Infer => self.types.fresh(),
        }
    }
}

// The names a declaration's parameters were written with, in order: a
// `Ty::Param` names its by place, and this is the list it indexes.
fn names_of(generics: &[TIRGeneric]) -> Vec<String> {
    generics
        .iter()
        .map(|g| match g {
            TIRGeneric::Type { name, .. } | TIRGeneric::Life { name, .. } => name.clone(),
        })
        .collect()
}

// The type parameters alone, which is the index space a `Ty::Param` counts in.
// A lifetime is not a type: it takes no slot among them and gets no hole at a
// call, since nothing a call could work out would ever fill one.
fn lifetimes_of(generics: &[TIRGeneric]) -> usize {
    generics.iter().filter(|g| matches!(g, TIRGeneric::Life { .. })).count()
}

fn type_names_of(generics: &[TIRGeneric]) -> Vec<String> {
    generics
        .iter()
        .filter_map(|g| match g {
            TIRGeneric::Type { name, .. } => Some(name.clone()),
            TIRGeneric::Life { .. } => None,
        })
        .collect()
}

// ---- 3. Bodies ------------------------------------------------------------

impl<'a> Lowerer<'a> {
    fn bodies(&mut self, items: &[TIRItemId]) {
        for &id in items {
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    let Some(made) = self.made[id] else { continue };
                    let Some(value) = f.body else { continue };
                    self.here = self.span(id);
                    self.params = type_names_of(&f.generics);
                    self.open_regions(&f.generics);
                    self.close_regions();
                    let body = self.body(made, &f, value);
                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.body = Some(body);
                    self.params.clear();
                }
                TIRItemKind::Impl { generics, ty, for_ty, members, .. } => {
                    self.open_regions(&generics);
                    self.close_regions();
                    let subject = match for_ty {
                        Some(for_ty) => self.ty(for_ty),
                        None => self.ty(ty),
                    };
                    let held = self.subject.replace(subject);
                    self.bodies(&members);
                    self.subject = held;
                }
                TIRItemKind::Namespace { items, .. }
                | TIRItemKind::Trait { members: items, .. } => self.bodies(&items),
                _ => {}
            }
        }
    }

    // One fn's body: a slot for every parameter, then the expression, then the
    // two put together.
    fn body(&mut self, made: TTIRItemId, f: &TIRFn, value: TIRExprId) -> TTIRBodyId {
        self.frames.push(Frame::new(0, false));

        let (arg_tys, ret) = {
            let TTIRItemKind::Fn(held) = &self.out.items[made].kind else {
                return self.finish_body(0)
            };
            let Ty::Fn { params, ret, .. } = &self.types.get(held.ty).clone() else {
                return self.finish_body(0)
            };
            (params.clone(), *ret)
        };
        self.frames.last_mut().expect("a frame").ret = ret;

        // A parameter is a slot like any other, and the slot is what the body
        // names it by.
        let mut params = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            let ty = arg_tys.get(i).copied().unwrap_or_else(|| self.types.fresh());
            // A receiver binds under the word it was written with.
            let held = match p.name {
                TIRBinding::SelfRecv(..) => TIRBinding::Name("self".to_string()),
                _ => p.name.clone(),
            };
            let slot = self.bind(held, ty, crate::tir::tir_nodes::TIRIntro::Let, self.here);
            params.push(TTIRParam { name: p.name.clone(), slot: Some(slot) });
        }
        let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
            return self.finish_body(0)
        };
        held.params = params;

        let out = self.expr(value);
        // "a body that could fall off the end of a `never` is refused" is the
        // checker's; what is held here is that a body gives back what it said.
        let found = self.out.exprs[out].ty;
        if self.types.unify(found, ret).is_err() {
            let (found, ret) = (self.spell(found), self.spell(ret));
            self.errors.push(
                Diagnostic::error(
                    format!("this body gives back `{}` and the signature says `{}`", found, ret),
                    self.at(value),
                )
                .with_label("this is what it comes to"),
            );
        }
        let at = self.at(value);
        self.stands_as(found, ret, at);
        // Now that every hole in this body is as filled as it is going to
        // get, the parameters are held to what they were declared with.
        let held = std::mem::take(&mut self.pending);
        for (arg, bound, name, at) in held {
            self.holds(arg, &bound, &name, at);
        }
        self.finish_body(out)
    }

    fn finish_body(&mut self, value: TTIRExprId) -> TTIRBodyId {
        let frame = self.frames.pop().expect("a frame");
        self.out.bodies.push(TTIRBody { locals: frame.locals, value });
        self.out.bodies.len() - 1
    }

    // `where` is where the name was bound. A slot is not an expression and had
    // none until the checker wanted one: "the value was moved here, and it was
    // bound there" is two places, and only one of them is a line anybody wrote
    // an expression on.
    fn bind(
        &mut self,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
        where_: Span,
    ) -> TTIRLocalId {
        let at = self.frames.len() - 1;
        self.into_frame(at, name, ty, intro, where_)
    }

    fn into_frame(
        &mut self,
        at: usize,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
        where_: Span,
    ) -> TTIRLocalId {
        let frame = &mut self.frames[at];
        frame.locals.push(TTIRLocal {
            name: name.clone(),
            ty,
            intro,
            line: where_.line,
            col: where_.col,
        });
        let slot = frame.locals.len() - 1;
        if let TIRBinding::Name(name) = name {
            if let Some(scope) = frame.scopes.last_mut() {
                scope.insert(name, slot);
            }
        }
        slot
    }

    // The slot a name stands for, seen from the innermost body. A name of a
    // frame further out is captured on the way in -- once per frame it has to
    // cross, so a closure inside a closure takes it from the one that took it.
    fn slot(&mut self, name: &str, used: Span) -> Option<TTIRLocalId> {
        let depth = self.frames.len();
        for at in (0..depth).rev() {
            let found = self.frames[at]
                .scopes
                .iter()
                .rev()
                .find_map(|scope| scope.get(name).copied());
            let Some(mut held) = found else { continue };
            for inner in at + 1..depth {
                held = self.catch(inner, held, name, used);
            }
            return Some(held);
        }
        None
    }

    // One name of the frame outside `at`, given a slot inside it. "A name the
    // body uses but did not declare is captured, and how is worked out per
    // name, each taking the least the body asks of it" -- so it starts at a
    // `&` and is sharpened to a `*` where the body assigns to it.
    fn catch(
        &mut self,
        at: usize,
        outer: TTIRLocalId,
        name: &str,
        used: Span,
    ) -> TTIRLocalId {
        if let Some(&held) = self.frames[at].caught.get(&outer) {
            return self.frames[at].captures[held].slot;
        }
        let held = &self.frames[at - 1].locals[outer];
        let (ty, intro) = (held.ty, held.intro);
        let where_ = Span::at(held.line, held.col);
        let slot = self.into_frame(at, TIRBinding::Name(name.to_string()), ty, intro, where_);
        let mode = if self.frames[at].is_move {
            TTIRCaptureMode::Value
        } else {
            TTIRCaptureMode::Ref(TIRRefOp::Imm)
        };
        let frame = &mut self.frames[at];
        // Where the body first named it, which is the line a refusal about
        // the borrow it takes has to point at.
        frame.captures.push(TTIRCapture { outer, slot, mode, line: used.line, col: used.col });
        let held = frame.captures.len() - 1;
        frame.caught.insert(outer, held);
        slot
    }

    // "assigning to one takes a `*`" -- the least the body asks of it, once it
    // turns out to ask that much. A `move` closure is already by value and
    // there is nothing to sharpen.
    fn assigns_to(&mut self, slot: TTIRLocalId) {
        let Some(frame) = self.frames.last_mut() else { return };
        if frame.is_move {
            return;
        }
        if let Some(held) = frame.captures.iter_mut().find(|c| c.slot == slot) {
            held.mode = TTIRCaptureMode::Ref(TIRRefOp::Mut);
        }
    }

    fn locals(&self) -> &[TTIRLocal] {
        &self.frames[self.frames.len() - 1].locals
    }

    fn make(&mut self, kind: TTIRExprKind, ty: TyId, at: TIRExprId) -> TTIRExprId {
        let held = &self.tir.exprs[at];
        self.out.exprs.push(TTIRExpr { kind, ty, line: held.line, col: held.col });
        self.out.exprs.len() - 1
    }

    fn spell(&self, ty: TyId) -> String {
        let items = &self.out.items;
        self.types.spell(ty, &|item| match &items[item].kind {
            TTIRItemKind::Struct { name, .. }
            | TTIRItemKind::Enum { name, .. }
            | TTIRItemKind::Trait { name, .. } => name.clone(),
            _ => "?".to_string(),
        })
    }

    // What this pass cannot work out yet. One message and an `Error`, which is
    // what keeps the rest of the body being checked.
    fn not_yet(&mut self, what: &str, at: TIRExprId) -> TTIRExprId {
        self.errors.push(
            Diagnostic::error(format!("`sema` cannot type {} yet", what), self.at(at))
                .with_label("this is not worked out")
                .with_note("the tree below this holds an `Error` where its type would be"),
        );
        let ty = self.types.error();
        self.make(TTIRExprKind::Literal(TIRLit::Null), ty, at)
    }
}

// ---- Expressions ----------------------------------------------------------

impl<'a> Lowerer<'a> {
    fn expr(&mut self, id: TIRExprId) -> TTIRExprId {
        match self.tir.exprs[id].kind.clone() {
            // A number with no suffix is a hole: what it is depends on what it
            // is put beside, which is what inference is for.
            TIRExprKind::Literal { value, suffix } => {
                let ty = match (&value, suffix) {
                    (_, Some(prim)) => self.types.prim(prim),
                    (TIRLit::Int(_), None) => self.types.fresh_whole(),
                    (TIRLit::Float(_), None) => self.types.fresh_fractional(),
                    (TIRLit::Str(_), None) => self.types.prim(TIRPrim::Str),
                    (TIRLit::Char(_), None) => self.types.prim(TIRPrim::Char),
                    (TIRLit::Bool(_), None) => self.types.prim(TIRPrim::Bool),
                    (TIRLit::Null, None) => self.types.null(),
                };
                self.make(TTIRExprKind::Literal(value), ty, id)
            }

            // A name: a slot of this body first, and a declaration after --
            // "the innermost scope that has it answers".
            TIRExprKind::Name(path) => self.named(&path, id),

            TIRExprKind::Block { stmts, tail } => self.block(&stmts, tail, id),

            TIRExprKind::Unary { op, operand } => {
                let held = self.expr(operand);
                let inner = self.out.exprs[held].ty;
                let ty = match op {
                    crate::tir::tir_nodes::TIRUnaryOp::Not => self.types.prim(TIRPrim::Bool),
                    crate::tir::tir_nodes::TIRUnaryOp::Neg => inner,
                    crate::tir::tir_nodes::TIRUnaryOp::Ref(op) => {
                        self.types.intern(Ty::Ref { op, life: 0, inner })
                    }
                    crate::tir::tir_nodes::TIRUnaryOp::Addr => {
                        self.types.intern(Ty::Ptr(inner))
                    }
                };
                self.make(TTIRExprKind::Unary { op, operand: held }, ty, id)
            }

            TIRExprKind::Binary { op, lhs, rhs } => {
                let (l, r) = (self.expr(lhs), self.expr(rhs));
                let (lt, rt) = (self.out.exprs[l].ty, self.out.exprs[r].ty);
                if self.types.unify(lt, rt).is_err() {
                    let (lt, rt) = (self.spell(lt), self.spell(rt));
                    self.errors.push(
                        Diagnostic::error(
                            format!("`{}` and `{}` are not one type", lt, rt),
                            self.at(id),
                        )
                        .with_label("the two sides disagree"),
                    );
                }
                // A comparison and a logical operator give back a `bool`
                // whatever they were handed; the rest give back what they took.
                let ty = if answers_bool(op) {
                    self.types.prim(TIRPrim::Bool)
                } else {
                    lt
                };
                self.make(TTIRExprKind::Binary { op, lhs: l, rhs: r }, ty, id)
            }

            TIRExprKind::Assign { op, place, value } => {
                let (p, v) = (self.expr(place), self.expr(value));
                // "assigning to one takes a `*`" -- the least the body asks of
                // it turns out to be more than a read.
                if let TTIRExprKind::Local(slot) = self.out.exprs[p].kind {
                    self.assigns_to(slot);
                }
                let (pt, vt) = (self.out.exprs[p].ty, self.out.exprs[v].ty);
                if self.types.unify(vt, pt).is_err() {
                    let (vt, pt) = (self.spell(vt), self.spell(pt));
                    self.errors.push(
                        Diagnostic::error(
                            format!("`{}` cannot be assigned to `{}`", vt, pt),
                            self.at(id),
                        )
                        .with_label("this is what is put there"),
                    );
                }
                let ty = self.types.null();
                self.make(TTIRExprKind::Assign { op, place: p, value: v }, ty, id)
            }

            // "A method, resolved to the one it calls. `.` and `::` are both
            // gone: which separator was written mattered to the resolver and to
            // nobody after it." The TIR has no method call of its own -- one is
            // a call of a field -- so which it is, is settled here.
            TIRExprKind::Call { callee, args } => {
                // `Shape::Line(5)` is a variant being built and not a fn being
                // called: which it is, is what the path names.
                if let Some(path) = self.flatten(callee) {
                    if let Some((of, index)) = self.variant_path(&path) {
                        return self.variant_lit(of, index, &args, id);
                    }
                }
                if let TIRExprKind::Field { base, name } = self.tir.exprs[callee].kind.clone() {
                    if let Some(made) = self.method(base, &name, &args, id) {
                        return made;
                    }
                }
                let c = self.expr(callee);
                let made: Vec<TTIRExprId> = args.iter().map(|&a| self.expr(a)).collect();
                let ty = self.calling(c, &made, id);
                self.make(TTIRExprKind::Call { callee: c, args: made }, ty, id)
            }

            TIRExprKind::If { cond, then, els } => {
                let c = self.expr(cond);
                let want = self.types.prim(TIRPrim::Bool);
                let got = self.out.exprs[c].ty;
                if self.types.unify(got, want).is_err() {
                    let got = self.spell(got);
                    self.errors.push(
                        Diagnostic::error(
                            format!("an `if` asks a `bool` and this is `{}`", got),
                            self.at(cond),
                        )
                        .with_label("this is the condition"),
                    );
                }
                let t = self.expr(then);
                let e = els.map(|e| self.expr(e));
                let tt = self.out.exprs[t].ty;
                let ty = match e {
                    Some(e) => {
                        let et = self.out.exprs[e].ty;
                        match self.types.unify(tt, et) {
                            Ok(one) => one,
                            Err(_) => {
                                let (tt, et) = (self.spell(tt), self.spell(et));
                                self.errors.push(
                                    Diagnostic::error(
                                        format!("one way gives `{}` and the other `{}`", tt, et),
                                        self.at(id),
                                    )
                                    .with_label("an `if` is worth one type"),
                                );
                                self.types.error()
                            }
                        }
                    }
                    // "A block with no trailing expression is `null`", and an
                    // `if` with no `else` is the same answer.
                    None => self.types.null(),
                };
                self.make(TTIRExprKind::If { cond: c, then: t, els: e }, ty, id)
            }

            TIRExprKind::While { cond, body } => {
                let c = self.expr(cond);
                let want = self.types.prim(TIRPrim::Bool);
                let got = self.out.exprs[c].ty;
                if self.types.unify(got, want).is_err() {
                    let got = self.spell(got);
                    self.errors.push(
                        Diagnostic::error(
                            format!("a `while` asks a `bool` and this is `{}`", got),
                            self.at(cond),
                        )
                        .with_label("this is the condition"),
                    );
                }
                self.breaks.push(Vec::new());
                let b = self.expr(body);
                let ty = self.loop_value(id);
                self.make(TTIRExprKind::While { cond: c, body: b }, ty, id)
            }

            TIRExprKind::Cast { value, ty } => {
                let v = self.expr(value);
                let to = self.ty(ty);
                self.make(TTIRExprKind::Cast(v), to, id)
            }

            TIRExprKind::TupleLit(members) => {
                let made: Vec<TTIRExprId> = members.iter().map(|&m| self.expr(m)).collect();
                let tys: Vec<TyId> = made.iter().map(|&m| self.out.exprs[m].ty).collect();
                let ty = self.types.intern(Ty::Tuple(tys));
                self.make(TTIRExprKind::TupleLit(made), ty, id)
            }

            TIRExprKind::ArrayLit(elems) => {
                let made: Vec<TTIRExprId> = elems.iter().map(|&e| self.expr(e)).collect();
                let elem = match made.first() {
                    Some(&first) => {
                        let mut held = self.out.exprs[first].ty;
                        for &other in &made[1..] {
                            let ty = self.out.exprs[other].ty;
                            match self.types.unify(held, ty) {
                                Ok(one) => held = one,
                                Err(_) => {
                                    self.errors.push(
                                        Diagnostic::error(
                                            "an array holds one type".to_string(),
                                            self.at(id),
                                        )
                                        .with_label("these are not all one"),
                                    );
                                    held = self.types.error();
                                    break;
                                }
                            }
                        }
                        held
                    }
                    None => self.types.fresh(),
                };
                let ty = self.types.intern(Ty::Array { elem, len: made.len() as u64 });
                self.make(TTIRExprKind::ArrayLit(made), ty, id)
            }

            TIRExprKind::TupleIndex { base, index } => {
                let b = self.expr(base);
                let bt = self.out.exprs[b].ty;
                let ty = match self.types.get(bt).clone() {
                    Ty::Tuple(members) => members.get(index as usize).copied().unwrap_or_else(|| {
                        self.errors.push(
                            Diagnostic::error(
                                format!("this tuple has no `.{}`", index),
                                self.at(id),
                            )
                            .with_label("it is not that long"),
                        );
                        self.types.error()
                    }),
                    _ => self.types.error(),
                };
                self.make(TTIRExprKind::TupleIndex { base: b, index }, ty, id)
            }

            TIRExprKind::Field { base, name } => {
                let b = self.expr(base);
                let bt = self.out.exprs[b].ty;
                match self.field_of(bt, &name) {
                    Some((index, ty)) => {
                        self.make(TTIRExprKind::Field { base: b, index }, ty, id)
                    }
                    None => {
                        let held = self.spell(bt);
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` has no field `{}`", held, name),
                                self.at(id),
                            )
                            .with_label("no such field"),
                        );
                        let ty = self.types.error();
                        self.make(TTIRExprKind::Field { base: b, index: 0 }, ty, id)
                    }
                }
            }

            TIRExprKind::Index { base, index } => {
                let b = self.expr(base);
                let i = self.expr(index);
                let bt = self.out.exprs[b].ty;
                let ty = match self.types.get(bt).clone() {
                    Ty::Array { elem, .. } | Ty::Run(elem) => elem,
                    Ty::Ref { inner, .. } => match self.types.get(inner).clone() {
                        Ty::Array { elem, .. } | Ty::Run(elem) => elem,
                        _ => self.types.error(),
                    },
                    _ => self.types.error(),
                };
                self.make(TTIRExprKind::Index { base: b, index: i }, ty, id)
            }

            // The three that do not come back: "expressions of type `never`,
            // the empty type" (§5).
            TIRExprKind::Return(value) => {
                let v = value.map(|v| self.expr(v));
                if let Some(v) = v {
                    let ret = self.frames.last().expect("a frame").ret;
                    let found = self.out.exprs[v].ty;
                    if self.types.unify(found, ret).is_err() {
                        let (found, ret) = (self.spell(found), self.spell(ret));
                        self.errors.push(
                            Diagnostic::error(
                                format!("this returns `{}` and the signature says `{}`", found, ret),
                                self.at(id),
                            )
                            .with_label("this is what goes back"),
                        );
                    }
                }
                let ty = self.types.never();
                self.make(TTIRExprKind::Return(v), ty, id)
            }
            TIRExprKind::Break(value) => {
                let v = value.map(|v| self.expr(v));
                // "Every loop takes one -- `break x` in a `for` and a
                // conditional `while` as much as in a `while true` -- and where
                // none is given the loop is `null`" (§5.1).
                let held = match v {
                    Some(v) => self.out.exprs[v].ty,
                    None => self.types.null(),
                };
                match self.breaks.last_mut() {
                    Some(out) => out.push(held),
                    None => self.errors.push(
                        Diagnostic::error("`break` is not in a loop".to_string(), self.at(id))
                            .with_label("there is nothing here to leave"),
                    ),
                }
                let ty = self.types.never();
                self.make(TTIRExprKind::Break(v), ty, id)
            }
            TIRExprKind::Continue => {
                let ty = self.types.never();
                self.make(TTIRExprKind::Continue, ty, id)
            }

            TIRExprKind::StructLit { base, fields } => self.struct_lit(base, &fields, id),
            TIRExprKind::Match { scrutinee, arms } => self.matching(scrutinee, &arms, id),

            TIRExprKind::Closure { is_move, params, body } => {
                self.closure(is_move, &params, body, id)
            }

            TIRExprKind::Map { hashed, entries } => self.map(hashed, &entries, id),
            TIRExprKind::Set { hashed, elems } => self.set(hashed, &elems, id),
            TIRExprKind::Range { op, start, end } => self.range(op, start, end, id),

            TIRExprKind::For { name, iter, body } => self.for_each(&name, iter, body, id),

            // "`::` reaches into a namespace, a module or a type" (§5). What it
            // reaches is a declaration, so the whole path is looked up rather
            // than the base being typed as a value -- an enum is not one.
            TIRExprKind::Path { .. } => match self.flatten(id) {
                Some(path) => self.named(&path, id),
                None => self.not_yet("a `::` after something that is not a name", id),
            },

            // `foo<MyType>(x)`. The arguments are put where the parameters
            // stood and are spent doing it: the tree below holds the type they
            // made, and nothing of the writing.
            TIRExprKind::TypeArgs { base, args } => {
                let held: Vec<TyId> = args
                    .iter()
                    .filter_map(|a| match a {
                        crate::tir::tir_nodes::TIRGenericArg::Type(ty) => Some(self.ty(*ty)),
                        crate::tir::tir_nodes::TIRGenericArg::Life(_) => None,
                    })
                    .collect();
                let made = self.expr(base);
                let ty = self.instantiate(made, Some(held), id);
                // The node is spent: what is left is the base, with the type
                // the arguments made of it.
                self.out.exprs[made].ty = ty;
                made
            }
            // `self` is the receiver's slot, and the receiver is a parameter
            // like any other -- "a receiver comes first and comes only in a
            // method" is the checker's, and this is where it is taken as read.
            TIRExprKind::SelfExpr => match self.slot("self", self.at(id)) {
                Some(slot) => {
                    let ty = self.locals()[slot].ty;
                    self.make(TTIRExprKind::Local(slot), ty, id)
                }
                None => {
                    self.errors.push(
                        Diagnostic::error("`self` is not in a method".to_string(), self.at(id))
                            .with_label("nothing here has a receiver")
                            .with_help("a receiver is written `self`, `&self` or `*self`"),
                    );
                    self.errored(id)
                }
            },
        }
    }

    // A block, and the scope its statements stand in.
    fn block(
        &mut self,
        stmts: &[TIRStmt],
        tail: Option<TIRExprId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
        let mut made = Vec::new();
        for stmt in stmts {
            match stmt {
                TIRStmt::Let { is_unsafe, intro, name, ty, init, .. } => {
                    let init = init.map(|i| self.expr(i));
                    let written = ty.map(|t| self.ty(t));
                    let ty = match (written, init) {
                        (Some(want), Some(got)) => {
                            let found = self.out.exprs[got].ty;
                            if self.types.unify(found, want).is_err() {
                                let (found, want) = (self.spell(found), self.spell(want));
                                self.errors.push(
                                    Diagnostic::error(
                                        format!("this is `{}` and the name says `{}`", found, want),
                                        self.at(at),
                                    )
                                    .with_label("the two disagree"),
                                );
                            }
                            let at = self.at(at);
                            self.stands_as(found, want, at);
                            want
                        }
                        (Some(want), None) => want,
                        (None, Some(got)) => self.out.exprs[got].ty,
                        // Neither written: "a `<var_decl>` with neither is a
                        // shape the grammar admits and the checker has to
                        // answer for" -- a hole, until something fills it.
                        (None, None) => self.types.fresh(),
                    };
                    let where_ = match init {
                        Some(init) => Span::at(
                            self.out.exprs[init].line,
                            self.out.exprs[init].col,
                        ),
                        None => self.here,
                    };
                    let local = self.bind(name.clone(), ty, *intro, where_);
                    made.push(TTIRStmt::Let { is_unsafe: *is_unsafe, local, init });
                }
                TIRStmt::Expr { is_unsafe, expr } => {
                    let expr = self.expr(*expr);
                    made.push(TTIRStmt::Expr { is_unsafe: *is_unsafe, expr });
                }
                TIRStmt::Item(item) => {
                    if let Some(made_item) = self.made[*item] {
                        made.push(TTIRStmt::Item(made_item));
                    }
                }
            }
        }
        let tail = tail.map(|t| self.expr(t));
        self.frames.last_mut().expect("a frame").scopes.pop();
        // "A block is an expression, and its value is the trailing expression
        // -- the one left without a `;`. A block with no trailing expression is
        // `null`."
        let ty = match tail {
            Some(t) => self.out.exprs[t].ty,
            None => self.types.null(),
        };
        self.make(TTIRExprKind::Block { stmts: made, tail }, ty, at)
    }

    // What a call comes to: the callee has to be a fn, and what it takes has to
    // agree with what it was handed.
    fn calling(&mut self, callee: TTIRExprId, args: &[TTIRExprId], at: TIRExprId) -> TyId {
        // Every parameter of what is called gets a hole, so `id(1)` works out
        // its own `T` -- "what it stands for is settled at the call and not at
        // the declaration".
        let ct = self.instantiate(callee, None, at);
        let Ty::Fn { params, ret, .. } = self.types.get(ct).clone() else {
            if !matches!(self.types.get(ct), Ty::Error) {
                let ct = self.spell(ct);
                self.errors.push(
                    Diagnostic::error(format!("`{}` is not a fn", ct), self.at(at))
                        .with_label("this is called"),
                );
            }
            return self.types.error();
        };
        if params.len() != args.len() {
            self.errors.push(
                Diagnostic::error(
                    format!("this takes {} and was handed {}", params.len(), args.len()),
                    self.at(at),
                )
                .with_label("the wrong number of arguments"),
            );
            return ret;
        }
        for (i, (&want, &got)) in params.iter().zip(args.iter()).enumerate() {
            let found = self.out.exprs[got].ty;
            if self.types.unify(found, want).is_err() {
                let (found, want) = (self.spell(found), self.spell(want));
                self.errors.push(
                    Diagnostic::error(
                        format!("argument {} is `{}` and it takes `{}`", i + 1, found, want),
                        self.at(at),
                    )
                    .with_label("this is what it was handed"),
                );
            }
            let at = self.at(at);
            self.stands_as(found, want, at);
        }
        ret
    }

    // The type a declaration stands for where its name is used as a value.
    fn item_ty(&mut self, item: TTIRItemId) -> TyId {
        match &self.out.items[item].kind {
            TTIRItemKind::Fn(f) => f.ty,
            TTIRItemKind::Const { ty, .. } | TTIRItemKind::Global { ty, .. } => *ty,
            _ => self.types.error(),
        }
    }

    // A field by the name it was written with, and the index it turned out to
    // be: "Reached by index rather than by name: which field `x` is, is
    // settled."
    fn field_of(&mut self, ty: TyId, name: &str) -> Option<(usize, TyId)> {
        // A reference stands for the place it refers to, so reaching into one
        // reaches into what it refers to (§3).
        let held = match self.types.get(ty).clone() {
            Ty::Ref { inner, .. } => inner,
            _ => ty,
        };
        let Ty::Named { item, .. } = self.types.get(held).clone() else { return None };
        let TTIRItemKind::Struct { fields, .. } = &self.out.items[item].kind else {
            return None;
        };
        fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == name)
            .map(|(i, f)| (i, f.ty))
    }
}

// Whether an operator gives back a `bool` whatever it was handed.
fn answers_bool(op: TIRBinOp) -> bool {
    matches!(
        op,
        TIRBinOp::Eq | TIRBinOp::Ne | TIRBinOp::Lt | TIRBinOp::Gt | TIRBinOp::Le
            | TIRBinOp::Ge | TIRBinOp::And | TIRBinOp::Or | TIRBinOp::Xor
    )
}

#[cfg(test)]
mod tests;

// ---- Struct literals ------------------------------------------------------

impl<'a> Lowerer<'a> {
    // `Point { x: 1, y: 2 }`. The fields come out in the order they were
    // declared and not the order they were written -- "In declaration order,
    // whatever order they were written in" -- so everything below this reads
    // one shape whatever the writer chose.
    fn struct_lit(
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

    fn errored(&mut self, at: TIRExprId) -> TTIRExprId {
        let ty = self.types.error();
        self.make(TTIRExprKind::Literal(TIRLit::Null), ty, at)
    }
}

// ---- Match ----------------------------------------------------------------

impl<'a> Lowerer<'a> {
    // Every arm tested against the one scrutinee, and every arm worth the one
    // type. A pattern binds names, and what it binds stands in that arm's body
    // and nowhere else.
    fn matching(
        &mut self,
        scrutinee: TIRExprId,
        arms: &[crate::tir::tir_nodes::TIRArm],
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
            let body = self.expr(arm.body);
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

    fn make_pat(&mut self, kind: TTIRPatKind, ty: TyId, at: TIRPatId) -> TTIRPatId {
        let held = &self.tir.pats[at];
        self.out.pats.push(crate::tir::ttir_nodes::TTIRPat {
            kind,
            ty,
            line: held.line,
            col: held.col,
        });
        self.out.pats.len() - 1
    }

    fn pat_at(&self, at: TIRPatId) -> Span {
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
                let named = self.names.get(&path.join("::")).copied();
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
                    let ty = self.types.intern(Ty::Named { item: of, args: Vec::new(), regions: Vec::new() });
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
                let ty = self.types.intern(Ty::Named { item: of, args: Vec::new(), regions: Vec::new() });
                self.hold(ty, want, id);
                let carried = self.payload_tys(of, index);
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
                    let ty = self.types.intern(Ty::Named { item: of, args: Vec::new(), regions: Vec::new() });
                    self.hold(ty, want, id);
                    let named = self.payload_names(of, index);
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
                let Some(item) = self.names.get(&path.join("::")).copied() else {
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
                let regions = self.named_regions(item, &[], self.pat_at(id));
                let ty = self.types.intern(Ty::Named { item, args: Vec::new(), regions });
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

    // A name that binds: a slot of the body, standing in this arm alone.
    fn binding(&mut self, path: &[String], want: TyId, id: TIRPatId) -> TTIRPatId {
        if path.len() != 1 {
            let name = path.join("::");
            self.errors.push(
                Diagnostic::error(format!("nothing is called `{}`", name), self.pat_at(id))
                    .with_label("no such constant or variant")
                    .with_help("a name with a `::` in it tests; a bare one binds"),
            );
            return self.errored_pat(id, want);
        }
        let slot = self.bind(
            TIRBinding::Name(path[0].clone()),
            want,
            crate::tir::tir_nodes::TIRIntro::Let,
            self.pat_at(id),
        );
        self.make_pat(TTIRPatKind::Bind(slot), want, id)
    }

    fn errored_pat(&mut self, id: TIRPatId, want: TyId) -> TTIRPatId {
        self.make_pat(TTIRPatKind::Wildcard, want, id)
    }

    // A pattern's own type held against what it is tested on.
    // Whether a body hands a slot's value over rather than reading through it.
    // The four places §2 names -- an argument, a return, the right of an
    // assignment, a field of a literal being built -- come to one thing here: a
    // name standing for its value and not for a place reached into.
    //
    // Walked from the body's own value and not over the arena: "a
    // `TTIRLocalId` is a slot of the body that holds it, not of the program",
    // so the same number in two bodies is two different slots.
    fn hands_away(&self, body: TTIRBodyId, slot: TTIRLocalId) -> bool {
        self.given_away(self.out.bodies[body].value, slot)
    }

    // Whether a body writes to a slot, however it reaches it: a `var n = ..`
    // captured by value and assigned to is a closure with state of its own.
    fn writes_to(&self, body: TTIRBodyId, slot: TTIRLocalId) -> bool {
        self.out.exprs.iter().enumerate().any(|(id, e)| {
            matches!(&e.kind, TTIRExprKind::Assign { place, .. } if self.roots_at(*place, slot))
                && self.within(self.out.bodies[body].value, id)
        })
    }

    // Whether a place is reached from a slot: the name at the bottom of it.
    fn roots_at(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Local(held) => *held == slot,
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.roots_at(*base, slot),
            _ => false,
        }
    }

    // Whether one expression stands inside another, which is how a body says
    // which expressions are its own -- the arena holds every body's at once.
    fn within(&self, outer: TTIRExprId, id: TTIRExprId) -> bool {
        if outer == id {
            return true;
        }
        self.kids_of(outer).into_iter().any(|kid| self.within(kid, id))
    }

    // Everything one expression holds, whatever it is. A closure's body is not
    // among them: it is a body of its own and its slots are its own.
    fn kids_of(&self, id: TTIRExprId) -> Vec<TTIRExprId> {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                vec![*base]
            }
            TTIRExprKind::Index { base, index } => vec![*base, *index],
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => vec![*operand],
            TTIRExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            TTIRExprKind::Assign { place, value, .. } => vec![*place, *value],
            TTIRExprKind::Call { callee, args } => {
                std::iter::once(*callee).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::Method { recv, args, .. } => {
                std::iter::once(*recv).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => fields.clone(),
            TTIRExprKind::Map { entries, .. } => {
                entries.iter().flat_map(|&(k, v)| [k, v]).collect()
            }
            TTIRExprKind::Range { start, end, .. } => {
                [start, end].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::Block { stmts, tail } => {
                let mut held: Vec<TTIRExprId> = Vec::new();
                for stmt in stmts {
                    match stmt {
                        TTIRStmt::Let { init, .. } => held.extend(init.iter()),
                        TTIRStmt::Expr { expr, .. } => held.push(*expr),
                        TTIRStmt::Item(_) => {}
                    }
                }
                held.extend(tail.iter());
                held
            }
            TTIRExprKind::If { cond, then, els } => {
                [Some(cond), Some(then), els.as_ref()].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::While { cond, body } => vec![*cond, *body],
            TTIRExprKind::For { iter, body, .. } => vec![*iter, *body],
            TTIRExprKind::Match { scrutinee, arms } => std::iter::once(*scrutinee)
                .chain(arms.iter().map(|a| a.body))
                .collect(),
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                value.iter().copied().collect()
            }
            _ => Vec::new(),
        }
    }

    fn given_away(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        let kids: Vec<TTIRExprId> = match &self.out.exprs[id].kind {
            // Here it is, standing for its value: this is the handing over.
            TTIRExprKind::Local(held) => return *held == slot,
            // Reached into or borrowed, either of which leaves it where it is.
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. } => {
                return self.reaches_past(*base, slot)
            }
            TTIRExprKind::Index { base, index } => {
                return self.reaches_past(*base, slot) || self.given_away(*index, slot)
            }
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), operand }
            | TTIRExprKind::Unary { op: TIRUnaryOp::Addr, operand } => {
                return self.reaches_past(*operand, slot)
            }
            TTIRExprKind::Assign { place, value, .. } => {
                return self.reaches_past(*place, slot) || self.given_away(*value, slot)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => vec![*operand],
            TTIRExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            TTIRExprKind::Call { callee, args } => {
                std::iter::once(*callee).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::Method { recv, args, .. } => {
                std::iter::once(*recv).chain(args.iter().copied()).collect()
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => fields.clone(),
            TTIRExprKind::Map { entries, .. } => {
                entries.iter().flat_map(|&(k, v)| [k, v]).collect()
            }
            TTIRExprKind::Range { start, end, .. } => {
                [start, end].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::Block { stmts, tail } => {
                let mut held: Vec<TTIRExprId> = Vec::new();
                for stmt in stmts {
                    match stmt {
                        TTIRStmt::Let { init, .. } => held.extend(init.iter()),
                        TTIRStmt::Expr { expr, .. } => held.push(*expr),
                        TTIRStmt::Item(_) => {}
                    }
                }
                held.extend(tail.iter());
                held
            }
            TTIRExprKind::If { cond, then, els } => {
                [Some(cond), Some(then), els.as_ref()].into_iter().flatten().copied().collect()
            }
            TTIRExprKind::While { cond, body } => vec![*cond, *body],
            TTIRExprKind::For { iter, body, .. } => vec![*iter, *body],
            TTIRExprKind::Match { scrutinee, arms } => std::iter::once(*scrutinee)
                .chain(arms.iter().map(|a| a.body))
                .collect(),
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                value.iter().copied().collect()
            }
            // A closure inside a closure names the outer frame's slots through
            // its own captures, which the outer one already caught.
            _ => Vec::new(),
        };
        kids.into_iter().any(|kid| self.given_away(kid, slot))
    }

    // The same walk, of something being reached into rather than handed over:
    // the name at the bottom of it stays where it is, and anything else in it
    // is handed over as it would be anywhere.
    fn reaches_past(&self, id: TTIRExprId, slot: TTIRLocalId) -> bool {
        match &self.out.exprs[id].kind {
            TTIRExprKind::Local(_) => false,
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                self.reaches_past(*base, slot)
            }
            TTIRExprKind::Index { base, index } => {
                self.reaches_past(*base, slot) || self.given_away(*index, slot)
            }
            _ => self.given_away(id, slot),
        }
    }

    // Whether a type is copied where it is handed over. `Copy` is found by
    // name, as §2 says the compiler knows it.
    fn copies(&self, ty: TyId) -> bool {
        // Through a filled hole: this runs while the body's types are still
        // being worked out, and a number is a hole until something fixes it.
        match self.types.get(self.types.shallow(ty)) {
            Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Fn { .. } | Ty::Run(_) => true,
            // One nobody has worked out yet, and one that went wrong: both
            // read as copying, which is the answer that adds no second message
            // to a program that already has one.
            Ty::Var(_) | Ty::Error => true,
            Ty::Named { item, .. } => self.out.items.iter().any(|held| {
                matches!(&held.kind, TTIRItemKind::Impl { ty, of: Some(of), .. }
                    if matches!(self.types.get(*ty), Ty::Named { item: named, .. } if named == item)
                        && matches!(&self.out.items[*of].kind,
                            TTIRItemKind::Trait { name, .. } if name == "Copy"))
            }),
            _ => false,
        }
    }

    // "a closure stands where a weaker one is wanted: reading is less than
    // writing and writing is less than taking" -- and not the other way. This
    // is the half `unify` cannot say: it takes the greater of the two, which is
    // the right answer where a hole is being filled and the wrong one where a
    // person wrote what they wanted. So wherever what was written is one side
    // and what was found is the other, this is asked as well.
    fn stands_as(&mut self, found: TyId, want: TyId, at: Span) {
        let found = self.types.shallow(found);
        let want = self.types.shallow(want);
        let (Ty::Fn { uses: got, .. }, Ty::Fn { uses: asked, .. }) =
            (self.types.get(found).clone(), self.types.get(want).clone())
        else {
            return;
        };
        if got <= asked {
            return;
        }
        let (found, want) = (self.spell(found), self.spell(want));
        self.errors.push(
            Diagnostic::error(
                format!("this is `{}` and what wants it says `{}`", found, want),
                at,
            )
            .with_label("it may be called fewer times than that")
            .with_note("`fn` reads what a closure captured, `var fn` writes to it and `once fn` takes it")
            .with_help("a closure stands where a weaker one is wanted, and not the other way"),
        );
    }

    fn hold(&mut self, found: TyId, want: TyId, id: TIRPatId) {
        if self.types.unify(found, want).is_err() {
            let (found, want) = (self.spell(found), self.spell(want));
            self.errors.push(
                Diagnostic::error(
                    format!("this tests `{}` against `{}`", found, want),
                    self.pat_at(id),
                )
                .with_label("the two do not meet"),
            );
        }
    }

    // The enum a path names a variant of, and which variant it is. "`::`
    // reaches into a namespace, a module or a type" (§5) -- an enum is the
    // type, and the name after it is the variant, so `Color::Red` is the enum
    // named by everything but the last segment.
    fn variant_path(&self, path: &[String]) -> Option<(TTIRItemId, usize)> {
        if path.len() < 2 {
            return None;
        }
        let last = path.last()?;
        let of = *self.names.get(&path[..path.len() - 1].join("::"))?;
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else { return None };
        variants.iter().position(|v| v.name == *last).map(|i| (of, i))
    }

    // What one variant carries, by the names it gave them: a struct-shaped
    // variant names its fields, and a pattern may reach them by name.
    fn payload_names(&self, of: TTIRItemId, index: usize) -> Vec<(String, TyId)> {
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else {
            return Vec::new();
        };
        match variants.get(index).map(|v| &v.payload) {
            Some(TTIRPayload::Named(fields)) => {
                fields.iter().map(|f| (f.name.clone(), f.ty)).collect()
            }
            // A tuple variant names nothing, so nothing reaches it by name.
            _ => Vec::new(),
        }
    }

    // What one variant carries, as types.
    fn payload_tys(&self, of: TTIRItemId, index: usize) -> Vec<TyId> {
        let TTIRItemKind::Enum { variants, .. } = &self.out.items[of].kind else {
            return Vec::new();
        };
        match variants.get(index).map(|v| &v.payload) {
            Some(TTIRPayload::Tuple(tys)) => tys.clone(),
            Some(TTIRPayload::Named(fields)) => fields.iter().map(|f| f.ty).collect(),
            _ => Vec::new(),
        }
    }
}

// ---- Closures and methods -------------------------------------------------

impl<'a> Lowerer<'a> {
    // A closure is a body inside a body. Its parameters are slots of its own,
    // and every name it uses but did not declare is taken from the frame it was
    // written in -- which is what `catch` does as each name is met.
    fn closure(
        &mut self,
        is_move: bool,
        params: &[crate::tir::tir_nodes::TIRParam],
        body: TIRExprId,
        at: TIRExprId,
    ) -> TTIRExprId {
        // What it gives back is worked out from what its body comes to: a
        // closure writes no return type, there being nowhere to write one.
        let ret = self.types.fresh();
        self.frames.push(Frame::new(ret, is_move));

        let mut arg_tys = Vec::new();
        for p in params {
            let ty = match p.ty {
                Some(ty) => self.ty(ty),
                None => self.types.fresh(),
            };
            arg_tys.push(ty);
            self.bind(p.name.clone(), ty, crate::tir::tir_nodes::TIRIntro::Let, self.at(at));
        }

        let value = self.expr(body);
        let found = self.out.exprs[value].ty;
        if self.types.unify(found, ret).is_err() {
            let (found, ret) = (self.spell(found), self.spell(ret));
            self.errors.push(
                Diagnostic::error(
                    format!("this closure gives back `{}` and `{}` at once", found, ret),
                    self.at(at),
                )
                .with_label("it is worth one type"),
            );
        }

        // The frame comes off, and what it caught comes with it.
        let captures = self.frames.last().expect("a frame").captures.clone();
        // What calling it does to what it captured, which is the most any one
        // capture asks: "worked out per name, each taking the least the body
        // asks of it" (§5), and the closure is the most of those.
        //
        // A `move` capture is what takes: the closure owns the value, so a
        // second call would hand away what the first already did. A capture
        // the body assigns to is what writes. Everything else only reads, and
        // a closure that captured nothing reads nothing.
        let made = self.finish_body(value);
        let uses = captures
            .iter()
            .map(|c| match c.mode {
                // "By value is a copy where the name's type copies and a move
                // where it does not": a copy is the closure's own and calling
                // it changes nothing, and one that moved is only given away
                // where the body gives it away.
                TTIRCaptureMode::Value => {
                    let ty = self.out.bodies[made].locals[c.slot].ty;
                    if !self.copies(ty) && self.hands_away(made, c.slot) {
                        TIRFnUses::Takes
                    } else if self.writes_to(made, c.slot) {
                        // A `move` closure with a copy of its own that it
                        // writes to has state, and state is what one holder at
                        // a time is for.
                        TIRFnUses::Writes
                    } else {
                        TIRFnUses::Reads
                    }
                }
                TTIRCaptureMode::Ref(TIRRefOp::Mut) => TIRFnUses::Writes,
                TTIRCaptureMode::Ref(TIRRefOp::Imm) => TIRFnUses::Reads,
            })
            .max()
            .unwrap_or(TIRFnUses::Reads);
        let ty = self.types.intern(Ty::Fn { uses, params: arg_tys, ret, is_unsafe: false });
        self.make(TTIRExprKind::Closure { captures, body: made }, ty, at)
    }

    // A call of a field, where the field turns out to be a method. `None` where
    // it is not one -- a field holding a fn is called like anything else, and
    // that is a `Call` of a `Field`.
    fn method(
        &mut self,
        base: TIRExprId,
        name: &str,
        args: &[TIRExprId],
        at: TIRExprId,
    ) -> Option<TTIRExprId> {
        let recv = self.expr(base);
        let held = self.out.exprs[recv].ty;
        // A field of the same name wins: it is the nearer thing, and a struct
        // holding a fn is reached before an impl is looked in.
        if self.field_of(held, name).is_some() {
            return None;
        }
        let item = self.method_of(held, name)?;

        let made: Vec<TTIRExprId> = args.iter().map(|&a| self.expr(a)).collect();
        let TTIRItemKind::Fn(f) = &self.out.items[item].kind else { return None };
        let (fn_ty, takes_self) = (
            f.ty,
            matches!(f.params.first().map(|p| &p.name), Some(TIRBinding::SelfRecv(..))),
        );
        let Ty::Fn { params, ret, .. } = self.types.get(fn_ty).clone() else { return None };

        // The receiver is the first parameter, so what is left is what the call
        // was handed.
        let wanted: Vec<TyId> = if takes_self { params[1..].to_vec() } else { params.clone() };
        if wanted.len() != made.len() {
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` takes {} and was handed {}", name, wanted.len(), made.len()),
                    self.at(at),
                )
                .with_label("the wrong number of arguments"),
            );
        } else {
            for (i, (&want, &got)) in wanted.iter().zip(made.iter()).enumerate() {
                let found = self.out.exprs[got].ty;
                if self.types.unify(found, want).is_err() {
                    let (found, want) = (self.spell(found), self.spell(want));
                    self.errors.push(
                        Diagnostic::error(
                            format!("argument {} is `{}` and it takes `{}`", i + 1, found, want),
                            self.at(at),
                        )
                        .with_label("this is what it was handed"),
                    );
                }
                let at = self.at(at);
                self.stands_as(found, want, at);
            }
        }
        Some(self.make(TTIRExprKind::Method { recv, item, args: made }, ret, at))
    }

    // The method of that name written for that type. "an impl makes methods for
    // its type and holds nothing else" (§8), so this is every impl whose
    // subject is the type, and the member of it with that name.
    fn method_of(&mut self, ty: TyId, name: &str) -> Option<TTIRItemId> {
        // A reference stands for the place it refers to, so a method of the
        // referent is a method of the reference.
        let held = match self.types.get(ty).clone() {
            Ty::Ref { inner, .. } => inner,
            _ => ty,
        };
        let of = match self.types.get(held).clone() {
            Ty::Named { item, .. } => item,
            _ => return None,
        };
        for item in &self.out.items {
            let TTIRItemKind::Impl { ty: subject, members, .. } = &item.kind else { continue };
            let Ty::Named { item: written, .. } = self.types.get(*subject).clone() else {
                continue;
            };
            if written != of {
                continue;
            }
            for &member in members {
                if let TTIRItemKind::Fn(f) = &self.out.items[member].kind {
                    if f.name == name {
                        return Some(member);
                    }
                }
            }
        }
        None
    }
}

// ---- Maps, sets and ranges ------------------------------------------------
//
// All three are literal syntax for a type a library declares, which is the
// shape §8 settles: "A map and a set are `Map<K, V>` and `Set<T>`, and the
// hashed kinds are types of their own, `HashMap<K, V>` and `HashSet<T>` -- so
// which one you named says how it behaves, and a `#{` literal builds the hashed
// one." So nothing is built in here; the names are looked up like any other.

impl<'a> Lowerer<'a> {
    // `{1: 2}` and `#{1: 2}`. Every key is one type and every value another,
    // which is what makes a map a map rather than a list of pairs.
    fn map(
        &mut self,
        hashed: bool,
        entries: &[crate::tir::tir_nodes::TIRMapEntry],
        at: TIRExprId,
    ) -> TTIRExprId {
        let mut made = Vec::new();
        let mut key = self.types.fresh();
        let mut value = self.types.fresh();
        for entry in entries {
            let k = self.expr(entry.key);
            let v = self.expr(entry.value);
            key = self.agree(key, self.out.exprs[k].ty, "every key of a map is one type", at);
            value =
                self.agree(value, self.out.exprs[v].ty, "every value of a map is one type", at);
            made.push((k, v));
        }
        let ty = self.container(hashed, "Map", vec![key, value], at);
        self.make(TTIRExprKind::Map { hashed, entries: made }, ty, at)
    }

    // `{1, 2}` and `#{1, 2}`, and `{,}` which is the empty one.
    fn set(&mut self, hashed: bool, elems: &[TIRExprId], at: TIRExprId) -> TTIRExprId {
        let mut made = Vec::new();
        let mut elem = self.types.fresh();
        for &held in elems {
            let e = self.expr(held);
            elem = self.agree(elem, self.out.exprs[e].ty, "every element of a set is one type", at);
            made.push(e);
        }
        let ty = self.container(hashed, "Set", vec![elem], at);
        self.make(TTIRExprKind::Set { hashed, elems: made }, ty, at)
    }

    // `1..10`, `1..`, `..10` and `..`. One type for however many bounds were
    // written, and a `..` with neither is a hole until something fills it.
    fn range(
        &mut self,
        op: crate::tir::tir_nodes::TIRRangeOp,
        start: Option<TIRExprId>,
        end: Option<TIRExprId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        let mut bound = self.types.fresh();
        let start = start.map(|s| self.expr(s));
        let end = end.map(|e| self.expr(e));
        for &held in start.iter().chain(end.iter()) {
            bound = self.agree(bound, self.out.exprs[held].ty, "a range runs between one type", at);
        }
        // The prose names `Map` and `Set` and does not name this one, so the
        // name is a choice: one `Range<T>` for all four shapes, the bounds
        // being optional in the value rather than in the type. Four types for
        // four shapes is the other answer, and nothing here settles it.
        let ty = self.container(false, "Range", vec![bound], at);
        self.make(TTIRExprKind::Range { op, start, end }, ty, at)
    }

    // The declaration a literal builds. `#` makes it the hashed kind, which is
    // "a type of its own" and not the same one with a flag.
    //
    // What a `{` literal with no annotation builds is left open by §8. It
    // builds the ordered one here, `#` being what the language spends on saying
    // hashed -- so a literal with nothing on it is the one with nothing on it.
    fn container(
        &mut self,
        hashed: bool,
        kind: &str,
        args: Vec<TyId>,
        at: TIRExprId,
    ) -> TyId {
        let name = if hashed { format!("Hash{}", kind) } else { kind.to_string() };
        match self.names.get(&name).copied() {
            Some(item) if matches!(
                self.out.items[item].kind,
                TTIRItemKind::Struct { .. } | TTIRItemKind::Enum { .. }
            ) =>
            {
                let regions = self.named_regions(item, &[], self.at(at));
                self.types.intern(Ty::Named { item, args, regions })
            }
            _ => {
                self.errors.push(
                    Diagnostic::error(format!("no type is called `{}`", name), self.at(at))
                        .with_label("this builds one")
                        .with_note("a literal is syntax for a type a library declares, and this suite declares none"),
                );
                self.types.error()
            }
        }
    }

    // Two types that have to be one, with what to say where they are not.
    fn agree(&mut self, held: TyId, found: TyId, what: &str, at: TIRExprId) -> TyId {
        match self.types.unify(held, found) {
            Ok(one) => one,
            Err(_) => {
                let (held, found) = (self.spell(held), self.spell(found));
                self.errors.push(
                    Diagnostic::error(format!("`{}` and `{}` are not one type", held, found), self.at(at))
                        .with_label(what),
                );
                self.types.error()
            }
        }
    }
}

// ---- Loops ----------------------------------------------------------------

impl<'a> Lowerer<'a> {
    // `for x in it`. The loop variable is a slot of the body, bound afresh each
    // turn, and what it holds is what the iterable holds.
    fn for_each(
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
    fn loop_value(&mut self, at: TIRExprId) -> TyId {
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

// ---- Paths, variants and generic arguments --------------------------------

impl<'a> Lowerer<'a> {
    // The path an expression spells, where it spells one. A `::` chain of names
    // and nothing else: "`::` reaches into a namespace, a module or a type",
    // and all three are declarations rather than values.
    fn flatten(&self, id: TIRExprId) -> Option<Vec<String>> {
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
    fn named(&mut self, path: &[String], id: TIRExprId) -> TTIRExprId {
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
    fn variant_lit(
        &mut self,
        of: TTIRItemId,
        index: usize,
        args: &[TIRExprId],
        at: TIRExprId,
    ) -> TTIRExprId {
        let carried = self.payload_tys(of, index);
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

        let ty = self.types.intern(Ty::Named { item: of, args: Vec::new(), regions: Vec::new() });
        self.make(TTIRExprKind::VariantLit { item: of, variant: index, fields: made }, ty, at)
    }

    // What a declaration's type comes to at one use of it. A generic is written
    // once and used many times, so every parameter is put out of the way before
    // anything is held to it -- with the arguments where they were written, and
    // with a hole for each where they were not.
    //
    // "what it stands for is settled at the call and not at the declaration",
    // which is the whole of why this happens here and not in `resolve`.
    fn instantiate(
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

// ---- Bounds ---------------------------------------------------------------

impl<'a> Lowerer<'a> {
    // Which types answer each trait. "an impl makes methods for its type" and
    // an `impl Show for Buf` is Buf saying it answers Show -- so the impls are
    // the whole of what a bound can be held against.
    fn gather_impls(&mut self) {
        for id in 0..self.out.items.len() {
            let TTIRItemKind::Impl { ty, of: Some(held), .. } = &self.out.items[id].kind else {
                continue;
            };
            let (ty, held) = (*ty, *held);
            self.answers.entry(held).or_default().push(ty);
        }
    }

    // Whether one type is held to one bound, said where it is not.
    fn holds(&mut self, arg: TyId, bound: &TTIRBound, name: &str, at: TIRExprId) {
        // A region is another pass's, and a type nobody worked out has been
        // reported once already.
        let TTIRBound::Trait(want) = bound else { return };
        // Followed first: a hole that was filled still reads as one in the
        // arena, and what filled it is what is being held to the bound.
        let arg = self.types.shallow(arg);
        if matches!(self.types.get(arg), Ty::Var(_) | Ty::Error) {
            return;
        }
        let Ty::Named { item: held, .. } = self.types.get(*want).clone() else { return };
        if self.answers_to(arg, held) {
            return;
        }
        let (arg, held) = (self.spell(arg), self.spell(*want));
        self.errors.push(
            Diagnostic::error(format!("`{}` does not answer `{}`", arg, held), self.at(at))
                .with_label(format!("`{}` is held to it here", name))
                .with_help(format!("`impl {} for {}` is how a type says it does", held, arg)),
        );
    }

    // Whether a type answers a trait: an impl of it written for that type, or
    // -- where the type is a parameter of the declaration being walked -- a
    // bound saying it will be. A generic holding another generic to a trait is
    // answered by the caller and not here.
    fn answers_to(&mut self, arg: TyId, want: TTIRItemId) -> bool {
        let arg = self.types.shallow(arg);
        if let Ty::Param { index, .. } = self.types.get(arg).clone() {
            return self.param_bounds(index).iter().any(|bound| {
                matches!(bound, TTIRBound::Trait(held)
                    if matches!(self.types.get(*held), Ty::Named { item, .. } if *item == want))
            });
        }
        let Some(written) = self.answers.get(&want) else { return false };
        let held = head_of(self.types.get(arg));
        written.clone().iter().any(|&subject| head_of(self.types.get(subject)) == held)
    }

    // What the declaration being walked holds its own parameter at `index` to.
    fn param_bounds(&self, index: usize) -> Vec<TTIRBound> {
        let Some(name) = self.params.get(index) else { return Vec::new() };
        for item in &self.out.items {
            let TTIRItemKind::Fn(f) = &item.kind else { continue };
            if let Some(TTIRGeneric::Type { name: held, bounds }) = f.generics.get(index) {
                if held == name {
                    return bounds.clone();
                }
            }
        }
        Vec::new()
    }
}

// What a type is, for asking whether an impl was written for it. A declaration
// by the one it is, and anything else by itself: `impl Copy for i32` is written
// for the primitive and not for a name.
#[derive(PartialEq, Eq)]
enum Head {
    Named(TTIRItemId),
    Exact(String),
}

fn head_of(ty: &Ty) -> Head {
    match ty {
        Ty::Named { item, .. } => Head::Named(*item),
        other => Head::Exact(format!("{:?}", other)),
    }
}

// ---- Exhaustiveness -------------------------------------------------------
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
    fn exhaustive(
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
                path.len() == 1 && !self.names.contains_key(&path[0])
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
