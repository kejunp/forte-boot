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
// What it does not do yet, and says so where it meets one: a `match`, a `for`,
// a closure, a method call, a struct or variant literal, a map or a set, a
// range, and a call with type arguments written at it. Each of those gets a
// `Ty::Error` and one message, which is what that type is for -- "so one
// mistake costs one message and not every message after it". The tree it hands
// on is honest about what it could not work out rather than quietly wrong about
// it, which is the difference between a pass that is unfinished and one that
// lies.
//
// Regions are not worked out either: every `Ty::Ref` gets region 0. Comparing
// them is a pass of its own (§3), and `types::unify` already leaves them alone.
//
// One more thing it gets wrong, and knowingly. A number with no suffix is a
// hole, so that `let x: i64 = 5` puts an i64 there and `let y: u8 = 5` a u8 --
// which is what a hole is for. The cost is that the hole will take *anything*:
// `if 5 { }` is accepted, the 5 having become a `bool`. What is wanted is a
// hole that only numbers fill, which is one more kind of hole than `Types` has.
// Until it has one, a number is too free rather than too fixed, and that is the
// direction that accepts a wrong program rather than refusing a right one.

// Nothing has called this until now: the driver stops at the TIR, and this is
// what carries it past. The allow covers the parts of the surface no caller has
// reached yet.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::sema::types::Types;
use crate::tir::tir_nodes::{
    TIRAttrs, TIRBinOp, TIRBinding, TIRExprId, TIRExprKind, TIRFn, TIRGeneric, TIRItemId,
    TIRItemKind, TIRLit, TIRPatId, TIRPatKind, TIRPrim, TIRProgram, TIRRefOp, TIRStmt,
    TIRTypeId, TIRTypeKind, TIRVis,
};
use crate::tir::ttir_nodes::{
    TTIRBody, TTIRBodyId, TTIRCapture, TTIRCaptureMode, TTIRExpr, TTIRExprId, TTIRExprKind,
    TTIRFieldDecl, TTIRFn,
    TTIRGeneric, TTIRItem, TTIRItemId, TTIRItemKind, TTIRLocal, TTIRLocalId, TTIRModule,
    TTIRParam, TTIRPatId, TTIRPatKind, TTIRPayload, TTIRProgram, TTIRStmt, TTIRVariant, Ty,
    TyId,
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
        let roots: Vec<TIRItemId> = self.tir.roots.clone();
        self.declare(&roots, &[]);
        self.resolve(&roots);
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
                        generics: Vec::new(), wheres: Vec::new(), fields: Vec::new(),
                    },
                ),
                TIRItemKind::Enum { vis, name, .. } => (
                    name.clone(),
                    TTIRItemKind::Enum {
                        vis: *vis, attrs: TIRAttrs::default(), name: name.clone(),
                        generics: Vec::new(), wheres: Vec::new(), variants: Vec::new(),
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
            body: None,
        })
    }
}

// ---- 2. Resolving what was written ----------------------------------------

impl<'a> Lowerer<'a> {
    fn resolve(&mut self, items: &[TIRItemId]) {
        for &id in items {
            let Some(made) = self.made[id] else { continue };
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    self.params = names_of(&f.generics);
                    let generics = self.generics(&f.generics);
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
                            None => self.receiver_ty(&p.name),
                        })
                        .collect();
                    let ret = match f.ret {
                        Some(ret) => self.ty(ret),
                        // "A `<return_type_opt>` left out is `null`" (§2).
                        None => self.types.null(),
                    };
                    let ty = self.types.intern(Ty::Fn {
                        params: arg_tys,
                        ret,
                        is_unsafe: f.is_unsafe,
                    });
                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.generics = generics;
                    held.params = params;
                    held.ret = ret;
                    held.ty = ty;
                    self.params.clear();
                }

                TIRItemKind::Struct { name: _, generics, fields, .. } => {
                    self.params = names_of(&generics);
                    let made_generics = self.generics(&generics);
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
                    self.params = names_of(&generics);
                    let made_generics = self.generics(&generics);
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
                    self.params = names_of(&generics);
                    let made_generics = self.generics(&generics);
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

                TIRItemKind::Impl { generics, ty, for_ty, members, .. } => {
                    self.params = names_of(&generics);
                    let made_generics = self.generics(&generics);
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
                    let TTIRItemKind::Impl { generics, ty, of: written, members, .. } =
                        &mut self.out.items[made].kind
                    else {
                        continue;
                    };
                    *generics = made_generics;
                    *ty = subject;
                    *written = of;
                    *members = inner;
                    self.params.clear();
                }

                TIRItemKind::Import { .. } => {}
            }
        }
    }

    // What `self` is. An impl names the type it is written for, and that is the
    // whole of what a receiver's type comes from.
    //
    // A trait's is another matter: the type is whatever answers the trait, and
    // `Ty` has no way to say "the one this is about". So a trait's receiver is
    // an `Error` -- said once here rather than left as a hole that would be
    // reported as one the checker forgot.
    fn receiver_ty(&mut self, name: &TIRBinding) -> TyId {
        let TIRBinding::SelfRecv(how) = name else { return self.types.fresh() };
        let Some(subject) = self.subject else { return self.types.error() };
        match how {
            // "A bare `self` takes the value whole and so moves it."
            crate::tir::tir_nodes::TIRSelf::Value => subject,
            crate::tir::tir_nodes::TIRSelf::Ref => {
                self.types.intern(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: subject })
            }
            crate::tir::tir_nodes::TIRSelf::Mut => {
                self.types.intern(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: subject })
            }
        }
    }

    fn generics(&mut self, held: &[TIRGeneric]) -> Vec<TTIRGeneric> {
        held.iter()
            .map(|g| match g {
                TIRGeneric::Type { name, .. } => TTIRGeneric::Type {
                    name:   name.clone(),
                    // A bound is a trait, and holding one to it wants the pass
                    // that checks traits. Kept empty rather than guessed at.
                    bounds: Vec::new(),
                },
                TIRGeneric::Life { name, .. } => TTIRGeneric::Life {
                    name:   name.clone(),
                    region: 0,
                    bounds: Vec::new(),
                },
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
        let TIRTypeKind::Named { path, .. } = &self.tir.types[ty].kind else { return None };
        self.names.get(&path.join("::")).copied()
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
                let args: Vec<TyId> = args
                    .iter()
                    .filter_map(|a| match a {
                        crate::tir::tir_nodes::TIRGenericArg::Type(ty) => Some(self.ty(*ty)),
                        // A lifetime argument names a region, and regions are
                        // another pass's.
                        crate::tir::tir_nodes::TIRGenericArg::Life(_) => None,
                    })
                    .collect();
                match self.names.get(&path.join("::")).copied() {
                    // "an alias is a name for a type and not a type, so once
                    // the resolver has followed it there is nothing left of it"
                    Some(item) => match &self.out.items[item].kind {
                        TTIRItemKind::TypeAlias { ty, .. } => *ty,
                        _ => self.types.intern(Ty::Named { item, args }),
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

            // Region 0 for every one: how long a reference is good for is a
            // pass of its own, and `types::unify` leaves them alone.
            TIRTypeKind::Ref { op, inner, .. } => {
                let inner = self.ty(inner);
                self.types.intern(Ty::Ref { op, life: 0, inner })
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

// ---- 3. Bodies ------------------------------------------------------------

impl<'a> Lowerer<'a> {
    fn bodies(&mut self, items: &[TIRItemId]) {
        for &id in items {
            match self.tir.items[id].kind.clone() {
                TIRItemKind::Fn(f) => {
                    let Some(made) = self.made[id] else { continue };
                    let Some(value) = f.body else { continue };
                    self.params = names_of(&f.generics);
                    let body = self.body(made, &f, value);
                    let TTIRItemKind::Fn(held) = &mut self.out.items[made].kind else {
                        continue;
                    };
                    held.body = Some(body);
                    self.params.clear();
                }
                TIRItemKind::Impl { ty, for_ty, members, .. } => {
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
                TIRBinding::SelfRecv(_) => TIRBinding::Name("self".to_string()),
                _ => p.name.clone(),
            };
            let slot = self.bind(held, ty, crate::tir::tir_nodes::TIRIntro::Let);
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
        self.finish_body(out)
    }

    fn finish_body(&mut self, value: TTIRExprId) -> TTIRBodyId {
        let frame = self.frames.pop().expect("a frame");
        self.out.bodies.push(TTIRBody { locals: frame.locals, value });
        self.out.bodies.len() - 1
    }

    fn bind(
        &mut self,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
    ) -> TTIRLocalId {
        let at = self.frames.len() - 1;
        self.into_frame(at, name, ty, intro)
    }

    fn into_frame(
        &mut self,
        at: usize,
        name: TIRBinding,
        ty: TyId,
        intro: crate::tir::tir_nodes::TIRIntro,
    ) -> TTIRLocalId {
        let frame = &mut self.frames[at];
        frame.locals.push(TTIRLocal { name: name.clone(), ty, intro, line: 1, col: 1 });
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
    fn slot(&mut self, name: &str) -> Option<TTIRLocalId> {
        let depth = self.frames.len();
        for at in (0..depth).rev() {
            let found = self.frames[at]
                .scopes
                .iter()
                .rev()
                .find_map(|scope| scope.get(name).copied());
            let Some(mut held) = found else { continue };
            for inner in at + 1..depth {
                held = self.catch(inner, held, name);
            }
            return Some(held);
        }
        None
    }

    // One name of the frame outside `at`, given a slot inside it. "A name the
    // body uses but did not declare is captured, and how is worked out per
    // name, each taking the least the body asks of it" -- so it starts at a
    // `&` and is sharpened to a `*` where the body assigns to it.
    fn catch(&mut self, at: usize, outer: TTIRLocalId, name: &str) -> TTIRLocalId {
        if let Some(&held) = self.frames[at].caught.get(&outer) {
            return self.frames[at].captures[held].slot;
        }
        let held = &self.frames[at - 1].locals[outer];
        let (ty, intro) = (held.ty, held.intro);
        let slot = self.into_frame(at, TIRBinding::Name(name.to_string()), ty, intro);
        let mode = if self.frames[at].is_move {
            TTIRCaptureMode::Value
        } else {
            TTIRCaptureMode::Ref(TIRRefOp::Imm)
        };
        let frame = &mut self.frames[at];
        frame.captures.push(TTIRCapture { outer, slot, mode, line: 1, col: 1 });
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
            TIRExprKind::Name(path) => {
                if path.len() == 1 {
                    if let Some(slot) = self.slot(&path[0]) {
                        let ty = self.locals()[slot].ty;
                        return self.make(TTIRExprKind::Local(slot), ty, id);
                    }
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
                                .with_help("a name is a local, a parameter, or something declared"),
                        );
                        let ty = self.types.error();
                        self.make(TTIRExprKind::Literal(TIRLit::Null), ty, id)
                    }
                }
            }

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
                let b = self.expr(body);
                let ty = self.types.null();
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

            // Everything still to come. Each is one message and an `Error`.
            TIRExprKind::For { .. } => self.not_yet("a `for`", id),
            TIRExprKind::Path { .. } => self.not_yet("a `::` path into a value", id),
            TIRExprKind::TypeArgs { .. } => self.not_yet("type arguments at a call", id),
            // `self` is the receiver's slot, and the receiver is a parameter
            // like any other -- "a receiver comes first and comes only in a
            // method" is the checker's, and this is where it is taken as read.
            TIRExprKind::SelfExpr => match self.slot("self") {
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
                            want
                        }
                        (Some(want), None) => want,
                        (None, Some(got)) => self.out.exprs[got].ty,
                        // Neither written: "a `<var_decl>` with neither is a
                        // shape the grammar admits and the checker has to
                        // answer for" -- a hole, until something fills it.
                        (None, None) => self.types.fresh(),
                    };
                    let local = self.bind(name.clone(), ty, *intro);
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
        let ct = self.out.exprs[callee].ty;
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
        let ty = self.types.intern(Ty::Named { item, args: Vec::new() });
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
                    let ty = self.types.intern(Ty::Named { item: of, args: Vec::new() });
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
                let ty = self.types.intern(Ty::Named { item: of, args: Vec::new() });
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
                    let ty = self.types.intern(Ty::Named { item: of, args: Vec::new() });
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
                let ty = self.types.intern(Ty::Named { item, args: Vec::new() });
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
        );
        self.make_pat(TTIRPatKind::Bind(slot), want, id)
    }

    fn errored_pat(&mut self, id: TIRPatId, want: TyId) -> TTIRPatId {
        self.make_pat(TTIRPatKind::Wildcard, want, id)
    }

    // A pattern's own type held against what it is tested on.
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
            self.bind(p.name.clone(), ty, crate::tir::tir_nodes::TIRIntro::Let);
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
        let made = self.finish_body(value);
        let ty = self.types.intern(Ty::Fn { params: arg_tys, ret, is_unsafe: false });
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
            matches!(f.params.first().map(|p| &p.name), Some(TIRBinding::SelfRecv(_))),
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
                self.types.intern(Ty::Named { item, args })
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
