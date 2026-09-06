// Lowering: the AST to the TIR.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR -> sema
//
// The last pass that cares how the source was written, and the first that does
// not have to. What it settles is everything a single declaration answers on its
// own: the closed set of attributes, the grammar's scaffolding, the several
// spellings of one thing. What it leaves alone is everything that needs a second
// declaration in hand -- no name is resolved and no type is worked out here.
//
// It reads the arena the parser built and writes a `TIRProgram` of its own,
// touching neither. Reports go into a `Diagnostics` and the pass carries on, so
// one bad attribute does not cost the rest of the file.

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::parse::ast_nodes::{
    ASTAssignOp, ASTBinOp, ASTBinding, ASTFnUses, ASTImportLeaf, ASTLit, ASTNode, ASTNodeId,
    ASTNodeKind,
    ASTPrimType, ASTRangeOp, ASTRefOp, ASTSelf, ASTUnaryOp, ASTVariableIntro, ASTVisibility,
};
use crate::parse::parser::Parser;
use super::tir_nodes::*;

// The six the compiler knows. A name outside this set is an error where it was
// written -- see `docs/prose.txt` section 1, which is where the set is closed.
const ATTRS: &[&str] = &["symbol", "must_use", "inline", "noinline", "deprecated", "test"];

// What a `gc` binding was found to hold. Three answers and not two because
// this pass has no types: only what the syntax settles on its own is decided
// here, and `Unknown` is everything whose type `sema` is the first to know.
enum Holds {
    // A heap value or a pointer: what a `gc` binding is for.
    Held,
    // Plainly neither, and what it plainly is instead -- the words go under
    // the caret, so they read on from "this is".
    Not(&'static str),
    // Nothing the syntax settles.
    Unknown,
}

// What an attribute is being put on, for the one check that needs to know.
// `%deprecated` goes on anything; the other five are a function's.
#[derive(Clone, Copy, PartialEq)]
enum Target {
    Fn,
    Other(&'static str),
}

pub struct Lowerer<'a> {
    parser: &'a Parser,
    tir:    TIRProgram,
    errors: Diagnostics,
    // Whether what is being lowered stands inside an `unsafe` statement. A
    // count and not a flag: `unsafe { unsafe f() }` nests, and the inner word
    // must not put the outer one out when it is done with.
    guarded: usize,
}

impl<'a> Lowerer<'a> {
    pub fn new(parser: &'a Parser) -> Lowerer<'a> {
        Lowerer { parser, tir: TIRProgram::default(), errors: Diagnostics::new(), guarded: 0 }
    }

    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    pub fn finish(self) -> TIRProgram {
        self.tir
    }

    // ---- Reading the AST -------------------------------------------------

    fn kind(&self, id: ASTNodeId) -> ASTNodeKind {
        self.parser.get_node(id).kind.clone()
    }

    fn at(&self, id: ASTNodeId) -> (usize, usize) {
        let node = self.parser.get_node(id);
        (node.line, node.col)
    }

    // A caret and no more: an AST node keeps where it began and not how wide it
    // was written, so there is no length here to underline with.
    fn span(&self, id: ASTNodeId) -> Span {
        let (line, col) = self.at(id);
        Span::at(line, col)
    }

    // ---- Writing the TIR -------------------------------------------------

    fn push_item(&mut self, kind: TIRItemKind, at: ASTNodeId) -> TIRItemId {
        let (line, col) = self.at(at);
        self.tir.items.push(TIRItem { kind, line, col });
        self.tir.items.len() - 1
    }

    fn push_expr(&mut self, kind: TIRExprKind, at: ASTNodeId) -> TIRExprId {
        let (line, col) = self.at(at);
        self.tir.exprs.push(TIRExpr { kind, line, col });
        self.tir.exprs.len() - 1
    }

    fn push_type(&mut self, kind: TIRTypeKind, at: ASTNodeId) -> TIRTypeId {
        let (line, col) = self.at(at);
        self.tir.types.push(TIRType { kind, line, col });
        self.tir.types.len() - 1
    }

    fn push_pat(&mut self, kind: TIRPatKind, at: ASTNodeId) -> TIRPatId {
        let (line, col) = self.at(at);
        self.tir.pats.push(TIRPat { kind, line, col });
        self.tir.pats.len() - 1
    }

    // ---- The file --------------------------------------------------------

    pub fn lower(&mut self, root: &ASTNode) {
        let items = match &root.kind {
            ASTNodeKind::Program(items) => items.clone(),
            other => panic!("a file lowered from {:?}", other),
        };
        for id in items {
            if let Some(item) = self.item(id) {
                self.tir.roots.push(item);
            }
        }
    }

    // ---- Attributes ------------------------------------------------------

    // The list folded into fields. Every attribute is a function's but one, so
    // this always builds the wider struct and a lesser declaration takes the
    // `common` out of it.
    fn attrs(&mut self, ids: &[ASTNodeId], target: Target) -> TIRFnAttrs {
        let mut out = TIRFnAttrs::default();
        // Where each was written, so a second one can point at the first.
        let mut seen: Vec<(String, ASTNodeId)> = Vec::new();

        for &id in ids {
            let ASTNodeKind::Attr { name, args } = self.kind(id) else { continue };

            if !ATTRS.contains(&name.as_str()) {
                let mut d = Diagnostic::error(format!("unknown attribute `%{}`", name),
                                              self.span(id))
                    .with_label("no such attribute");
                if let Some(near) = nearest(&name) {
                    d = d.with_help(format!("did you mean `%{}`?", near));
                } else {
                    d = d.with_help(format!("the attributes are {}", list(ATTRS)));
                }
                self.errors.push(d);
                continue;
            }

            if let Some((_, first)) = seen.iter().find(|(n, _)| *n == name) {
                self.errors.push(
                    Diagnostic::error(format!("`%{}` is written twice", name), self.span(id))
                        .with_label("written again")
                        .with_secondary(self.span(*first), "the first one is"),
                );
                continue;
            }
            seen.push((name.clone(), id));

            // `%deprecated` is the one that goes on any declaration; the rest
            // say something only a function can be.
            if name != "deprecated" {
                if let Target::Other(what) = target {
                    self.errors.push(
                        Diagnostic::error(format!("`%{}` goes on a function", name),
                                          self.span(id))
                            .with_label(format!("this is {}", what))
                            .with_note("`%deprecated` is the one that goes on anything"),
                    );
                    continue;
                }
            }

            match name.as_str() {
                "symbol" => {
                    if let Some(text) = self.one_string(&args, id, "symbol") {
                        out.symbol = Some(text);
                    }
                }
                "deprecated" => {
                    if let Some(text) = self.one_string(&args, id, "deprecated") {
                        out.common.deprecated = Some(text);
                    }
                }
                "must_use" | "inline" | "noinline" | "test" => {
                    if !args.is_empty() {
                        self.errors.push(
                            Diagnostic::error(format!("`%{}` takes no arguments", name),
                                              self.span(id))
                                .with_label("nothing goes in here"),
                        );
                        continue;
                    }
                    match name.as_str() {
                        "must_use" => out.must_use = true,
                        "test" => out.is_test = true,
                        "inline" => out.inline = TIRInline::Always,
                        _ => out.inline = TIRInline::Never,
                    }
                }
                _ => {}
            }
        }

        // The one pair that contradicts. They are one field with three answers,
        // so writing both is a question with two answers rather than a state to
        // carry -- see `TIRInline`.
        let inline = seen.iter().find(|(n, _)| n == "inline");
        let noinline = seen.iter().find(|(n, _)| n == "noinline");
        if let (Some((_, first)), Some((_, second))) = (inline, noinline) {
            self.errors.push(
                Diagnostic::error("`%inline` and `%noinline` contradict".to_string(),
                                  self.span(*second))
                    .with_label("the other was already written")
                    .with_secondary(self.span(*first), "the first one is"),
            );
        }
        out
    }

    // The one STRING_LITERAL `%symbol` and `%deprecated` each take.
    fn one_string(&mut self, args: &[ASTNodeId], at: ASTNodeId, name: &str) -> Option<String> {
        if args.len() != 1 {
            self.errors.push(
                Diagnostic::error(format!("`%{}` takes one string", name), self.span(at))
                    .with_label(format!("{} given", count(args.len(), "argument"))),
            );
            return None;
        }
        match self.kind(args[0]) {
            ASTNodeKind::Literal(ASTLit::Str(text)) => Some(text),
            other => {
                self.errors.push(
                    Diagnostic::error(format!("`%{}` takes a string", name), self.span(args[0]))
                        .with_label("not a string")
                        .with_note(format!("this is {}", describe_arg(&other))),
                );
                None
            }
        }
    }

    // ---- Items -----------------------------------------------------------

    fn item(&mut self, id: ASTNodeId) -> Option<TIRItemId> {
        let kind = self.kind(id);
        let built = match kind {
            ASTNodeKind::Import { attrs, vis, leaves } => TIRItemKind::Import {
                vis:    visibility(vis),
                attrs:  self.attrs(&attrs, Target::Other("an import")).common,
                leaves: leaves.iter().map(import_leaf).collect(),
            },

            ASTNodeKind::Fn { .. } => {
                let f = self.function(id);
                TIRItemKind::Fn(f)
            }

            ASTNodeKind::Struct { attrs, vis, name, generics, fields } => {
                let attrs = self.attrs(&attrs, Target::Other("a struct")).common;
                TIRItemKind::Struct {
                    vis: visibility(vis),
                    attrs,
                    name,
                    generics: self.generics(&generics),
                    fields: self.fields(&fields),
                }
            }

            ASTNodeKind::Enum { attrs, vis, name, generics, variants } => {
                let attrs = self.attrs(&attrs, Target::Other("an enum")).common;
                let variants = variants.iter().map(|&v| self.variant(v)).collect();
                TIRItemKind::Enum {
                    vis: visibility(vis),
                    attrs,
                    name,
                    generics: self.generics(&generics),
                    variants,
                }
            }

            ASTNodeKind::Trait { attrs, vis, name, generics, members } => {
                let attrs = self.attrs(&attrs, Target::Other("a trait")).common;
                let members = members.iter().filter_map(|&m| self.item(m)).collect();
                TIRItemKind::Trait {
                    vis: visibility(vis),
                    attrs,
                    name,
                    generics: self.generics(&generics),
                    members,
                }
            }

            ASTNodeKind::Impl { attrs, vis, generics, ty, for_ty, wheres, members } => {
                let attrs = self.attrs(&attrs, Target::Other("an impl")).common;
                let ty = self.ty(ty);
                let for_ty = for_ty.map(|f| self.ty(f));
                let members = members.iter().filter_map(|&m| self.item(m)).collect();
                TIRItemKind::Impl {
                    vis: visibility(vis),
                    attrs,
                    generics: self.generics(&generics),
                    ty,
                    for_ty,
                    wheres: self.wheres(&wheres),
                    members,
                }
            }

            ASTNodeKind::Namespace { attrs, vis, name, items } => {
                let attrs = self.attrs(&attrs, Target::Other("a namespace")).common;
                let items = items.iter().filter_map(|&i| self.item(i)).collect();
                TIRItemKind::Namespace { vis: visibility(vis), attrs, name, items }
            }

            ASTNodeKind::TypeAlias { attrs, vis, name, generics, ty } => {
                let attrs = self.attrs(&attrs, Target::Other("a type alias")).common;
                let generics = self.generics(&generics);
                let ty = self.ty(ty);
                TIRItemKind::TypeAlias { vis: visibility(vis), attrs, name, generics, ty }
            }

            ASTNodeKind::Const { attrs, vis, name, ty, value } => {
                let attrs = self.attrs(&attrs, Target::Other("a constant")).common;
                let ty = self.ty(ty);
                let value = self.expr(value);
                TIRItemKind::Const { vis: visibility(vis), attrs, name, ty, value }
            }

            // A `<var_decl>` here is at file or namespace scope, which is what
            // makes it a global; the same node inside a block is a `Let`.
            ASTNodeKind::Variable { attrs, vis, intro, gc, name, ty, init } => {
                let attrs = self.attrs(&attrs, Target::Other("a variable")).common;
                if gc {
                    self.gc_check(ty, init);
                }
                let ty = ty.map(|t| self.ty(t));
                let init = init.map(|i| self.expr(i));
                TIRItemKind::Global {
                    vis: visibility(vis),
                    attrs,
                    intro: intro_of(intro),
                    is_gc: gc,
                    name: binding(&name),
                    ty,
                    init,
                }
            }

            ASTNodeKind::MacroDecl { .. } | ASTNodeKind::MacroCall { .. } => {
                panic!("a macro reached lowering; `expand` is meant to spend them all")
            }

            other => panic!("an item lowered from {:?}", other),
        };
        Some(self.push_item(built, id))
    }

    fn function(&mut self, id: ASTNodeId) -> TIRFn {
        let ASTNodeKind::Fn {
            attrs, vis, is_const, is_unsafe, name, generics, params, ret, wheres, body,
        } = self.kind(id) else {
            panic!("a function lowered from something else")
        };
        let attrs = self.attrs(&attrs, Target::Fn);
        let generics = self.generics(&generics);
        let params = params.iter().map(|&p| self.param(p)).collect();
        let ret = ret.map(|r| self.ty(r));
        let wheres = self.wheres(&wheres);
        let body = body.map(|b| self.expr(b));
        TIRFn {
            vis: visibility(vis),
            attrs,
            is_const,
            is_unsafe,
            name,
            generics,
            params,
            ret,
            wheres,
            body,
        }
    }

    fn param(&mut self, id: ASTNodeId) -> TIRParam {
        match self.kind(id) {
            ASTNodeKind::Param { name, ty } => {
                TIRParam { name: binding(&name), ty: ty.map(|t| self.ty(t)) }
            }
            other => panic!("a parameter lowered from {:?}", other),
        }
    }

    fn fields(&mut self, ids: &[ASTNodeId]) -> Vec<TIRFieldDecl> {
        ids.iter()
            .map(|&id| match self.kind(id) {
                ASTNodeKind::FieldDecl { attrs, vis, name, ty } => {
                    let attrs = self.attrs(&attrs, Target::Other("a field")).common;
                    let ty = self.ty(ty);
                    TIRFieldDecl { vis: visibility(vis), attrs, name, ty }
                }
                other => panic!("a field lowered from {:?}", other),
            })
            .collect()
    }

    // The three payload nodes become one enum, which is what leaves no fourth
    // state for a later pass to wonder about.
    fn variant(&mut self, id: ASTNodeId) -> TIRVariant {
        let ASTNodeKind::EnumVariant { attrs, name, body } = self.kind(id) else {
            panic!("a variant lowered from something else")
        };
        let attrs = self.attrs(&attrs, Target::Other("an enum variant")).common;
        let payload = match body {
            None => TIRPayload::None,
            Some(b) => match self.kind(b) {
                ASTNodeKind::TuplePayload(types) => {
                    TIRPayload::Tuple(types.iter().map(|&t| self.ty(t)).collect())
                }
                ASTNodeKind::NamedPayload(fields) => TIRPayload::Named(self.fields(&fields)),
                ASTNodeKind::Discriminant(value) => TIRPayload::Discriminant(self.expr(value)),
                other => panic!("a variant payload lowered from {:?}", other),
            },
        };
        TIRVariant { attrs, name, payload }
    }

    // ---- Generics --------------------------------------------------------

    fn generics(&mut self, ids: &[ASTNodeId]) -> Vec<TIRGeneric> {
        ids.iter()
            .map(|&id| match self.kind(id) {
                ASTNodeKind::GenericParam { name, bounds } => {
                    TIRGeneric::Type { name, bounds: self.bounds(&bounds) }
                }
                ASTNodeKind::LifetimeParam { name, bounds } => {
                    TIRGeneric::Life { name, bounds: self.bounds(&bounds) }
                }
                other => panic!("a generic parameter lowered from {:?}", other),
            })
            .collect()
    }

    fn bounds(&mut self, ids: &[ASTNodeId]) -> Vec<TIRBound> {
        ids.iter().map(|&id| self.bound(id)).collect()
    }

    fn bound(&mut self, id: ASTNodeId) -> TIRBound {
        match self.kind(id) {
            ASTNodeKind::Lifetime(name) => TIRBound::Life(name),
            _ => TIRBound::Trait(self.ty(id)),
        }
    }

    fn wheres(&mut self, ids: &[ASTNodeId]) -> Vec<TIRWherePred> {
        ids.iter()
            .map(|&id| match self.kind(id) {
                ASTNodeKind::WherePred { ty, bounds } => TIRWherePred {
                    subject: self.bound(ty),
                    bounds: self.bounds(&bounds),
                },
                other => panic!("a where predicate lowered from {:?}", other),
            })
            .collect()
    }

    // ---- Types -----------------------------------------------------------

    fn ty(&mut self, id: ASTNodeId) -> TIRTypeId {
        let kind = match self.kind(id) {
            ASTNodeKind::Prim(p) => TIRTypeKind::Prim(prim(p)),
            ASTNodeKind::Named { path, args } => {
                let args = args.iter().map(|&a| self.generic_arg(a)).collect();
                TIRTypeKind::Named { path, args }
            }
            ASTNodeKind::RefType { op, life, inner } => {
                let life = life.map(|l| match self.kind(l) {
                    ASTNodeKind::Lifetime(name) => name,
                    other => panic!("a lifetime lowered from {:?}", other),
                });
                TIRTypeKind::Ref { op: ref_op(op), life, inner: self.ty(inner) }
            }
            ASTNodeKind::PtrType(inner) => TIRTypeKind::Ptr(self.ty(inner)),
            ASTNodeKind::DynType(inner) => TIRTypeKind::Dyn(self.ty(inner)),
            ASTNodeKind::GcType(inner) => TIRTypeKind::Gc(self.ty(inner)),
            ASTNodeKind::Array { elem, len } => {
                TIRTypeKind::Array { elem: self.ty(elem), len: self.expr(len) }
            }
            ASTNodeKind::Run(inner) => TIRTypeKind::Run(self.ty(inner)),
            ASTNodeKind::TupleType(members) => {
                TIRTypeKind::Tuple(members.iter().map(|&m| self.ty(m)).collect())
            }
            ASTNodeKind::FnType { uses, params, ret } => TIRTypeKind::Fn {
                uses:   match uses {
                    ASTFnUses::Reads => TIRFnUses::Reads,
                    ASTFnUses::Writes => TIRFnUses::Writes,
                    ASTFnUses::Takes => TIRFnUses::Takes,
                },
                params: params.iter().map(|&p| self.ty(p)).collect(),
                ret:    ret.map(|r| self.ty(r)),
            },
            ASTNodeKind::Infer => TIRTypeKind::Infer,

            // A name substituted into a type position by a macro arrives shaped
            // as the expression it was written as -- `Vec<$t>` with `$t:ident`
            // is the case. The parser would have built a `Named` here, and this
            // is the one place the expanded tree differs from a parsed one.
            ASTNodeKind::Ident(name) => TIRTypeKind::Named { path: vec![name], args: Vec::new() },
            ASTNodeKind::Name(path) => TIRTypeKind::Named { path, args: Vec::new() },

            other => panic!("a type lowered from {:?}", other),
        };
        self.push_type(kind, id)
    }

    fn generic_arg(&mut self, id: ASTNodeId) -> TIRGenericArg {
        match self.kind(id) {
            ASTNodeKind::Lifetime(name) => TIRGenericArg::Life(name),
            _ => TIRGenericArg::Type(self.ty(id)),
        }
    }

    // ---- Patterns --------------------------------------------------------

    fn pat(&mut self, id: ASTNodeId) -> TIRPatId {
        let kind = match self.kind(id) {
            ASTNodeKind::Wildcard => TIRPatKind::Wildcard,
            // Still a name: whether it tests against a constant or binds is what
            // is in scope, and that is the resolver's to say.
            ASTNodeKind::Name(path) => TIRPatKind::Name(path),
            ASTNodeKind::Ident(name) => TIRPatKind::Name(vec![name]),
            ASTNodeKind::LitPat { negated, value } => {
                let suffix = suffix_of(&value);
                TIRPatKind::Lit { negated, value: lit(value), suffix }
            }
            ASTNodeKind::RangePat { op, lo, hi } => {
                TIRPatKind::Range { op: range_op(op), lo: self.pat(lo), hi: self.pat(hi) }
            }
            ASTNodeKind::VariantPat { path, elems } => TIRPatKind::Variant {
                path,
                elems: elems.iter().map(|&e| self.pat(e)).collect(),
            },
            ASTNodeKind::TuplePat(elems) => {
                TIRPatKind::Tuple(elems.iter().map(|&e| self.pat(e)).collect())
            }
            ASTNodeKind::StructPat { path, fields } => {
                let fields = fields
                    .iter()
                    .map(|&f| match self.kind(f) {
                        ASTNodeKind::FieldPat { name, pat } => {
                            TIRFieldPat { name, pat: pat.map(|p| self.pat(p)) }
                        }
                        other => panic!("a field pattern lowered from {:?}", other),
                    })
                    .collect();
                TIRPatKind::Struct { path, fields }
            }
            other => panic!("a pattern lowered from {:?}", other),
        };
        self.push_pat(kind, id)
    }

    // ---- gc ---------------------------------------------------------------

    // Holds a `gc` binding against the one rule there is about it: what stands
    // under one has to be something a collector can hold, which is a value on
    // the heap or a pointer to one. A number is not collected, and saying `gc`
    // over one is a mistake about what the word does rather than a shorthand
    // for anything.
    //
    // The type decides where one is written, and the value where none is: a
    // `let gc x: ptr u8 = f()` says pointer whatever `f` turns out to return,
    // and turning the initialiser down as well would be reporting one mistake
    // twice. Neither written leaves nothing to hold it against, which is
    // `sema`'s to settle along with what the binding's type even is.
    fn gc_check(&mut self, ty: Option<ASTNodeId>, init: Option<ASTNodeId>) {
        let (at, holds) = match (ty, init) {
            (Some(t), _) => (t, self.holds_ty(t)),
            (None, Some(i)) => (i, self.holds_expr(i)),
            (None, None) => return,
        };
        let Holds::Not(what) = holds else { return };
        self.errors.push(
            Diagnostic::error("`gc` needs a heap value or a pointer".to_string(),
                              self.span(at))
                .with_label(format!("this is {}", what))
                .with_help(
                    "a struct, an enum, a map, a set or a `ptr` is what a `gc` binding \
                     holds -- a number is a value the frame can keep",
                ),
        );
    }

    // What a written type says a `gc` binding would hold. A `<named_type>` is
    // the interesting one and the one nothing can be said about here: `Map<..>`
    // and the growable containers a library writes are both named types, and
    // which of them a name reaches is the resolver's to say (section 8).
    fn holds_ty(&self, id: ASTNodeId) -> Holds {
        match self.kind(id) {
            ASTNodeKind::PtrType(_) => Holds::Held,
            // `_` was written to be worked out; so is this.
            ASTNodeKind::Named { .. } | ASTNodeKind::Infer => Holds::Unknown,
            ASTNodeKind::Prim(_) => Holds::Not("a primitive"),
            // A reference is not a pointer: it is good for a while and says so,
            // and what it borrows is owned somewhere else already.
            ASTNodeKind::RefType { .. } => Holds::Not("a reference"),
            ASTNodeKind::Array { .. } => Holds::Not("an array, which is owned where it stands"),
            ASTNodeKind::Run(_) => Holds::Not("a run, which only a reference holds"),
            ASTNodeKind::TupleType(_) => Holds::Not("a tuple"),
            ASTNodeKind::FnType { .. } => Holds::Not("a closure"),
            _ => Holds::Unknown,
        }
    }

    // The same question of a value. A literal answers it outright, and so does
    // an `addr`, which is the only thing that makes a pointer. Everything that
    // has to be resolved or typed first -- a call, a name, a struct literal, a
    // block -- is left alone: a struct holding what it allocated is exactly the
    // shape a container has here, so a struct literal is where a heap value is
    // most likely to be rather than least.
    fn holds_expr(&self, id: ASTNodeId) -> Holds {
        match self.kind(id) {
            ASTNodeKind::Map { .. } | ASTNodeKind::Set { .. } => Holds::Held,
            ASTNodeKind::Unary { op: ASTUnaryOp::Addr, .. } => Holds::Held,
            // `q as ptr u64` makes a pointer of one; a cast to anything else
            // is worth exactly what that type is worth.
            ASTNodeKind::Cast { ty, .. } => self.holds_ty(ty),

            ASTNodeKind::Literal(value) => Holds::Not(match value {
                ASTLit::Int(..) | ASTLit::Float(..) => "a number",
                ASTLit::Str(_) => "a string literal",
                ASTLit::Char(_) => "a character",
                ASTLit::Bool(_) => "a boolean",
                ASTLit::Null => "`null`",
            }),
            ASTNodeKind::ArrayLit(_) => Holds::Not("an array, which is owned where it stands"),
            ASTNodeKind::TupleLit(_) => Holds::Not("a tuple"),
            ASTNodeKind::Closure { .. } => Holds::Not("a closure"),
            ASTNodeKind::Range { .. } => Holds::Not("a range"),
            ASTNodeKind::Unary { op: ASTUnaryOp::Ref(_), .. } => Holds::Not("a reference"),
            ASTNodeKind::Unary { op: ASTUnaryOp::Neg, .. } => Holds::Not("a number"),
            ASTNodeKind::Unary { op: ASTUnaryOp::Not, .. } => Holds::Not("a boolean"),
            ASTNodeKind::Binary { op, .. } => Holds::Not(match op {
                ASTBinOp::Eq | ASTBinOp::Ne | ASTBinOp::Lt | ASTBinOp::Gt
                | ASTBinOp::Le | ASTBinOp::Ge | ASTBinOp::And | ASTBinOp::Or
                | ASTBinOp::Xor => "a boolean",
                _ => "a number",
            }),

            _ => Holds::Unknown,
        }
    }

    // ---- Statements ------------------------------------------------------

    // `None` where the node was a macro declaration the expander should already
    // have dropped; everything else is one of the three shapes a statement has.
    fn stmt(&mut self, id: ASTNodeId, is_unsafe: bool) -> Option<TIRStmt> {
        match self.kind(id) {
            // The word becomes a flag: there are exactly two statements it can
            // stand in front of, and a node wrapped round one said no more.
            // What it guards is lowered with the count up, so an `addr`
            // anywhere under it is answered for.
            ASTNodeKind::Unsafe(inner) => {
                self.guarded += 1;
                let out = self.stmt(inner, true);
                self.guarded -= 1;
                out
            }
            ASTNodeKind::ExprStmt(e) => {
                Some(TIRStmt::Expr { is_unsafe, expr: self.expr(e) })
            }
            ASTNodeKind::Variable { attrs, intro, gc, name, ty, init, .. } => {
                // A `let` in a block takes no visibility, and the grammar gives
                // it none; attributes are still checked where they were written.
                self.attrs(&attrs, Target::Other("a variable"));
                if gc {
                    self.gc_check(ty, init);
                }
                let ty = ty.map(|t| self.ty(t));
                let init = init.map(|i| self.expr(i));
                Some(TIRStmt::Let {
                    is_unsafe,
                    is_gc: gc,
                    intro: intro_of(intro),
                    name: binding(&name),
                    ty,
                    init,
                })
            }
            // A declaration written inside an unsafe statement is still a
            // declaration, and section 2 says the word tells a body nothing --
            // so the count starts over at one, exactly as it does for the
            // body of an `unsafe fn`.
            _ => {
                let outer = std::mem::replace(&mut self.guarded, 0);
                let out = self.item(id).map(TIRStmt::Item);
                self.guarded = outer;
                out
            }
        }
    }

    // ---- Expressions -----------------------------------------------------

    fn expr(&mut self, id: ASTNodeId) -> TIRExprId {
        let kind = match self.kind(id) {
            ASTNodeKind::Literal(value) => {
                let suffix = suffix_of(&value);
                TIRExprKind::Literal { value: lit(value), suffix }
            }
            ASTNodeKind::Ident(name) => TIRExprKind::Name(vec![name]),
            ASTNodeKind::Name(path) => TIRExprKind::Name(path),
            ASTNodeKind::SelfExpr => TIRExprKind::SelfExpr,

            // `.` reaches a value and `::` what the compiler knows the name of.
            // They look alike once resolved, and are kept apart here because
            // which was written is what the resolver is about to read.
            ASTNodeKind::Field { base, name } => {
                TIRExprKind::Field { base: self.expr(base), name }
            }
            ASTNodeKind::Path { base, name } => {
                TIRExprKind::Path { base: self.expr(base), name }
            }
            ASTNodeKind::TupleIndex { base, index } => {
                TIRExprKind::TupleIndex { base: self.expr(base), index }
            }
            ASTNodeKind::TypeArgs { base, args } => {
                let base = self.expr(base);
                let args = args.iter().map(|&a| self.generic_arg(a)).collect();
                TIRExprKind::TypeArgs { base, args }
            }

            ASTNodeKind::Call { callee, args } => TIRExprKind::Call {
                callee: self.expr(callee),
                args: args.iter().map(|&a| self.expr(a)).collect(),
            },
            ASTNodeKind::Index { base, index } => {
                TIRExprKind::Index { base: self.expr(base), index: self.expr(index) }
            }
            ASTNodeKind::StructLit { base, fields } => {
                let base = self.expr(base);
                let fields = fields
                    .iter()
                    .map(|&f| match self.kind(f) {
                        ASTNodeKind::FieldInit { name, value } => {
                            TIRFieldInit { name, value: self.expr(value) }
                        }
                        other => panic!("a field initialiser lowered from {:?}", other),
                    })
                    .collect();
                TIRExprKind::StructLit { base, fields }
            }

            ASTNodeKind::ArrayLit(elems) => {
                TIRExprKind::ArrayLit(elems.iter().map(|&e| self.expr(e)).collect())
            }
            ASTNodeKind::TupleLit(elems) => {
                TIRExprKind::TupleLit(elems.iter().map(|&e| self.expr(e)).collect())
            }
            ASTNodeKind::Map { hashed, entries } => {
                let entries = entries
                    .iter()
                    .map(|&e| match self.kind(e) {
                        ASTNodeKind::MapEntry { key, value } => {
                            TIRMapEntry { key: self.expr(key), value: self.expr(value) }
                        }
                        other => panic!("a map entry lowered from {:?}", other),
                    })
                    .collect();
                TIRExprKind::Map { hashed, entries }
            }
            ASTNodeKind::Set { hashed, elems } => TIRExprKind::Set {
                hashed,
                elems: elems.iter().map(|&e| self.expr(e)).collect(),
            },

            ASTNodeKind::Unary { op, operand } => {
                // The two that reach outside what the checker answers for.
                // `addr` makes an address the checker stopped following, and
                // `deref` reads one back -- and of the two this is the one
                // that can fault, so if either wants a guard both do.
                if matches!(op, ASTUnaryOp::Addr | ASTUnaryOp::Deref) && self.guarded == 0 {
                    let (what, said) = match op {
                        ASTUnaryOp::Addr => ("`addr` needs an `unsafe`", "this makes a pointer"),
                        _ => ("`deref` needs an `unsafe`", "this reads through a pointer"),
                    };
                    self.errors.push(
                        Diagnostic::error(what.to_string(), self.span(id))
                            .with_label(said)
                            .with_note("write `unsafe` in front of the statement it is in"),
                    );
                }
                TIRExprKind::Unary { op: unary_op(op), operand: self.expr(operand) }
            }
            ASTNodeKind::Binary { op, lhs, rhs } => {
                TIRExprKind::Binary { op: bin_op(op), lhs: self.expr(lhs), rhs: self.expr(rhs) }
            }
            // The operator is kept rather than desugared: `a += b` written out
            // is the place twice, and saying it once needs a temporary, which
            // needs the types `sema` has not worked out yet.
            ASTNodeKind::Assign { op, target, value } => TIRExprKind::Assign {
                op: assign_op(op),
                place: self.expr(target),
                value: self.expr(value),
            },
            ASTNodeKind::Range { op, start, end } => TIRExprKind::Range {
                op: range_op(op),
                start: start.map(|s| self.expr(s)),
                end: end.map(|e| self.expr(e)),
            },
            ASTNodeKind::Cast { value, ty } => {
                TIRExprKind::Cast { value: self.expr(value), ty: self.ty(ty) }
            }
            ASTNodeKind::Closure { is_move, params, body } => TIRExprKind::Closure {
                is_move,
                params: params.iter().map(|&p| self.param(p)).collect(),
                body: self.expr(body),
            },

            ASTNodeKind::Block { .. } => return self.block(id),

            // The `elif`s the AST keeps as written are folded here, from the
            // last one backwards into the `else`, so every pass below reads one
            // shape instead of two.
            ASTNodeKind::If { cond, then, elifs, else_block } => {
                let cond = self.expr(cond);
                let then = self.expr(then);
                let mut els = else_block.map(|b| self.expr(b));
                for &elif in elifs.iter().rev() {
                    let ASTNodeKind::Elif { cond, block } = self.kind(elif) else {
                        panic!("an elif lowered from something else")
                    };
                    let cond = self.expr(cond);
                    let then = self.expr(block);
                    let nested = TIRExprKind::If { cond, then, els };
                    els = Some(self.push_expr(nested, elif));
                }
                TIRExprKind::If { cond, then, els }
            }
            ASTNodeKind::While { cond, body } => {
                TIRExprKind::While { cond: self.expr(cond), body: self.expr(body) }
            }
            ASTNodeKind::For { name, iter, body } => TIRExprKind::For {
                name: binding(&name),
                iter: self.expr(iter),
                body: self.expr(body),
            },
            ASTNodeKind::Match { scrutinee, arms } => {
                let scrutinee = self.expr(scrutinee);
                let arms = arms
                    .iter()
                    .map(|&a| match self.kind(a) {
                        ASTNodeKind::MatchArm { pats, body } => TIRArm {
                            pats: pats.iter().map(|&p| self.pat(p)).collect(),
                            body: self.expr(body),
                        },
                        other => panic!("a match arm lowered from {:?}", other),
                    })
                    .collect();
                TIRExprKind::Match { scrutinee, arms }
            }

            ASTNodeKind::Return(value) => TIRExprKind::Return(value.map(|v| self.expr(v))),
            ASTNodeKind::Break(value) => TIRExprKind::Break(value.map(|v| self.expr(v))),
            ASTNodeKind::Continue => TIRExprKind::Continue,

            ASTNodeKind::MacroCall { .. } | ASTNodeKind::MacroVar(_) => {
                panic!("a macro reached lowering; `expand` is meant to spend them all")
            }

            other => panic!("an expression lowered from {:?}", other),
        };
        self.push_expr(kind, id)
    }

    fn block(&mut self, id: ASTNodeId) -> TIRExprId {
        let ASTNodeKind::Block { stmts, tail } = self.kind(id) else {
            panic!("a block lowered from something else")
        };
        let mut out: Vec<TIRStmt> = Vec::new();
        for s in stmts {
            if let Some(stmt) = self.stmt(s, false) {
                out.push(stmt);
            }
        }
        // The slot the grammar leaves for a last thing with no separator holds
        // an expression *or* a declaration -- `<unterminated_stmt>` takes a
        // `<var_head>` too. Only an expression is the block's value; a
        // declaration there is a statement like any other, and the block yields
        // `null` as one with nothing at the end does.
        //
        // `unsafe` is the third thing it holds, and it guards the tail without
        // taking its value away: `fn read(p: ptr i64): i64 { unsafe p[0] }` is
        // what it looks like, and the grammar admits it here for exactly that
        // reason -- there is no `;` in front of a `}`, so the tail slot is the
        // only place an `unsafe` can be the last thing in a body at all.
        //
        // It used to make a statement of whatever it prefixed, and a block
        // ending in one was `null`. Nothing said so: `null` "belongs to every
        // type", so the signature above agreed with it and the fn returned
        // nought. A word that guards a read should not also throw the read
        // away.
        //
        // It is taken off here rather than in `stmt`, which is handed
        // statements and never the bare expression this slot has, and what is
        // left of it is the flag on the block -- the word guards a statement
        // (§8: there is no unsafe *expression*), and this is the one place a
        // thing is guarded and is a value at once.
        let mut is_unsafe = false;
        let mut tail = tail;
        while let Some(ASTNodeKind::Unsafe(inner)) = tail.map(|t| self.kind(t)) {
            is_unsafe = true;
            tail = Some(inner);
        }
        self.guarded += is_unsafe as usize;
        let tail = match tail {
            None => None,
            Some(t) if !self.is_value(t) => {
                if let Some(stmt) = self.stmt(t, is_unsafe) {
                    out.push(stmt);
                }
                None
            }
            Some(t) => Some(self.expr(t)),
        };
        self.guarded -= is_unsafe as usize;
        // The word is spent where it was written: a tail that turned out to be
        // a declaration went into `out` as a guarded statement above, and there
        // is no tail left for the flag to be about.
        let tail_unsafe = is_unsafe && tail.is_some();
        self.push_expr(TIRExprKind::Block { stmts: out, tail, tail_unsafe }, id)
    }

    // Whether the node in a block's tail slot is the value of the block or the
    // last statement in it.
    fn is_value(&self, id: ASTNodeId) -> bool {
        match self.kind(id) {
            ASTNodeKind::Variable { .. }
            | ASTNodeKind::Const { .. }
            | ASTNodeKind::TypeAlias { .. }
            | ASTNodeKind::Fn { .. } => false,
            _ => true,
        }
    }
}

// ---- The leaves -----------------------------------------------------------
// Spelled again rather than borrowed: a `+` means the same in both trees, and
// nothing below this module should have to reach into the syntax to name one.

fn visibility(v: ASTVisibility) -> TIRVis {
    match v {
        ASTVisibility::Unwritten => TIRVis::Unwritten,
        ASTVisibility::Pub => TIRVis::Pub,
        ASTVisibility::Priv => TIRVis::Priv,
        ASTVisibility::Suite => TIRVis::Suite,
    }
}

fn import_leaf(l: &ASTImportLeaf) -> TIRImportLeaf {
    TIRImportLeaf {
        path:  l.path.clone(),
        alias: l.alias.clone(),
        glob:  l.glob,
        line:  l.line,
        col:   l.col,
    }
}

fn self_of(s: ASTSelf) -> TIRSelf {
    match s {
        ASTSelf::Value => TIRSelf::Value,
        ASTSelf::Ref => TIRSelf::Ref,
        ASTSelf::Mut => TIRSelf::Mut,
    }
}

fn intro_of(i: ASTVariableIntro) -> TIRIntro {
    match i {
        ASTVariableIntro::Let => TIRIntro::Let,
        ASTVariableIntro::Var => TIRIntro::Var,
    }
}

fn binding(b: &ASTBinding) -> TIRBinding {
    match b {
        ASTBinding::Name(name) => TIRBinding::Name(name.clone()),
        ASTBinding::Discard => TIRBinding::Discard,
        ASTBinding::SelfRecv(held, life) => {
            TIRBinding::SelfRecv(self_of(*held), life.clone())
        }
    }
}

// The type a number's suffix named, which only a number can have carried.
fn suffix_of(l: &ASTLit) -> Option<TIRPrim> {
    match l {
        ASTLit::Int(_, s) | ASTLit::Float(_, s) => s.map(prim),
        _ => None,
    }
}

fn lit(l: ASTLit) -> TIRLit {
    match l {
        ASTLit::Int(n, _) => TIRLit::Int(n),
        ASTLit::Float(f, _) => TIRLit::Float(f),
        ASTLit::Str(s) => TIRLit::Str(s),
        ASTLit::Char(c) => TIRLit::Char(c),
        ASTLit::Bool(b) => TIRLit::Bool(b),
        ASTLit::Null => TIRLit::Null,
    }
}

fn ref_op(op: ASTRefOp) -> TIRRefOp {
    match op {
        ASTRefOp::Imm => TIRRefOp::Imm,
        ASTRefOp::Mut => TIRRefOp::Mut,
    }
}

fn unary_op(op: ASTUnaryOp) -> TIRUnaryOp {
    match op {
        ASTUnaryOp::Not => TIRUnaryOp::Not,
        ASTUnaryOp::Neg => TIRUnaryOp::Neg,
        ASTUnaryOp::Ref(r) => TIRUnaryOp::Ref(ref_op(r)),
        ASTUnaryOp::Addr => TIRUnaryOp::Addr,
        ASTUnaryOp::Deref => TIRUnaryOp::Deref,
    }
}

fn bin_op(op: ASTBinOp) -> TIRBinOp {
    match op {
        ASTBinOp::Add => TIRBinOp::Add,
        ASTBinOp::Sub => TIRBinOp::Sub,
        ASTBinOp::Mul => TIRBinOp::Mul,
        ASTBinOp::Div => TIRBinOp::Div,
        ASTBinOp::Rem => TIRBinOp::Rem,
        ASTBinOp::Shl => TIRBinOp::Shl,
        ASTBinOp::Shr => TIRBinOp::Shr,
        ASTBinOp::BitAnd => TIRBinOp::BitAnd,
        ASTBinOp::BitOr => TIRBinOp::BitOr,
        ASTBinOp::BitXor => TIRBinOp::BitXor,
        ASTBinOp::Eq => TIRBinOp::Eq,
        ASTBinOp::Ne => TIRBinOp::Ne,
        ASTBinOp::Lt => TIRBinOp::Lt,
        ASTBinOp::Gt => TIRBinOp::Gt,
        ASTBinOp::Le => TIRBinOp::Le,
        ASTBinOp::Ge => TIRBinOp::Ge,
        ASTBinOp::And => TIRBinOp::And,
        ASTBinOp::Or => TIRBinOp::Or,
        ASTBinOp::Xor => TIRBinOp::Xor,
    }
}

fn assign_op(op: ASTAssignOp) -> TIRAssignOp {
    match op {
        ASTAssignOp::Set => TIRAssignOp::Set,
        ASTAssignOp::Add => TIRAssignOp::Add,
        ASTAssignOp::Sub => TIRAssignOp::Sub,
        ASTAssignOp::Mul => TIRAssignOp::Mul,
        ASTAssignOp::Div => TIRAssignOp::Div,
        ASTAssignOp::And => TIRAssignOp::And,
        ASTAssignOp::Or => TIRAssignOp::Or,
        ASTAssignOp::Xor => TIRAssignOp::Xor,
        ASTAssignOp::Shl => TIRAssignOp::Shl,
        ASTAssignOp::Shr => TIRAssignOp::Shr,
    }
}

fn range_op(op: ASTRangeOp) -> TIRRangeOp {
    match op {
        ASTRangeOp::Exclusive => TIRRangeOp::Exclusive,
        ASTRangeOp::Inclusive => TIRRangeOp::Inclusive,
    }
}

fn prim(p: ASTPrimType) -> TIRPrim {
    match p {
        ASTPrimType::I8 => TIRPrim::I8,
        ASTPrimType::I16 => TIRPrim::I16,
        ASTPrimType::I32 => TIRPrim::I32,
        ASTPrimType::I64 => TIRPrim::I64,
        ASTPrimType::I128 => TIRPrim::I128,
        ASTPrimType::U8 => TIRPrim::U8,
        ASTPrimType::U16 => TIRPrim::U16,
        ASTPrimType::U32 => TIRPrim::U32,
        ASTPrimType::U64 => TIRPrim::U64,
        ASTPrimType::U128 => TIRPrim::U128,
        ASTPrimType::F32 => TIRPrim::F32,
        ASTPrimType::F64 => TIRPrim::F64,
        ASTPrimType::Bool => TIRPrim::Bool,
        ASTPrimType::Char => TIRPrim::Char,
        ASTPrimType::Str => TIRPrim::Str,
        ASTPrimType::Null => TIRPrim::Null,
        ASTPrimType::Never => TIRPrim::Never,
    }
}

// ---- Words for messages ---------------------------------------------------

fn count(n: usize, word: &str) -> String {
    if n == 1 { format!("1 {}", word) } else { format!("{} {}s", n, word) }
}

fn list(words: &[&str]) -> String {
    words.iter().map(|w| format!("`%{}`", w)).collect::<Vec<_>>().join(", ")
}

fn describe_arg(kind: &ASTNodeKind) -> &'static str {
    match kind {
        ASTNodeKind::Literal(ASTLit::Int(..)) => "an integer",
        ASTNodeKind::Literal(ASTLit::Float(..)) => "a float",
        ASTNodeKind::Literal(ASTLit::Char(_)) => "a character",
        ASTNodeKind::Literal(ASTLit::Bool(_)) => "a boolean",
        ASTNodeKind::Literal(ASTLit::Null) => "`null`",
        ASTNodeKind::Attr { .. } => "a name",
        _ => "not a literal",
    }
}

// The known attribute a misspelling is nearest to, where it is near enough to
// be worth naming. The set is closed, which is what makes the guess worth
// making at all -- see section 1 of docs/prose.txt.
fn nearest(name: &str) -> Option<&'static str> {
    let mut best: Option<(usize, &'static str)> = None;
    for &known in ATTRS {
        let d = distance(name, known);
        if d <= 2 && best.map_or(true, |(b, _)| d < b) {
            best = Some((d, known));
        }
    }
    best.map(|(_, known)| known)
}

// Levenshtein, small and plain: the words are short and there are six of them.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        cur[0] = i;
        for j in 1..=b.len() {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

#[cfg(test)]
mod tests;
