// Macro expansion: the pass that spends every `@name(..)` and leaves a tree
// with none in it.
//
// Where it sits:
//
//     prep -> lex -> parse -> AST -> expand -> lower -> GIR -> sema
//
// Before lowering, because the GIR has no macro of any kind -- see
// `gir/gir_nodes.rs`, whose item kinds stop at `Global`. After parsing, because
// what a macro expands to is written in the language and is parsed as the
// language: a body is a `<block>` the parser has already built, and expanding
// is copying it with the arguments put where the parameters stood.
//
// It runs on the AST and not the GIR for the same reason it must run before
// one: a macro is a thing of the syntax, and by the GIR there is nothing left
// of it to be.
//
// What it does not do is resolve anything. A macro is found by the name it was
// declared with, in a table of its own, and that table is the only lookup here;
// `sema` still sees every other name exactly as written.

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::parse::ast_nodes::{ASTNode, ASTNodeId, ASTNodeKind};
use crate::parse::parser::Parser;

// The fragments a parameter may ask for. Closed, as the attributes are: the
// compiler knows every one there is, and one it does not know is an error where
// it is written.
//
// Three and not Rust's dozen, because an argument is an `<expression>` and
// these are the three an expression can be. A `ty` is not here: `@m(i32)` does
// not parse at all -- a primitive is no `<primary>` -- so a fragment that could
// only ever be handed a name would be `ident` under another spelling.
const FRAGMENTS: &[&str] = &["expr", "ident", "lit"];

// How deep an expansion may nest before it is called a loop. A macro may invoke
// another, and may invoke itself; nothing here proves it stops, so a depth is
// what stands in for the proof.
const MAX_DEPTH: usize = 64;

// A macro as declared: what it takes, and the block it stands for.
struct MacroDef {
    params: Vec<(String, String)>,
    body:   ASTNodeId,
    line:   usize,
    col:    usize,
}

pub struct Expander<'a> {
    parser: &'a mut Parser,
    macros: HashMap<String, MacroDef>,
    errors: Diagnostics,
    depth:  usize,
}

// Every handle a node holds, lent for writing so one walk can both read the
// children and put new ones back. The order is the order they are written in,
// and both halves of a copy rely on it being the same order twice.
//
// This is `children_of` in `build/tests.rs` with the borrows the other way
// round. Two of them rather than one because the test wants to look and this
// wants to rewrite, and a shared shape would make one of the two clumsy.
fn children_mut(kind: &mut ASTNodeKind) -> Vec<&mut ASTNodeId> {
    let mut out: Vec<&mut ASTNodeId> = Vec::new();
    match kind {
        ASTNodeKind::Program(ids)
        | ASTNodeKind::List(ids)
        | ASTNodeKind::ArrayLit(ids)
        | ASTNodeKind::TupleLit(ids)
        | ASTNodeKind::TupleType(ids)
        | ASTNodeKind::TuplePat(ids)
        | ASTNodeKind::TuplePayload(ids)
        | ASTNodeKind::NamedPayload(ids) => out.extend(ids.iter_mut()),
        ASTNodeKind::FnType { params, ret, .. } => {
            out.extend(params.iter_mut());
            out.extend(ret.iter_mut());
        }
        ASTNodeKind::Fn { attrs, generics, params, ret, wheres, body, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.extend(params.iter_mut());
            out.extend(wheres.iter_mut());
            out.extend(ret.iter_mut());
            out.extend(body.iter_mut());
        }
        ASTNodeKind::Struct { attrs, generics, fields, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.extend(fields.iter_mut());
        }
        ASTNodeKind::Enum { attrs, generics, variants, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.extend(variants.iter_mut());
        }
        ASTNodeKind::Trait { attrs, generics, members, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.extend(members.iter_mut());
        }
        ASTNodeKind::Impl { attrs, generics, ty, for_ty, wheres, members, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.extend(wheres.iter_mut());
            out.extend(members.iter_mut());
            out.push(ty);
            out.extend(for_ty.iter_mut());
        }
        ASTNodeKind::Namespace { attrs, items, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(items.iter_mut());
        }
        ASTNodeKind::Variable { attrs, ty, init, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(ty.iter_mut());
            out.extend(init.iter_mut());
        }
        ASTNodeKind::Const { attrs, ty, value, .. } => {
            out.extend(attrs.iter_mut());
            out.push(ty);
            out.push(value);
        }
        ASTNodeKind::TypeAlias { attrs, generics, ty, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(generics.iter_mut());
            out.push(ty);
        }
        ASTNodeKind::Attr { args, .. } => out.extend(args.iter_mut()),
        ASTNodeKind::Param { ty, .. } => out.extend(ty.iter_mut()),
        ASTNodeKind::FieldDecl { attrs, ty, .. } => {
            out.extend(attrs.iter_mut());
            out.push(ty);
        }
        ASTNodeKind::EnumVariant { attrs, body, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(body.iter_mut());
        }
        ASTNodeKind::Discriminant(id)
        | ASTNodeKind::Run(id)
        | ASTNodeKind::PtrType(id)
        | ASTNodeKind::ExprStmt(id)
        | ASTNodeKind::Unsafe(id) => out.push(id),
        ASTNodeKind::MacroDecl { attrs, params, body, .. } => {
            out.extend(attrs.iter_mut());
            out.extend(params.iter_mut());
            out.push(body);
        }
        ASTNodeKind::MacroCall { args, .. } => out.extend(args.iter_mut()),
        ASTNodeKind::GenericParam { bounds, .. }
        | ASTNodeKind::LifetimeParam { bounds, .. } => out.extend(bounds.iter_mut()),
        ASTNodeKind::WherePred { ty, bounds } => {
            out.push(ty);
            out.extend(bounds.iter_mut());
        }
        ASTNodeKind::RefType { life, inner, .. } => {
            out.extend(life.iter_mut());
            out.push(inner);
        }
        ASTNodeKind::Array { elem, len } => {
            out.push(elem);
            out.push(len);
        }
        ASTNodeKind::Named { args, .. } => out.extend(args.iter_mut()),
        ASTNodeKind::Map { entries, .. } => out.extend(entries.iter_mut()),
        ASTNodeKind::Set { elems, .. } => out.extend(elems.iter_mut()),
        ASTNodeKind::MapEntry { key, value } => {
            out.push(key);
            out.push(value);
        }
        ASTNodeKind::Field { base, .. }
        | ASTNodeKind::TupleIndex { base, .. }
        | ASTNodeKind::Path { base, .. } => out.push(base),
        ASTNodeKind::TypeArgs { base, args } => {
            out.push(base);
            out.extend(args.iter_mut());
        }
        ASTNodeKind::Call { callee, args } => {
            out.push(callee);
            out.extend(args.iter_mut());
        }
        ASTNodeKind::Index { base, index } => {
            out.push(base);
            out.push(index);
        }
        ASTNodeKind::StructLit { base, fields } => {
            out.push(base);
            out.extend(fields.iter_mut());
        }
        ASTNodeKind::FieldInit { value, .. } => out.push(value),
        ASTNodeKind::Unary { operand, .. } => out.push(operand),
        ASTNodeKind::Binary { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        ASTNodeKind::Assign { target, value, .. } => {
            out.push(target);
            out.push(value);
        }
        ASTNodeKind::Range { start, end, .. } => {
            out.extend(start.iter_mut());
            out.extend(end.iter_mut());
        }
        ASTNodeKind::Cast { value, ty } => {
            out.push(value);
            out.push(ty);
        }
        ASTNodeKind::Closure { params, body, .. } => {
            out.extend(params.iter_mut());
            out.push(body);
        }
        ASTNodeKind::Block { stmts, tail } => {
            out.extend(stmts.iter_mut());
            out.extend(tail.iter_mut());
        }
        ASTNodeKind::If { cond, then, elifs, else_block } => {
            out.push(cond);
            out.push(then);
            out.extend(elifs.iter_mut());
            out.extend(else_block.iter_mut());
        }
        ASTNodeKind::Elif { cond, block } => {
            out.push(cond);
            out.push(block);
        }
        ASTNodeKind::While { cond, body } => {
            out.push(cond);
            out.push(body);
        }
        ASTNodeKind::For { iter, body, .. } => {
            out.push(iter);
            out.push(body);
        }
        ASTNodeKind::Match { scrutinee, arms } => {
            out.push(scrutinee);
            out.extend(arms.iter_mut());
        }
        ASTNodeKind::MatchArm { pats, body } => {
            out.extend(pats.iter_mut());
            out.push(body);
        }
        ASTNodeKind::Return(id) | ASTNodeKind::Break(id) => out.extend(id.iter_mut()),
        ASTNodeKind::RangePat { lo, hi, .. } => {
            out.push(lo);
            out.push(hi);
        }
        ASTNodeKind::VariantPat { elems, .. } => out.extend(elems.iter_mut()),
        ASTNodeKind::StructPat { fields, .. } => out.extend(fields.iter_mut()),
        ASTNodeKind::FieldPat { pat, .. } => out.extend(pat.iter_mut()),
        // An import holds no handle but the attributes written in front of it;
        // the tree it reached is spelling and stands in the node itself.
        ASTNodeKind::Import { attrs, .. } => out.extend(attrs.iter_mut()),
        // The leaves, and the scaffolding that names nothing.
        ASTNodeKind::Empty
        | ASTNodeKind::Mark(_)
        | ASTNodeKind::ImportTree(_)
        | ASTNodeKind::Prim(_)
        | ASTNodeKind::Infer
        | ASTNodeKind::Literal(_)
        | ASTNodeKind::Ident(_)
        | ASTNodeKind::Lifetime(_)
        | ASTNodeKind::MacroVar(_)
        | ASTNodeKind::MacroParam { .. }
        | ASTNodeKind::SelfExpr
        | ASTNodeKind::SelfRecv(..)
        | ASTNodeKind::Name(_)
        | ASTNodeKind::Continue
        | ASTNodeKind::Wildcard
        | ASTNodeKind::LitPat { .. } => {}
    }
    out
}

// Whether an argument is the kind of thing its parameter asked for. Only the
// three of `FRAGMENTS` are answerable, an argument being an expression: `ident`
// wants a bare name and `lit` a literal, and `expr` is every expression there
// is and so asks nothing.
fn fits_fragment(kind: &ASTNodeKind, fragment: &str) -> bool {
    match fragment {
        "expr" => true,
        "ident" => matches!(kind, ASTNodeKind::Ident(_))
            || matches!(kind, ASTNodeKind::Name(segments) if segments.len() == 1),
        "lit" => matches!(kind, ASTNodeKind::Literal(_)),
        // An unknown fragment was reported where it was declared; an argument
        // against one is not a second thing wrong.
        _ => true,
    }
}

fn describe(kind: &ASTNodeKind) -> &'static str {
    match kind {
        ASTNodeKind::Ident(_) | ASTNodeKind::Name(_) => "a name",
        ASTNodeKind::Literal(_) => "a literal",
        ASTNodeKind::Call { .. } => "a call",
        ASTNodeKind::Binary { .. } | ASTNodeKind::Unary { .. } => "an operation",
        ASTNodeKind::Block { .. } => "a block",
        _ => "an expression",
    }
}

impl<'a> Expander<'a> {
    pub fn new(parser: &'a mut Parser) -> Expander<'a> {
        Expander { parser, macros: HashMap::new(), errors: Diagnostics::new(), depth: 0 }
    }

    // Everything expansion turned down, in order. Spans and not text, as every
    // other phase reports: the caller holds the source and renders them.
    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    fn span_of(&self, id: ASTNodeId) -> Span {
        let node = self.parser.get_node(id);
        // A node keeps a line and a column and no width; a caret is what a
        // message about one can point with until the AST carries a length.
        Span::at(node.line, node.col)
    }

    fn kind(&self, id: ASTNodeId) -> ASTNodeKind {
        self.parser.get_node(id).kind.clone()
    }

    // The tree with every macro spent: the declarations gathered, the calls
    // replaced by what they stand for, and the declarations themselves dropped,
    // there being nothing downstream that could read one.
    pub fn expand(&mut self, root: &ASTNode) -> ASTNode {
        self.collect(root);
        let mut kind = root.kind.clone();
        self.strip_decls(&mut kind);
        self.copy_children(&mut kind, &HashMap::new());
        ASTNode::new(kind, root.line, root.col)
    }

    // Walks the items for declarations, into namespaces as well: a macro is an
    // item like any other and a namespace holds items.
    fn collect(&mut self, root: &ASTNode) {
        let mut stack: Vec<ASTNodeId> = match &root.kind {
            ASTNodeKind::Program(items) => items.clone(),
            _ => Vec::new(),
        };
        while let Some(id) = stack.pop() {
            match self.kind(id) {
                ASTNodeKind::Namespace { items, .. } => stack.extend(items),
                ASTNodeKind::MacroDecl { name, params, body, .. } => {
                    let node = self.parser.get_node(id);
                    let (line, col) = (node.line, node.col);
                    let params = self.read_params(&params);
                    if let Some(first) = self.macros.get(&name) {
                        let first = Span::at(first.line, first.col);
                        self.errors.push(
                            Diagnostic::error(format!("macro `{}` is declared twice", name),
                                              Span::at(line, col))
                                .with_label("declared again")
                                .with_secondary(first, "first declared"),
                        );
                        continue;
                    }
                    self.macros.insert(name, MacroDef { params, body, line, col });
                }
                _ => {}
            }
        }
    }

    // The `$name:fragment` pairs, with a fragment the compiler does not know
    // reported where it was written.
    fn read_params(&mut self, params: &[ASTNodeId]) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for &id in params {
            if let ASTNodeKind::MacroParam { name, fragment } = self.kind(id) {
                if !FRAGMENTS.contains(&fragment.as_str()) {
                    self.errors.push(
                        Diagnostic::error(format!("unknown fragment `{}`", fragment),
                                          self.span_of(id))
                            .with_label("no such fragment")
                            .with_help(format!("the fragments are {}", list(FRAGMENTS))),
                    );
                }
                out.push((name, fragment));
            }
        }
        out
    }

    // A declaration is dropped from the list that held it, there being nothing
    // below this pass that could read one -- the GIR has no macro item at all.
    // The three lists that can hold one are a file's, a namespace's and a
    // block's, a macro being a `<declaration>` and so a statement as well.
    fn strip_decls(&self, kind: &mut ASTNodeKind) {
        let held = |p: &Parser, i: ASTNodeId| {
            matches!(p.get_node(i).kind, ASTNodeKind::MacroDecl { .. })
        };
        match kind {
            ASTNodeKind::Program(items) | ASTNodeKind::Namespace { items, .. } => {
                items.retain(|&i| !held(self.parser, i))
            }
            ASTNodeKind::Block { stmts, .. } => stmts.retain(|&i| !held(self.parser, i)),
            _ => {}
        }
    }

    // Copies every child of `kind` into the arena, expanding as it goes, and
    // puts the new handles back where the old ones were. The two walks see the
    // same slots in the same order, which is what lets the second write what
    // the first read.
    fn copy_children(
        &mut self,
        kind: &mut ASTNodeKind,
        subst: &HashMap<String, ASTNodeId>,
    ) -> Vec<ASTNodeId> {
        let old: Vec<ASTNodeId> = children_mut(kind).into_iter().map(|slot| *slot).collect();
        let new: Vec<ASTNodeId> =
            old.iter().map(|&child| self.copy(child, subst)).collect();
        for (slot, id) in children_mut(kind).into_iter().zip(&new) {
            *slot = *id;
        }
        new
    }

    // One node copied into the arena, and the handle of the copy. A `$x` becomes
    // whatever the argument was -- copied again, so that a parameter used twice
    // is two subtrees and not one shared by two parents -- and a `@name(..)`
    // becomes the block it stands for.
    fn copy(&mut self, id: ASTNodeId, subst: &HashMap<String, ASTNodeId>) -> ASTNodeId {
        let node = self.parser.get_node(id).clone();
        let mut kind = node.kind;

        if let ASTNodeKind::MacroVar(name) = &kind {
            if let Some(&arg) = subst.get(name) {
                // The argument is copied afresh at each use, which is what makes
                // `$x` twice mean the expression twice.
                return self.copy(arg, &HashMap::new());
            }
        }

        if let ASTNodeKind::MacroCall { name, args } = &kind {
            let (name, args) = (name.clone(), args.clone());
            return self.expand_call(id, &name, &args, subst);
        }

        self.strip_decls(&mut kind);
        self.copy_children(&mut kind, subst);
        self.parser.push_node(ASTNode::new(kind, node.line, node.col))
    }

    // What one `@name(..)` becomes. The arguments are expanded where they were
    // written, so a macro handed a macro call gets the call's answer; the body
    // is then copied with them put where the parameters stood.
    fn expand_call(
        &mut self,
        at: ASTNodeId,
        name: &str,
        args: &[ASTNodeId],
        subst: &HashMap<String, ASTNodeId>,
    ) -> ASTNodeId {
        let args: Vec<ASTNodeId> = args.iter().map(|&a| self.copy(a, subst)).collect();

        let Some(def) = self.macros.get(name) else {
            self.errors.push(
                Diagnostic::error(format!("unknown macro `@{}`", name), self.span_of(at))
                    .with_label("no macro of this name")
                    .with_help("a macro is declared with `macro`, and the set is not open"),
            );
            return self.parser.push_node(ASTNode::new(ASTNodeKind::Empty, 0, 0));
        };
        let (params, body) = (def.params.clone(), def.body);

        if params.len() != args.len() {
            self.errors.push(
                Diagnostic::error(
                    format!(
                        "macro `@{}` takes {}, and {} given",
                        name,
                        count(params.len(), "argument"),
                        if args.len() == 1 { "1 was".to_string() } else { format!("{} were", args.len()) },
                    ),
                    self.span_of(at),
                )
                .with_label("wrong number of arguments")
                .with_secondary(Span::at(def.line, def.col), "declared"),
            );
            return self.parser.push_node(ASTNode::new(ASTNodeKind::Empty, 0, 0));
        }

        let mut next: HashMap<String, ASTNodeId> = HashMap::new();
        for ((param, fragment), &arg) in params.iter().zip(&args) {
            let kind = self.kind(arg);
            if !fits_fragment(&kind, fragment) {
                self.errors.push(
                    Diagnostic::error(
                        format!("`${}` wants {}, and was given {}",
                                param, fragment_word(fragment), describe(&kind)),
                        self.span_of(arg),
                    )
                    .with_label(format!("not {}", fragment_word(fragment)))
                    .with_secondary(Span::at(def.line, def.col), "the macro is declared"),
                );
            }
            next.insert(param.clone(), arg);
        }

        // A macro may invoke another and may invoke itself, and nothing here
        // proves either stops. The depth is what stands in for the proof.
        if self.depth >= MAX_DEPTH {
            self.errors.push(
                Diagnostic::error(format!("`@{}` expanded {} deep", name, MAX_DEPTH),
                                  self.span_of(at))
                    .with_label("expansion did not finish")
                    .with_note("a macro that invokes itself needs something to stop it"),
            );
            return self.parser.push_node(ASTNode::new(ASTNodeKind::Empty, 0, 0));
        }
        self.depth += 1;
        let expanded = self.copy(body, &next);
        self.depth -= 1;
        expanded
    }
}

fn count(n: usize, word: &str) -> String {
    if n == 1 { format!("1 {}", word) } else { format!("{} {}s", n, word) }
}

fn fragment_word(fragment: &str) -> &'static str {
    match fragment {
        "ident" => "a name",
        "lit" => "a literal",
        _ => "an expression",
    }
}

fn list(words: &[&str]) -> String {
    words.iter().map(|w| format!("`{}`", w)).collect::<Vec<_>>().join(", ")
}

#[cfg(test)]
mod tests;
