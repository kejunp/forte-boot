// Every expression, and the type that comes out of it.
//
// The walk is the ordinary one -- an expression's parts first, then the
// expression -- and what makes it the interesting pass is what happens between
// the two: each kind of expression says what its parts must agree about, and
// `Types` is what remembers the agreement. `a + b` says both sides are one
// type and the answer is that type; `if c { x } else { y }` says the condition
// is a `bool` and the two arms are one type; and a hole that nothing ever
// filled is where a refusal comes from.
//
// The shapes that need more than a paragraph are in files of their own: struct
// literals, `match`, closures, the three containers, loops and paths. What is
// here is everything that fits in one.

use std::collections::HashMap;

use crate::error::{Diagnostic, Span};
use crate::tir::tir_nodes::*;
use crate::tir::ttir_nodes::*;

use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn expr(&mut self, id: TIRExprId) -> TTIRExprId {
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
    pub(super) fn item_ty(&mut self, item: TTIRItemId) -> TyId {
        match &self.out.items[item].kind {
            TTIRItemKind::Fn(f) => f.ty,
            TTIRItemKind::Const { ty, .. } | TTIRItemKind::Global { ty, .. } => *ty,
            _ => self.types.error(),
        }
    }

    // A field by the name it was written with, and the index it turned out to
    // be: "Reached by index rather than by name: which field `x` is, is
    // settled."
    pub(super) fn field_of(&mut self, ty: TyId, name: &str) -> Option<(usize, TyId)> {
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

fn answers_bool(op: TIRBinOp) -> bool {
    matches!(
        op,
        TIRBinOp::Eq | TIRBinOp::Ne | TIRBinOp::Lt | TIRBinOp::Gt | TIRBinOp::Le
            | TIRBinOp::Ge | TIRBinOp::And | TIRBinOp::Or | TIRBinOp::Xor
    )
}
