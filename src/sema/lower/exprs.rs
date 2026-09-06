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

            TIRExprKind::Block { stmts, tail, tail_unsafe } => {
                self.block(&stmts, tail, tail_unsafe, id)
            }

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
                    // The other way: what the pointer points at. A `deref` of
                    // anything else is the one shape here that is refused --
                    // `addr` makes a pointer out of any place and this only
                    // reads one back.
                    crate::tir::tir_nodes::TIRUnaryOp::Deref => {
                        match self.types.get(inner).clone() {
                            Ty::Ptr(to) => to,
                            Ty::Error => inner,
                            _ => {
                                let held = self.spell(inner);
                                self.errors.push(
                                    Diagnostic::error(
                                        format!("`{}` is not a pointer", held),
                                        self.at(id),
                                    )
                                    .with_label("this reads through one")
                                    .with_help(
                                        "only a `ptr` is read through; a reference \
                                         already stands for what it refers to",
                                    ),
                                );
                                self.types.error()
                            }
                        }
                    }
                };
                self.make(TTIRExprKind::Unary { op, operand: held }, ty, id)
            }

            TIRExprKind::Binary { op, lhs, rhs } => {
                let (l, r) = (self.expr(lhs), self.expr(rhs));
                // "A reference stands for the place it refers to and is read
                // and written as that place" (§3), so an operator over one is
                // an operator over what it refers to. Read through both sides
                // before anything else looks at them: what comes out is the
                // referred type, which is what has to unify, what decides
                // whether the comparison is signed, and what the answer is.
                //
                // Without this a reference was opaque to every operator. Three
                // sides of that were refusals -- "`&i64` and `i64` are not one
                // type" for anything mixed -- and the fourth was worse: `&T`
                // against `&T` unified, so it compiled, and compared the two
                // *addresses*. A comparator over a key is exactly that shape,
                // and it answered whether two keys were in the same place.
                let (l, r) = (self.read_through(l), self.read_through(r));
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
                let vt = self.out.exprs[v].ty;
                let p = self.written_to(p, vt);
                let pt = self.out.exprs[p].ty;
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
                let mut made = made;
                let ty = self.calling(c, &mut made, id);
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
                // "A range is an expression, so a slice needs no rule of its
                // own" (§5): the same `[` indexes by one and slices by two, and
                // which it did is what the index turned out to be.
                let sliced = self.is_range(self.out.exprs[i].ty);
                let ty = match self.types.get(bt).clone() {
                    Ty::Array { elem, .. } | Ty::Run(elem) => elem,
                    // A pointer is indexed like the run it stands at the front
                    // of, which is what makes a container that manages its own
                    // room writable without a spelling for the arithmetic: the
                    // stride is the element's and `mir::layout` already knows
                    // it, so nothing here has to say how wide a `T` is.
                    //
                    // Like `deref`, it wants the word: it is a read through an
                    // address the checker stopped answering for, and §4 counts
                    // it among the three things an `unsafe` is for.
                    Ty::Ptr(elem) => {
                        if self.guarded == 0 {
                            self.errors.push(
                                Diagnostic::error(
                                    "indexing a `ptr` needs an `unsafe`".to_string(),
                                    self.at(id),
                                )
                                .with_label("this reads through a pointer")
                                .with_note(
                                    "write `unsafe` in front of the statement it is in",
                                ),
                            );
                        }
                        elem
                    }
                    Ty::Ref { inner, .. } => match self.types.get(inner).clone() {
                        Ty::Array { elem, .. } | Ty::Run(elem) => elem,
                        _ => self.not_indexable(bt, id),
                    },
                    // Anything the checker already gave up on stays given up
                    // on: one complaint about the same mistake is enough.
                    Ty::Error => bt,
                    _ => self.not_indexable(bt, id),
                };
                // "What a slice denotes is the run itself: `a[1..3]` is a
                // place of type `T[]`" -- so the element type the arms above
                // worked out is what the run is *of*, and the run is what this
                // is.
                let ty = match sliced && !matches!(self.types.get(ty), Ty::Error) {
                    true => self.types.intern(Ty::Run(ty)),
                    false => ty,
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
        // Whether an `unsafe` stood in front of the tail. It guards it and
        // leaves it the block's value, which is the one place the word does
        // both -- see `TIRExprKind::Block`.
        tail_unsafe: bool,
        at: TIRExprId,
    ) -> TTIRExprId {
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
        let mut made = Vec::new();
        for stmt in stmts {
            match stmt {
                TIRStmt::Let { is_unsafe, intro, name, ty, init, .. } => {
                    self.guarded += usize::from(*is_unsafe);
                    let mut init = init.map(|i| self.expr(i));
                    self.guarded -= usize::from(*is_unsafe);
                    let written = ty.map(|t| self.ty(t));
                    // A reference to an array where the name says a view: the
                    // binding keeps the conversion and not what was written.
                    if let (Some(want), Some(got)) = (written, init) {
                        init = Some(self.viewed(got, want));
                    }
                    let ty = match (written, init) {
                        (Some(want), Some(got)) => {
                            let found = self.out.exprs[got].ty;
                            if self.types.unify(found, want).is_err()
                                && !self.views(found, want)
                            {
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
                    // "`T[]` is a type of no known size, and nothing can hold
                    // one: no local, no field, no parameter and no return may
                    // be a `T[]`. It exists only behind a reference" (§3).
                    //
                    // A slice is where one turns up without being written --
                    // `a[1..3]` is a place of type `T[]` and `let x = a[1..3]`
                    // asks a name to hold it -- so this is said here, where the
                    // name is, rather than left to the layout to fail over.
                    if matches!(self.types.get(ty), Ty::Run(_)) {
                        let held = self.spell(ty);
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` is a run and nothing holds one", held),
                                self.at(at),
                            )
                            .with_label("a name would have to know how many there are")
                            .with_help(format!(
                                "`&{}` borrows a view of it, which carries the length",
                                held
                            )),
                        );
                    }
                    // And a trait object, for the same reason said the other
                    // way round: how wide one is is not a question with an
                    // answer, which is what makes it dynamic at all.
                    if matches!(self.types.get(ty), Ty::Dyn(_)) {
                        let held = self.spell(ty);
                        self.errors.push(
                            Diagnostic::error(
                                format!("`{}` is a trait object and nothing holds one", held),
                                self.at(at),
                            )
                            .with_label("a name would have to know how wide it is")
                            .with_help(format!(
                                "`&{}` borrows one, which carries the table beside it",
                                held
                            )),
                        );
                    }
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
                    self.guarded += usize::from(*is_unsafe);
                    let expr = self.expr(*expr);
                    self.guarded -= usize::from(*is_unsafe);
                    made.push(TTIRStmt::Expr { is_unsafe: *is_unsafe, expr });
                }
                TIRStmt::Item(item) => {
                    if let Some(made_item) = self.made[self.at][*item] {
                        made.push(TTIRStmt::Item(made_item));
                    }
                }
            }
        }
        self.guarded += usize::from(tail_unsafe);
        let tail = tail.map(|t| self.expr(t));
        self.guarded -= usize::from(tail_unsafe);
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
    // `args` is taken to be written to: an argument that is a reference to an
    // array where a view was wanted is rewritten into one (`viewed`), and the
    // node the caller goes on to build has to be the rewritten one.
    fn calling(&mut self, callee: TTIRExprId, args: &mut [TTIRExprId], at: TIRExprId) -> TyId {
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
        for (i, &want) in params.iter().enumerate() {
            let Some(&got) = args.get(i) else { continue };
            let found = self.out.exprs[got].ty;
            if self.types.unify(found, want).is_err()
                && !self.weakens(found, want)
                && !self.views(found, want)
                && !self.objects(found, want)
            {
                let (found, want) = (self.spell(found), self.spell(want));
                self.errors.push(
                    Diagnostic::error(
                        format!("argument {} is `{}` and it takes `{}`", i + 1, found, want),
                        self.at(at),
                    )
                    .with_label("this is what it was handed"),
                );
            }
            args[i] = self.viewed(got, want);
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
        let Ty::Named { item, args, .. } = self.types.get(held).clone() else { return None };
        let TTIRItemKind::Struct { fields, .. } = &self.out.items[item].kind else {
            return None;
        };
        let (index, ty) = fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == name)
            .map(|(i, f)| (i, f.ty))?;
        // What the declaration calls the field's type is written in the
        // declaration's own parameters: the `v` of a `Held<T>` is a `T`. What
        // it is *here* is that with the arguments of this use put in.
        Some((index, self.types.substitute(ty, &args)))
    }

    // Whether a `*` will do where a `&` was asked for.
    //
    // "The left of each is read-only and the right of each is not" (§2): a `*`
    // is everything a `&` is and a licence besides, so handing one to
    // something that only reads takes nothing away. Without this a body
    // holding a `*` could not call anything that reads -- `fn write(p: *P) {
    // p.a = read(p) + 1 }` was refused -- which is not a rule anybody wrote
    // down, only one nobody had written the other half of.
    //
    // It goes one way and only one. A `&` handed where a `*` is wanted would
    // be a write licence made out of nothing.
    pub(super) fn weakens(&mut self, found: TyId, want: TyId) -> bool {
        let (found, want) = (self.types.get(found).clone(), self.types.get(want).clone());
        match (found, want) {
            (
                Ty::Ref { op: TIRRefOp::Mut, inner: from, .. },
                Ty::Ref { op: TIRRefOp::Imm, inner: to, .. },
            ) => self.types.unify(from, to).is_ok(),
            _ => false,
        }
    }

    // Whether a reference to a fixed array stands where a view was wanted.
    //
    // "A reference to a fixed array is a view of it: `&i32[8]` is a `&i32[]`
    // and `*i32[8]` a `*i32[]`, the length moving out of the type and into the
    // value. That conversion is the only one, and it runs one way -- a view has
    // forgotten how many there are as a matter of type, so nothing turns it
    // back" (§3). So this is asked of `(found, want)` and never of the pair the
    // other way about.
    //
    // A view that writes wants a reference that writes; one that reads takes
    // either, which is the weakening `weakens` already allows and is allowed
    // here for the same reason rather than a second time.
    pub(super) fn views(&mut self, found: TyId, want: TyId) -> bool {
        let (
            Ty::Ref { op: from_op, inner: from, .. },
            Ty::Ref { op: want_op, inner: to, .. },
        ) = (self.types.get(found).clone(), self.types.get(want).clone())
        else {
            return false;
        };
        let kept = from_op == want_op
            || (from_op == TIRRefOp::Mut && want_op == TIRRefOp::Imm);
        if !kept {
            return false;
        }
        let (Ty::Array { elem, .. }, Ty::Run(held)) =
            (self.types.get(from).clone(), self.types.get(to).clone())
        else {
            return false;
        };
        self.types.unify(elem, held).is_ok()
    }

    // Whether a reference to something becomes a reference to a trait object.
    //
    // The same shape as `views` above and for the same reason: one type
    // standing where another was wanted, with the reference kept and what is
    // behind it widened. `&Sq` becomes `&dyn Shape` where `Sq` answers
    // `Shape`, and a `*` stands where a `&` is wanted as it does everywhere.
    //
    // What makes it sound is that nothing goes the other way: a `&dyn Shape`
    // is not a `&Sq`, having forgotten which type it was.
    pub(super) fn objects(&mut self, found: TyId, want: TyId) -> bool {
        let (
            Ty::Ref { op: from_op, inner: from, .. },
            Ty::Ref { op: want_op, inner: to, .. },
        ) = (self.types.get(found).clone(), self.types.get(want).clone())
        else {
            return false;
        };
        let kept = from_op == want_op
            || (from_op == TIRRefOp::Mut && want_op == TIRRefOp::Imm);
        if !kept {
            return false;
        }
        let Ty::Dyn(of) = self.types.get(to).clone() else { return false };
        let Ty::Named { item, .. } = self.types.get(from).clone() else { return false };
        self.answers(item, of)
    }

    // Whether that type has an impl of that trait. What `dyn` is held to: a
    // reference becomes an object only where there is something for the table
    // to be built out of.
    pub(super) fn answers(&self, item: TTIRItemId, of: TTIRItemId) -> bool {
        self.out.items.iter().any(|held| {
            let TTIRItemKind::Impl { ty, of: written, .. } = &held.kind else { return false };
            *written == Some(of)
                && matches!(self.types.get(*ty), Ty::Named { item: subject, .. }
                            if *subject == item)
        })
    }

    // The expression as a view, where a view is what was wanted and what it is
    // is a reference to an array. Anything else comes back as it was.
    //
    // The node is a `Cast`, which is not a lie about what this is: a cast is
    // the tree's word for a value that keeps what it means and changes how it
    // is written down, and `&i32[8]` to `&i32[]` is exactly that. It flows
    // through every IR already, and `mir::lower` is where the length actually
    // moves out of the type and into the value.
    pub(super) fn viewed(&mut self, got: TTIRExprId, want: TyId) -> TTIRExprId {
        let found = self.out.exprs[got].ty;
        if !self.views(found, want) && !self.objects(found, want) {
            return got;
        }
        // Where the operand stands, for the reason `read_through` gives: nobody
        // wrote this conversion, so it has no place of its own in the source.
        let (line, col) = (self.out.exprs[got].line, self.out.exprs[got].col);
        self.out.exprs.push(TTIRExpr {
            kind: TTIRExprKind::Cast(got),
            ty: want,
            line,
            col,
        });
        self.out.exprs.len() - 1
    }

    // An expression with the references taken off it, which is one read out
    // of the place each refers to. A `&&T` reads twice, one layer at a time,
    // as §3 says everything about a reference to a reference goes.
    //
    // The node is a `Deref`, which is the same node `deref p` makes and lowers
    // the same way -- `sir::lower` turns it into a `Load` of what the operand
    // holds, and a reference held in a register holds an address just as a
    // pointer does. What it does *not* go through is the checking `deref p`
    // gets: no `unsafe` is asked for, because §4 wants the word for a read
    // through a pointer and this is a read through a reference, which is the
    // one kind of address the checker still answers for.
    fn read_through(&mut self, expr: TTIRExprId) -> TTIRExprId {
        let mut held = expr;
        while let Ty::Ref { inner, .. } = self.types.get(self.out.exprs[held].ty).clone() {
            // Built here rather than through `make`, which wants a place in
            // the *source* to take a line from. There is none: nobody wrote
            // this read. So it stands where the operand it reads stands.
            let (line, col) = (self.out.exprs[held].line, self.out.exprs[held].col);
            self.out.exprs.push(TTIRExpr {
                kind: TTIRExprKind::Unary { op: TIRUnaryOp::Deref, operand: held },
                ty: inner,
                line,
                col,
            });
            held = self.out.exprs.len() - 1;
        }
        held
    }

    // The place an assignment lands on, given what is being put there.
    //
    // "A reference is transparent (section 3), so a name of type `*T` is a
    // place too, and what assigning to it does depends on what is assigned: a
    // value of type T is written through to the referent, and a reference of
    // type *T re-aims the name itself" (§5). So this is `read_through`'s
    // mirror, and it differs from it in the one way §8 sets out: the type
    // decides, "matching exactly and reaching one step".
    //
    // Exactly first, which is what makes a re-aim a re-aim: `cur = *b` puts a
    // reference in `cur`, and only if that cannot be what was meant is the
    // value written through to what `cur` refers to. `agrees` and not `unify`
    // for the asking, so that a question fills nothing in -- the answer is
    // committed to by the `unify` the caller does afterwards, once.
    //
    // And one step and not a chain, which is the asymmetry §8 names: reading
    // walks a chain of references to the bottom and writing reaches one place
    // down. A `**T` written to with a `T` is left to the caller's `unify` to
    // turn down rather than quietly reaching two steps, because a write that
    // went as far as it had to would make `p = q` mean something that depends
    // on how deep `p` happens to be.
    fn written_to(&mut self, place: TTIRExprId, value: TyId) -> TTIRExprId {
        let ty = self.out.exprs[place].ty;
        if self.types.agrees(value, ty) {
            return place;
        }
        let Ty::Ref { inner, .. } = self.types.get(ty).clone() else { return place };
        if !self.types.agrees(value, inner) {
            return place;
        }
        // Built here rather than through `make`, for `read_through`'s reason:
        // nobody wrote this, so it stands where the place it writes through
        // stands.
        let (line, col) = (self.out.exprs[place].line, self.out.exprs[place].col);
        self.out.exprs.push(TTIRExpr {
            kind: TTIRExprKind::Unary { op: TIRUnaryOp::Deref, operand: place },
            ty: inner,
            line,
            col,
        });
        self.out.exprs.len() - 1
    }

    // What indexing something that cannot be indexed comes to. It used to come
    // to `Ty::Error` with nothing said, which is a program accepted for a
    // reason nobody was told -- the error type is what a *reported* mistake
    // leaves behind and not a way of declining to report one.
    fn not_indexable(&mut self, ty: TyId, id: TIRExprId) -> TyId {
        let spelt = self.spell(ty);
        self.errors.push(
            Diagnostic::error(format!("`{}` cannot be indexed", spelt), self.at(id))
                .with_label("this is indexed here")
                .with_note("only an array, a run and a `ptr` may be"),
        );
        self.types.error()
    }
}

fn answers_bool(op: TIRBinOp) -> bool {
    matches!(
        op,
        TIRBinOp::Eq | TIRBinOp::Ne | TIRBinOp::Lt | TIRBinOp::Gt | TIRBinOp::Le
            | TIRBinOp::Ge | TIRBinOp::And | TIRBinOp::Or | TIRBinOp::Xor
    )
}
