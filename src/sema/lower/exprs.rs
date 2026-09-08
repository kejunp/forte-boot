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
        // Taken, so it reaches this expression and no other. What passes it
        // on says so by setting it again -- see `Lowerer::want`.
        let want = self.want.take();
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
                self.block(&stmts, tail, tail_unsafe, want, id)
            }

            TIRExprKind::Unary { op, operand } => {
                // A `&` is transparent to what is expected of it: `&[&a, &b]`
                // where a `&(&dyn Show)[]` was wanted has to hand the array
                // what the reference was told, or the elements never hear it.
                // The other three take a value and make something else of it,
                // so what is wanted of the whole says nothing about the part.
                if let crate::tir::tir_nodes::TIRUnaryOp::Ref(_) = op {
                    if let Some(Ty::Ref { inner, .. }) =
                        want.map(|held| self.types.get(held).clone())
                    {
                        self.want = Some(inner);
                    }
                }
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
                // A pointer and a number, which is the one shape here whose
                // two sides are not one type. `p + n` is the address `n`
                // elements along and `p - n` the one `n` back: it steps by the
                // element's stride, as `p[n]` does, being the same arithmetic
                // written without the read on the end.
                if let Some(made) = self.stepped(op, l, r, id) {
                    return made;
                }
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
                // The left of an `=` is somewhere a value already is. Anything
                // else is a value that was worked out, and there is nowhere to
                // put one -- `(a, b) = (b, a)` parses, being two expressions
                // with an `=` between them, and used to lower to a store to a
                // tuple built on the spot: accepted, and doing nothing at all.
                //
                // The borrow checker asks the same question of the same place
                // and is the one that says a `let` may not be written to. It
                // answers `None` for a `ptr` on purpose, and for a global,
                // so it is not the pass that can tell a place from a value.
                let pt = self.out.exprs[p].ty;
                if !addressable(&self.out.exprs[p].kind)
                    && !matches!(self.types.get(pt), Ty::Error)
                {
                    self.errors.push(
                        Diagnostic::error(
                            "this cannot be assigned to".to_string(),
                            self.at(place),
                        )
                        .with_label("this is a value, not a place")
                        .with_help(
                            "a name, a field, an element, or what a reference \
                             refers to is what an `=` writes into -- \
                             `let (a, b) = (b, a)` is how two names are bound \
                             at once",
                        ),
                    );
                }
                // "assigning to one takes a `*`" -- the least the body asks of
                // it turns out to be more than a read.
                if let TTIRExprKind::Local(slot) = self.out.exprs[p].kind {
                    self.assigns_to(slot);
                }
                let vt = self.out.exprs[v].ty;
                let p = self.written_to(p, vt);
                let pt = self.out.exprs[p].ty;
                // The place is what is expected of the value, exactly as a
                // name's written type is: "the right of an assignment" is one
                // of the places an expectation reaches (§5), and it was the
                // one that did not. So `held = List::Cons(..)` where `held` is
                // a `gc List` was "`List` cannot be assigned to `gc List`" --
                // the conversion a `let gc` makes, refused because the value
                // was reached by an `=` rather than by a `let`.
                let v = self.viewed(v, pt);
                let vt = self.out.exprs[v].ty;
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
                    // `T::f(&q)`: a method named through the declaration it
                    // belongs to, the receiver written first.
                    if let Some(made) = self.named_method(&path, &args, id) {
                        return made;
                    }
                }
                if let TIRExprKind::Field { base, name } = self.tir.exprs[callee].kind.clone() {
                    if let Some(made) = self.method(base, &name, &args, id) {
                        return made;
                    }
                }
                let c = self.expr(callee);
                // What each parameter is, where the callee says plainly. A
                // generic one is left alone: what its parameters stand for is
                // not settled until the call is, and offering a hole as an
                // expectation would be offering nothing twice. `calling` below
                // is still where a conversion is committed -- this only lets an
                // argument that is itself a choice, or an array, hear what was
                // wanted of it before its parts are worked out.
                let hints: Vec<Option<TyId>> = match self.types.get(self.out.exprs[c].ty) {
                    Ty::Fn { params, .. } if !self.types.has_param(self.out.exprs[c].ty) => {
                        params.iter().map(|&p| Some(p)).collect()
                    }
                    _ => Vec::new(),
                };
                let made: Vec<TTIRExprId> = args
                    .iter()
                    .enumerate()
                    .map(|(i, &a)| {
                        self.want = hints.get(i).copied().flatten();
                        self.expr(a)
                    })
                    .collect();
                let mut made = made;
                let (ty, types) = self.calling(c, &mut made, id);
                self.make(TTIRExprKind::Call { callee: c, args: made, types }, ty, id)
            }

            TIRExprKind::If { cond, then, els } => {
                let c = self.expr(cond);
                let asks = self.types.prim(TIRPrim::Bool);
                let got = self.out.exprs[c].ty;
                if self.types.unify(got, asks).is_err() {
                    let got = self.spell(got);
                    self.errors.push(
                        Diagnostic::error(
                            format!("an `if` asks a `bool` and this is `{}`", got),
                            self.at(cond),
                        )
                        .with_label("this is the condition"),
                    );
                }
                // Both branches are handed what was wanted of the `if`: an
                // `if` is a choice among values and nothing else, so what is
                // expected of it is expected of each of them.
                self.want = want;
                let t = self.expr(then);
                let t = self.held_to(t, want);
                let e = els.map(|e| {
                    self.want = want;
                    let held = self.expr(e);
                    self.held_to(held, want)
                });
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
                // A reference is cast as the place it refers to is, which is
                // the rule §3 gives for everything else one is: read, called,
                // indexed, reached into. A cast had been the one thing that
                // took the reference itself -- so `r as i64` on a `&i32` was
                // the *address* widened, and it said nothing about it. What
                // that looked like was an assertion reporting `left:
                // 140721311482340` where a 5 was meant to be.
                //
                // To a primitive only. A `ptr` is deliberately not read
                // through -- "`p as i64`, `n as ptr u8` and `p as ptr i32` all
                // lower to a conversion of the width they are" (§8), and an
                // address is exactly what a `ptr` cast is about; and a `&T as
                // ptr T` is left alone for the same reason, `addr` being how
                // an address is asked for by name.
                let held = self.types.shallow(to);
                let v = match self.types.get(held) {
                    Ty::Prim(_) => self.read_through(v),
                    _ => v,
                };
                self.make(TTIRExprKind::Cast(v), to, id)
            }

            TIRExprKind::TupleLit(members) => {
                let made: Vec<TTIRExprId> = members.iter().map(|&m| self.expr(m)).collect();
                let tys: Vec<TyId> = made.iter().map(|&m| self.out.exprs[m].ty).collect();
                let ty = self.types.intern(Ty::Tuple(tys));
                self.make(TTIRExprKind::TupleLit(made), ty, id)
            }

            TIRExprKind::ArrayLit(elems) => {
                // What each element is expected to be, where anything expects
                // one: an array of what was wanted, or a run of it.
                //
                // It stands as a *virtual first element*, which is what makes
                // this one rule rather than two. With no expectation `held`
                // starts empty, the first element fills it and the rest unify
                // against it -- which is exactly what this did before. With
                // one, the expectation is what they all unify against, and
                // each converts to it first. That order is the point:
                // `&[&a, &b]` where the two are references to different
                // structs are two types that never agree, and each becoming a
                // `&dyn Shape` before they are compared is what makes them one.
                let want = match want.map(|held| self.types.get(held).clone()) {
                    Some(Ty::Array { elem, .. }) | Some(Ty::Run(elem)) => Some(elem),
                    _ => None,
                };
                let mut made: Vec<TTIRExprId> = Vec::with_capacity(elems.len());
                let mut held: Option<TyId> = want;
                for &e in &elems {
                    self.want = want;
                    let one = self.expr(e);
                    let one = self.held_to(one, want);
                    made.push(one);
                    let ty = self.out.exprs[one].ty;
                    match held {
                        None => held = Some(ty),
                        Some(first) => match self.types.unify(first, ty) {
                            Ok(one) => held = Some(one),
                            Err(_) => {
                                self.errors.push(
                                    Diagnostic::error(
                                        "an array holds one type".to_string(),
                                        self.at(id),
                                    )
                                    .with_label("these are not all one"),
                                );
                                held = Some(self.types.error());
                                break;
                            }
                        },
                    }
                }
                let elem = match held {
                    Some(held) => held,
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
                    // Not a tuple at all. Quiet where the base is an error
                    // already or a hole nothing has filled -- reporting the
                    // second would be guessing -- and said plainly otherwise,
                    // this being the one way `.0` was ever wrong before.
                    _ => {
                        if self.types.not_a_tuple(bt) {
                            // A hole a number goes in spells as `_`, which
                            // says nothing here; what it will come to does.
                            let held = match self.types.standing(bt) {
                                Some(prim) => crate::sema::types::prim_name(prim).to_string(),
                                None => self.spell(bt),
                            };
                            self.errors.push(
                                Diagnostic::error(
                                    format!("`.{}` reads a member out of a tuple", index),
                                    self.at(id),
                                )
                                .with_label(format!("this is {}", held)),
                            );
                        }
                        self.types.error()
                    }
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
                    Ty::Ref { inner, .. } | Ty::GC(inner) => {
                        match self.types.get(inner).clone() {
                            Ty::Array { elem, .. } | Ty::Run(elem) => elem,
                            _ => self.not_indexable(bt, id),
                        }
                    }
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
                let ret = self.frames.last().expect("a frame").ret;
                let v = value.map(|v| self.expecting(v, ret));
                if let Some(v) = v {
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
            TIRExprKind::Match { scrutinee, arms } => {
                self.matching(scrutinee, &arms, want, id)
            }

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
                let (ty, args) = self.instantiate(made, Some(held), id);
                // The node is spent: what is left is the base, with the type
                // the arguments made of it -- and the arguments themselves put
                // where the call can find them, there being nothing left in
                // the type to work them back out of.
                self.out.exprs[made].ty = ty;
                if !args.is_empty() {
                    self.written_args.insert(made, args);
                }
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
        // What was expected of the block, which is what is expected of its
        // tail. See `Lowerer::want`.
        want: Option<TyId>,
        at: TIRExprId,
    ) -> TTIRExprId {
        self.frames.last_mut().expect("a frame").scopes.push(HashMap::new());
        let mut made = Vec::new();
        for stmt in stmts {
            match stmt {
                TIRStmt::Let { is_unsafe, is_gc, intro, name, ty, init, .. } => {
                    self.guarded += usize::from(*is_unsafe);
                    // The type the name was declared with is what is expected
                    // of what fills it, so a branch inside knows it too.
                    let said = ty.map(|t| self.ty(t));
                    let mut init = init.map(|i| match said {
                        Some(want) => self.expecting(i, want),
                        None => self.expr(i),
                    });
                    self.guarded -= usize::from(*is_unsafe);
                    let mut written = said;
                    // `let gc x = e` with no type written is a `gc` of
                    // whatever `e` came to. The word is on the binding and the
                    // type is what it makes: writing `gc Buf` says the same
                    // thing, and one of the two has to be the other's, or the
                    // word would mean one thing on a `let` and another in a
                    // signature.
                    if *is_gc && written.is_none() {
                        if let Some(got) = init {
                            let found = self.out.exprs[got].ty;
                            written = Some(self.types.intern(Ty::GC(found)));
                        }
                    }
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
                                && !self.objects(found, want)
                                && !self.collects(found, want)
                                && !self.borrows(found, want)
                                && !self.reads(found, want)
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
                    // A run or a trait object, which nothing holds. Said
                    // here and not only where a type is written, because this
                    // is where one turns up without being written: `a[1..3]`
                    // is a place of type `T[]`, and `let x = a[1..3]` asks a
                    // name to hold it.
                    self.unheld(ty, self.at(at));
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
        // The tail is what the block is worth, so what was expected of the
        // block is expected of it.
        let tail = tail.map(|t| {
            self.want = want;
            let held = self.expr(t);
            self.held_to(held, want)
        });
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
    fn calling(
        &mut self,
        callee: TTIRExprId,
        args: &mut [TTIRExprId],
        at: TIRExprId,
    ) -> (TyId, Vec<TyId>) {
        // Every parameter of what is called gets a hole, so `id(1)` works out
        // its own `T` -- "what it stands for is settled at the call and not at
        // the declaration".
        let (ct, types) = self.instantiate(callee, None, at);
        // Or what a written `<type_args>` settled before this was reached,
        // which leaves nothing in the type for `instantiate` to work out.
        let types = match types.is_empty() {
            true => self.written_args.get(&callee).cloned().unwrap_or_default(),
            false => types,
        };
        // Through the hole: what a generic gave back is a `Ty::Var` until
        // something fills it, so `at(&v, 0)(4)` on a `Vec<fn(i64): i64>` --
        // where the vector had already filled it with a fn type -- did not
        // look like a fn and was refused as "`fn(i64): i64` is not a fn",
        // which is the message spelling what this did not read.
        let Ty::Fn { params, ret, .. } = self.types.get(self.types.shallow(ct)).clone() else {
            if !matches!(self.types.get(ct), Ty::Error) {
                let ct = self.spell(ct);
                self.errors.push(
                    Diagnostic::error(format!("`{}` is not a fn", ct), self.at(at))
                        .with_label("this is called"),
                );
            }
            return (self.types.error(), Vec::new());
        };
        if params.len() != args.len() {
            self.errors.push(
                Diagnostic::error(
                    format!("this takes {} and was handed {}", params.len(), args.len()),
                    self.at(at),
                )
                .with_label("the wrong number of arguments"),
            );
            return (ret, types);
        }
        for (i, &want) in params.iter().enumerate() {
            let Some(&got) = args.get(i) else { continue };
            let found = self.out.exprs[got].ty;
            if self.types.unify(found, want).is_err()
                && !self.weakens(found, want)
                && !self.views(found, want)
                && !self.objects(found, want)
                && !self.collects(found, want)
                && !self.borrows(found, want)
                && !self.reads(found, want)
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
        (ret, types)
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
        // Through the hole first. What a generic gave back is a `Ty::Var`
        // until something fills it, and `at(&v, 3)` on a `Vec<gc Buf>` is
        // exactly that -- the arm below reads the entry as it stands, so a
        // hole that had been filled with a `gc Buf` read as no struct at all.
        let ty = self.types.shallow(ty);
        // A reference stands for the place it refers to, so reaching into one
        // reaches into what it refers to (§3). A `gc` value is read through
        // the same way and for the same reason: it is one word holding an
        // address, and the word on it is not meant to be spent at every use.
        let held = match self.types.get(ty).clone() {
            Ty::Ref { inner, .. } | Ty::GC(inner) => inner,
            _ => ty,
        };
        let held = self.types.shallow(held);
        // A run's length, which the value carries and nothing could ask for.
        // "The length moving out of the type and into the value" (§3) is what a
        // view is, and the value has been two words since -- where the elements
        // begin and how many there are -- with only the first of them reachable.
        //
        // One field and not two: where the elements *begin* is an address, and
        // handing one out is what `ptr` is for and what an index already does
        // without it.
        if matches!(self.types.get(held), Ty::Run(_)) {
            return match name {
                "len" => Some((1, self.types.prim(TIRPrim::I64))),
                _ => None,
            };
        }
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
        // Through the holes first. What a generic gave back is a `Ty::Var`
        // until something fills it and the arms below read the entry as it
        // stands, so a `T` the checker had already settled did not look like
        // the type it had been settled as -- see `objects`, where the same
        // omission made `push(*v, &q)` on a `Vec<&dyn Shape>` a refusal.
        let (found, want) = (self.types.shallow(found), self.types.shallow(want));
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
        // Through the holes first, both sides. What a generic gave back is a
        // `Ty::Var` until something fills it and the arms below read the entry
        // as it stands -- so `push(*v, &q)` on a `Vec<&dyn Shape>`, where the
        // parameter is a hole the vector had already filled with `&dyn Shape`,
        // did not look like a reference to a trait object and was refused as
        // "argument 2 is `&Sq` and it takes `&dyn Shape`".
        let (found, want) = (self.types.shallow(found), self.types.shallow(want));
        // The two shapes a trait object stands behind. A reference is the
        // borrowed one and a `gc` the owned: "a trait object lives as long as
        // what it was made from, so a container of them wants a `gc` of one",
        // and the two are the same two words -- where the value is, and where
        // the routines that answer for it are.
        //
        // A `gc` of one is made from a `gc` of what it was and from nothing
        // else. Handing the *collector's* handle over is the whole of what
        // makes it owned: a reference would be an address into a frame, and an
        // object made from one would outlive what it was made from.
        let (from, to) = match (self.types.get(found).clone(), self.types.get(want).clone()) {
            (
                Ty::Ref { op: from_op, inner: from, .. },
                Ty::Ref { op: want_op, inner: to, .. },
            ) => {
                // A `*` stands where a `&` is asked for and not the other way
                // round: a promise to read is no promise to write.
                let kept = from_op == want_op
                    || (from_op == TIRRefOp::Mut && want_op == TIRRefOp::Imm);
                if !kept {
                    return false;
                }
                (from, to)
            }
            (Ty::GC(from), Ty::GC(to)) => (from, to),
            _ => return false,
        };
        let (from, to) = (self.types.shallow(from), self.types.shallow(to));
        let Ty::Dyn(of) = self.types.get(to).clone() else { return false };
        // By head and not by name: a primitive answers a trait exactly as a
        // struct does (`impl Show for i64`), so `&5` becomes a `&dyn Show`
        // wherever a `&Sq` becomes one.
        // A parameter answers by its bound. `fn f<T: Show>(x: &T)` has said
        // that whatever `T` turns out to be answers `Show`, so an object may
        // be made of it -- and which table is built is a question for the
        // instance, where `T` is a type and not a name. Without this a bound
        // bought a method call and nothing else: `by_table(x)` inside such a
        // body was "argument 1 is `&T` and it takes `&dyn Show`".
        if matches!(self.types.get(from), Ty::Param { .. }) {
            return self.answers_to(from, of);
        }
        let head = head_of(self.types.get(from));
        if self.answers(&head, of) {
            return true;
        }
        // A literal that was never told what it is. `&5` beside a `&dyn Show`
        // is a hole with no impl written for it, because a hole is not a type
        // anybody writes an impl for -- so what is asked instead is the type
        // it would settle as, which is the guess `finish` makes at the end and
        // the one every unsuffixed number ends up taking.
        //
        // Asked and not taken: the hole is left standing, so a line further
        // down may still fill it with something else. `let n = 5` used as an
        // object and then as an `i64` is an `i64`, and the table is built for
        // what it ended as rather than for what was guessed halfway through.
        // Which means this answer is provisional, and `objects_answered` in
        // `lower.rs` is what holds it: the same question, asked once more of
        // every object in the finished tree, when there is nothing left to
        // guess about.
        let Some(prim) = self.types.standing(from) else { return false };
        self.answers(&head_of(&Ty::Prim(prim)), of)
    }

    // `p + n` and `p - n`: the address that many elements along.
    //
    // The one operator here whose two sides are not one type, and it has to
    // be: "`p[i]` is a place, under the same `unsafe` and stepping by the same
    // stride an indexed run steps by, and it is the whole of the pointer
    // arithmetic a container needs" (§2) -- which left the *general*
    // arithmetic, an address rather than a number, with no spelling at all.
    // A `Vec` that wants the element after the one it holds had to index a
    // place and take its address back, which is a read the program did not
    // want and a word it should not have needed.
    //
    // It steps by the element's stride and not by bytes, which is what makes
    // it arithmetic on a `ptr T` rather than on a number: `p + 1` is the next
    // T however wide a T is, and a byte offset is written on a `ptr u8`.
    //
    // No `unsafe`. "Where `ptr` is written is not itself the unsafe thing --
    // what needs the word is making one and reaching through one" (§2), and
    // this is neither: the address was already in hand and nothing is read.
    // The `deref` or the `p[i]` that follows is where the word goes.
    fn stepped(
        &mut self,
        op: TIRBinOp,
        lhs: TTIRExprId,
        rhs: TTIRExprId,
        at: TIRExprId,
    ) -> Option<TTIRExprId> {
        if !matches!(op, TIRBinOp::Add | TIRBinOp::Sub) {
            return None;
        }
        let (lt, rt) = (self.out.exprs[lhs].ty, self.out.exprs[rhs].ty);
        let Ty::Ptr(_) = self.types.get(self.types.shallow(lt)).clone() else { return None };
        // The other side is a whole number, which is what an offset is. A hole
        // that takes numbers is one too and takes an `i64` here, there being
        // nothing else for it to be.
        let whole = self.types.prim(TIRPrim::I64);
        if self.types.unify(rt, whole).is_err() {
            let (lt, rt) = (self.spell(lt), self.spell(rt));
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` steps by a whole number and this is `{}`", lt, rt),
                    self.at(at),
                )
                .with_label("this is what it was given")
                .with_note("`p + n` is the address n elements along, so n counts elements"),
            );
            return Some(self.errored(at));
        }
        Some(self.make(TTIRExprKind::Binary { op, lhs, rhs }, lt, at))
    }

    // Whether that type has an impl of that trait. What `dyn` is held to: a
    // reference becomes an object only where there is something for the table
    // to be built out of.
    pub(super) fn answers(&self, head: &Head, of: TTIRItemId) -> bool {
        self.out.items.iter().any(|held| {
            let TTIRItemKind::Impl { ty, of: written, .. } = &held.kind else { return false };
            *written == Some(of) && head_of(self.types.get(*ty)) == *head
        })
    }

    // Lower one expression with something expected of it, and hold it to
    // that: the conversions are the three `viewed` knows, and a branch that
    // came back as something else is left alone for whoever asked to report.
    pub(super) fn expecting(&mut self, id: TIRExprId, want: TyId) -> TTIRExprId {
        self.want = Some(want);
        let got = self.expr(id);
        self.want = None;
        self.viewed(got, want)
    }

    // And the same for one already lowered, which is what a branch is by the
    // time the node holding it knows the branches agreed on nothing.
    pub(super) fn held_to(&mut self, got: TTIRExprId, want: Option<TyId>) -> TTIRExprId {
        match want {
            Some(want) => self.viewed(got, want),
            None => got,
        }
    }

    // Whether a value becomes one the collector holds. `gc T` is what a
    // `let gc` makes and what a signature may take, so a `T` standing where
    // one was wanted is the conversion that puts it on the heap -- and it is
    // the third of the three written the same way, beside the view and the
    // trait object.
    //
    // One way only, as those two are: a `gc T` handed where a `T` was wanted
    // is not one, because taking the value out of the collector's room is
    // giving away something the collector still holds.
    pub(super) fn collects(&mut self, found: TyId, want: TyId) -> bool {
        let (found, want) = (self.types.shallow(found), self.types.shallow(want));
        let Ty::GC(inner) = self.types.get(want).clone() else { return false };
        if matches!(self.types.get(found), Ty::GC(_)) {
            return false;
        }
        self.types.unify(found, inner).is_ok()
    }

    // A collected value where a reference is wanted.
    //
    // "It is one word -- the address the collector handed back -- and it is
    // reached through exactly as a reference is" (§2), so a `gc T` stands
    // where a `&T` does: the two are the same word and the same thing at the
    // far end of it. Without this a collected value could only be handed to
    // something written to take one, so an `fn sum(l: &List)` could not be
    // called on a list the collector held -- and a recursive structure is the
    // reason there is a collector.
    //
    // A reference to one counts, and is where this is really wanted: matching
    // through a reference binds references (§8), so the `r` of an
    // `L::Cons(n, r)` is a `&gc L` and what it is handed to takes a `&L`. That
    // one is a read and not a retype -- the handle has to be fetched out of
    // the place holding it -- which is what `viewed` writes the `Deref` for.
    //
    // Only a `&`, never a `*`. A `gc` copies, so two names may hold one
    // handle; handing out something that may be written through would be
    // handing out one of two exclusive references to one value.
    pub(super) fn borrows(&mut self, found: TyId, want: TyId) -> bool {
        let (found, want) = (self.types.shallow(found), self.types.shallow(want));
        let Ty::Ref { op: TIRRefOp::Imm, inner: to, .. } = self.types.get(want).clone() else {
            return false;
        };
        let held = match self.types.get(found).clone() {
            Ty::GC(inner) => inner,
            Ty::Ref { inner, .. } => match self.types.get(self.types.shallow(inner)).clone() {
                Ty::GC(inner) => inner,
                _ => return false,
            },
            _ => return false,
        };
        self.types.unify(held, to).is_ok()
    }

    // Whether that conversion is the one that reads a handle out of a place
    // first: a `&gc T` becoming a `&T` rather than a `gc T` becoming one.
    fn borrows_through(&mut self, found: TyId) -> bool {
        matches!(self.types.get(self.types.shallow(found)), Ty::Ref { .. })
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
        // Where the operand stands, for the reason `read_through` gives: nobody
        // wrote this conversion, so it has no place of its own in the source.
        let (line, col) = (self.out.exprs[got].line, self.out.exprs[got].col);
        // A read out of a reference is not a cast: it is the same `Deref`
        // `read_through` makes, and `sir::lower` turns it into the `Load` that
        // `alias` and the two memory passes already understand. A cast would be
        // a lie about what happens -- the value moves, and this one goes and
        // fetches it.
        if self.reads(found, want) {
            self.out.exprs.push(TTIRExpr {
                kind: TTIRExprKind::Unary { op: TIRUnaryOp::Deref, operand: got },
                ty: want,
                line,
                col,
            });
            return self.out.exprs.len() - 1;
        }
        // A collected value handed where a reference is wanted. Where the
        // handle is in a place rather than in hand, it is read out of that
        // place first and the retype is over what came back.
        if self.borrows(found, want) {
            let got = match self.borrows_through(found) {
                true => self.read_through(got),
                false => got,
            };
            self.out.exprs.push(TTIRExpr {
                kind: TTIRExprKind::Cast(got),
                ty: want,
                line,
                col,
            });
            return self.out.exprs.len() - 1;
        }
        if !self.views(found, want)
            && !self.objects(found, want)
            && !self.collects(found, want)
        {
            return got;
        }
        self.out.exprs.push(TTIRExpr {
            kind: TTIRExprKind::Cast(got),
            ty: want,
            line,
            col,
        });
        self.out.exprs.len() - 1
    }

    // Whether a reference stands where what it refers to was wanted.
    //
    // "A reference stands for the place it refers to and is read, called,
    // indexed and reached into exactly as that place is" (§3) -- and that had
    // been true of every one of those but *read*. `read_through` is the rule,
    // and it was wired into one place only: the operands of a binary operator.
    // So `a + &b` worked and `f(&b)` did not, and neither did giving one back
    // where the signature says the value.
    //
    // A primitive and nothing else, for now. Every primitive copies, so there
    // is no question here about moving out of a reference -- which is exactly
    // the question a `&Buf` read as a `Buf` would be asking, and it is the
    // borrow checker's to answer rather than this one's. Widening it is a
    // separate change with a real argument attached.
    pub(super) fn reads(&mut self, found: TyId, want: TyId) -> bool {
        let (found, want) = (self.types.shallow(found), self.types.shallow(want));
        let inner = match self.types.get(found).clone() {
            Ty::Ref { inner, .. } | Ty::GC(inner) => inner,
            _ => return false,
        };
        if !matches!(self.types.get(inner), Ty::Prim(_)) {
            return false;
        }
        self.types.unify(inner, want).is_ok()
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
    pub(super) fn read_through(&mut self, expr: TTIRExprId) -> TTIRExprId {
        let mut held = expr;
        while let Ty::Ref { inner, .. } | Ty::GC(inner) =
            self.types.get(self.out.exprs[held].ty).clone()
        {
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


// Somewhere the source can name, which is somewhere a value already is -- the
// same predicate `gir::lower` holds a place to, with the one crossing it does
// not need: `deref p = 1` puts a `Deref` where the store goes, and that is a
// place as much as a field of one is.
fn addressable(kind: &TTIRExprKind) -> bool {
    matches!(
        kind,
        TTIRExprKind::Local(_)
            | TTIRExprKind::Item(_)
            | TTIRExprKind::SelfExpr
            | TTIRExprKind::Field { .. }
            | TTIRExprKind::TupleIndex { .. }
            | TTIRExprKind::Index { .. }
            | TTIRExprKind::Unary { op: TIRUnaryOp::Deref, .. }
    )
}
