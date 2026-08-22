// What the checker turns down. The TTIR is built by hand, `sema` being the pass
// that produces one from source, which these do not go through.

use super::*;
use crate::error::Source;
use crate::tir::tir_nodes::{
    TIRAssignOp, TIRAttrs, TIRFnAttrs, TIRInline, TIRIntro, TIRLit, TIRPrim, TIRVis,
};
use crate::tir::ttir_nodes::*;

// A body under construction. Every expression gets a line of its own, counting
// up, so a report can be read against a source that was never written: line 3
// is the third thing built.
struct Suite {
    p:      TTIRProgram,
    locals: Vec<TTIRLocal>,
    line:   usize,
}

impl Suite {
    const NULL: TyId = 0;
    const I32: TyId = 1;
    const BOOL: TyId = 2;

    fn new() -> Suite {
        let mut p = TTIRProgram::default();
        p.types.push(Ty::Prim(TIRPrim::Null));
        p.types.push(Ty::Prim(TIRPrim::I32));
        p.types.push(Ty::Prim(TIRPrim::Bool));
        Suite { p, locals: Vec::new(), line: 0 }
    }

    fn ty(&mut self, ty: Ty) -> TyId {
        if let Some(i) = self.p.types.iter().position(|held| *held == ty) {
            return i;
        }
        self.p.types.push(ty);
        self.p.types.len() - 1
    }

    fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    // A struct that moves, and one that copies.
    fn strukt(&mut self, name: &str) -> TyId {
        let item = self.item(TTIRItemKind::Struct {
            vis: TIRVis::Pub, attrs: TIRAttrs::default(), name: name.to_string(),
            generics: Vec::new(), fields: Vec::new(),
        });
        self.ty(Ty::Named { item, args: Vec::new(), regions: Vec::new() })
    }

    fn trait_named(&mut self, name: &str) -> TTIRItemId {
        self.item(TTIRItemKind::Trait {
            vis: TIRVis::Pub, attrs: TIRAttrs::default(), name: name.to_string(),
            generics: Vec::new(), wheres: Vec::new(), members: Vec::new(),
        })
    }

    // `impl Copy for T` / `impl Drop for T`.
    fn impl_for(&mut self, trait_name: &str, ty: TyId) {
        let of = self.trait_named(trait_name);
        self.item(TTIRItemKind::Impl {
            vis: TIRVis::Pub, attrs: TIRAttrs::default(), generics: Vec::new(),
            wheres: Vec::new(), ty, of: Some(of), members: Vec::new(),
        });
    }

    // A method taking its receiver the way the word says.
    fn method(&mut self, name: &str, mode: TIRSelf) -> TTIRItemId {
        let ty = self.ty(Ty::Fn { params: Vec::new(), ret: Self::NULL, is_unsafe: false });
        self.item(TTIRItemKind::Fn(TTIRFn {
            vis: TIRVis::Pub,
            attrs: TIRFnAttrs {
                common: TIRAttrs::default(), symbol: None, must_use: false,
                inline: TIRInline::Unwritten, is_test: false,
            },
            is_const: false, is_unsafe: false, name: name.to_string(),
            symbol: String::new(), generics: Vec::new(), wheres: Vec::new(),
            ty,
            params: vec![TTIRParam { name: TIRBinding::SelfRecv(mode, None), slot: None }],
            ret: Self::NULL, outlives: Vec::new(), body: None,
        }))
    }

    fn expr(&mut self, kind: TTIRExprKind, ty: TyId) -> TTIRExprId {
        self.line += 1;
        let line = self.line;
        self.p.exprs.push(TTIRExpr { kind, ty, line, col: 1 });
        self.p.exprs.len() - 1
    }

    fn slot(&mut self, name: &str, ty: TyId, intro: TIRIntro) -> TTIRLocalId {
        self.locals.push(TTIRLocal {
            name: TIRBinding::Name(name.to_string()), ty, intro, line: 1, col: 1,
        });
        self.locals.len() - 1
    }

    fn local(&mut self, id: TTIRLocalId) -> TTIRExprId {
        let ty = self.locals[id].ty;
        self.expr(TTIRExprKind::Local(id), ty)
    }

    fn int(&mut self, n: i64) -> TTIRExprId {
        self.expr(TTIRExprKind::Literal(TIRLit::Int(n)), Self::I32)
    }

    fn boolean(&mut self) -> TTIRExprId {
        self.expr(TTIRExprKind::Literal(TIRLit::Bool(true)), Self::BOOL)
    }

    // A call of nothing in particular, which is how a value is handed over.
    fn call(&mut self, args: Vec<TTIRExprId>) -> TTIRExprId {
        let callee = self.expr(TTIRExprKind::Literal(TIRLit::Null), Self::NULL);
        self.expr(TTIRExprKind::Call { callee, args }, Self::NULL)
    }

    fn borrow(&mut self, of: TTIRExprId, op: TIRRefOp) -> TTIRExprId {
        let inner = self.p.exprs[of].ty;
        let ty = self.ty(Ty::Ref { op, life: 0, inner });
        self.expr(TTIRExprKind::Unary { op: TIRUnaryOp::Ref(op), operand: of }, ty)
    }

    fn field(&mut self, base: TTIRExprId, index: usize, ty: TyId) -> TTIRExprId {
        self.expr(TTIRExprKind::Field { base, index }, ty)
    }

    // A body of its own begins: the slots declared from here are the inner
    // body's, and the outer body's are put aside until `shut`.
    fn open(&mut self) -> Vec<TTIRLocal> {
        std::mem::take(&mut self.locals)
    }

    // ...and ends, taking the slots declared since as its own.
    fn shut(
        &mut self,
        outer: Vec<TTIRLocal>,
        value: TTIRExprId,
        captures: Vec<(TTIRLocalId, TTIRCaptureMode)>,
    ) -> TTIRExprId {
        let locals = std::mem::replace(&mut self.locals, outer);
        self.p.bodies.push(TTIRBody { locals, value });
        let body = self.p.bodies.len() - 1;
        let line = self.line + 1;
        let held = captures
            .into_iter()
            .map(|(outer, mode)| TTIRCapture { outer, slot: 0, mode, line, col: 1 })
            .collect();
        self.expr(TTIRExprKind::Closure { captures: held, body }, Self::NULL)
    }

    // A closure over a body with nothing in it, capturing what it is told to.
    fn closure(&mut self, captures: Vec<(TTIRLocalId, TTIRCaptureMode)>) -> TTIRExprId {
        let outer = self.open();
        let empty = self.expr(TTIRExprKind::Literal(TIRLit::Null), Self::NULL);
        self.shut(outer, empty, captures)
    }

    fn block(&mut self, stmts: Vec<TTIRStmt>, tail: Option<TTIRExprId>) -> TTIRExprId {
        self.expr(TTIRExprKind::Block { stmts, tail }, Self::NULL)
    }

    fn eval(&mut self, expr: TTIRExprId) -> TTIRStmt {
        TTIRStmt::Expr { is_unsafe: false, expr }
    }

    // The body becomes a fn, since a fn is what `check` walks.
    fn func(&mut self, value: TTIRExprId) -> TTIRItemId {
        let locals = std::mem::take(&mut self.locals);
        self.p.bodies.push(TTIRBody { locals, value });
        let body = self.p.bodies.len() - 1;
        let ty = self.ty(Ty::Fn { params: Vec::new(), ret: Self::NULL, is_unsafe: false });
        let id = self.item(TTIRItemKind::Fn(TTIRFn {
            vis: TIRVis::Pub,
            attrs: TIRFnAttrs {
                common: TIRAttrs::default(), symbol: None, must_use: false,
                inline: TIRInline::Unwritten, is_test: false,
            },
            is_const: false, is_unsafe: false, name: "go".to_string(),
            symbol: String::new(), generics: Vec::new(), wheres: Vec::new(),
            ty, params: Vec::new(), ret: Self::NULL, outlives: Vec::new(),
            body: Some(body),
        }));
        self.p.modules = vec![TTIRModule { path: Vec::new(), roots: vec![id] }];
        id
    }

    // Everything the checker said, rendered against a source of blank numbered
    // lines: only the messages and the places matter here.
    fn errors(&mut self, value: TTIRExprId) -> String {
        self.func(value);
        let mut c = Checker::new(&self.p);
        c.check();
        let text: Vec<char> = (0..=self.line + 2)
            .map(|_| "-\n".to_string())
            .collect::<String>()
            .chars()
            .collect();
        c.errors().render(&Source::new("t.fc", &text))
    }
}

// ---- Moves ----------------------------------------------------------------

// "What `let b = a` does to a is move it... reading a after that is refused
// where it is written" (section 2).
#[test]
fn a_value_handed_over_is_gone_from_where_it_was() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let read = s.local(a);
    let again = s.call(vec![read]);
    let stmts = vec![s.eval(hand), s.eval(again)];
    let body = s.block(stmts, None);

    let out = s.errors(body);
    assert!(out.contains("error: `a` has been moved"), "{}", out);
    assert!(out.contains("this passes it"), "{}", out);
    assert!(out.contains("note: it was moved"), "{}", out);
    assert_eq!(out.matches("error:").count(), 1, "{}", out);
}

// "The primitives copy without asking" -- so the same shape with an i32 is
// nothing at all.
#[test]
fn a_value_that_copies_is_still_there() {
    let mut s = Suite::new();
    let n = s.slot("n", Suite::I32, TIRIntro::Let);
    let one = s.local(n);
    let hand = s.call(vec![one]);
    let two = s.local(n);
    let again = s.call(vec![two]);
    let stmts = vec![s.eval(hand), s.eval(again)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// "Copying is what a type asks for, and it asks with `impl Copy for Point {}`".
#[test]
fn a_type_may_ask_to_be_copied() {
    let mut s = Suite::new();
    let point = s.strukt("Point");
    s.impl_for("Copy", point);
    let a = s.slot("a", point, TIRIntro::Let);
    let one = s.local(a);
    let hand = s.call(vec![one]);
    let two = s.local(a);
    let again = s.call(vec![two]);
    let stmts = vec![s.eval(hand), s.eval(again)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// A moved-from slot may be filled again, and is whole once it is.
#[test]
fn a_slot_filled_again_is_whole_again() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Var);

    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let place = s.local(a);
    let fresh = s.call(Vec::new());
    let refill = s.expr(
        TTIRExprKind::Assign { op: TIRAssignOp::Set, place, value: fresh },
        Suite::NULL,
    );
    let read = s.local(a);
    let again = s.call(vec![read]);
    let stmts = vec![s.eval(hand), s.eval(refill), s.eval(again)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// Moved on one way and not the other: neither gone nor whole, and the message
// says which.
#[test]
fn a_move_on_one_way_only_is_a_maybe() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let cond = s.boolean();
    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let then = s.block(vec![], Some(hand));
    let iff = s.expr(TTIRExprKind::If { cond, then, els: None }, Suite::NULL);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(iff), s.eval(after)];
    let body = s.block(stmts, None);

    let out = s.errors(body);
    assert!(out.contains("error: `a` may have been moved"), "{}", out);
    assert!(out.contains("it is moved on one way here"), "{}", out);
}

// Moved on both ways is moved.
#[test]
fn a_move_on_every_way_is_a_move() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let cond = s.boolean();
    let one = s.local(a);
    let hand = s.call(vec![one]);
    let then = s.block(vec![], Some(hand));
    let two = s.local(a);
    let other = s.call(vec![two]);
    let els = s.block(vec![], Some(other));
    let iff = s.expr(TTIRExprKind::If { cond, then, els: Some(els) }, Suite::NULL);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(iff), s.eval(after)];
    let body = s.block(stmts, None);

    let out = s.errors(body);
    assert!(out.contains("error: `a` has been moved"), "{}", out);
    assert!(!out.contains("may have been"), "{}", out);
}

// A loop goes round more than once, so a move in the body is a move at the top
// of the second turn -- and it is said once, not once per turn.
#[test]
fn a_move_in_a_loop_is_a_move_on_the_second_turn() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let cond = s.boolean();
    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let inner = s.block(vec![], Some(hand));
    let looping = s.expr(TTIRExprKind::While { cond, body: inner }, Suite::NULL);
    let body = s.block(vec![], Some(looping));

    let out = s.errors(body);
    assert!(out.contains("has been moved") || out.contains("may have been moved"), "{}", out);
    assert_eq!(out.matches("error:").count(), 1, "{}", out);
}

// `return` does not come back, so what follows it is not reached and says
// nothing about what it would have done.
#[test]
fn nothing_after_a_return_is_walked() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let leaving = s.expr(TTIRExprKind::Return(Some(hand)), Suite::NULL);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(leaving), s.eval(after)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// ---- Aliasing -------------------------------------------------------------

// "`f(&p, *p)` asks for both at once and is refused" (section 3). Nothing here
// is a rule about calls: both borrows are simply in hand at once.
#[test]
fn one_call_may_not_ask_for_both() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);

    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));

    let out = s.errors(body);
    assert!(out.contains("error: `p` is borrowed already"), "{}", out);
    assert!(out.contains("this takes a `*`"), "{}", out);
    assert!(out.contains("a `&` of it is held from"), "{}", out);
}

// "any number of `&` and no `*`" -- so two readers are fine.
#[test]
fn many_readers_may_stand_at_once() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);
    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let two = s.local(p);
    let also = s.borrow(two, TIRRefOp::Imm);
    let hand = s.call(vec![read, also]);
    let body = s.block(vec![], Some(hand));
    assert_eq!(s.errors(body), "");
}

// Two writers are not.
#[test]
fn two_writers_may_not() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);
    let one = s.local(p);
    let write = s.borrow(one, TIRRefOp::Mut);
    let two = s.local(p);
    let also = s.borrow(two, TIRRefOp::Mut);
    let hand = s.call(vec![write, also]);
    let body = s.block(vec![], Some(hand));
    assert!(s.errors(body).contains("is borrowed already"));
}

// A borrow lasts to the end of the block that took it, and no further.
#[test]
fn a_borrow_is_let_go_at_the_end_of_its_block() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);

    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let held = s.call(vec![read]);
    let inner_stmt = s.eval(held);
    let inner = s.block(vec![inner_stmt], None);

    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let after = s.call(vec![write]);
    let stmts = vec![s.eval(inner), s.eval(after)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// "It is a rule about places and not about names": two fields of one struct are
// two places, and holding both is allowed.
#[test]
fn two_fields_are_two_places() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);

    let base = s.local(p);
    let x = s.field(base, 0, Suite::I32);
    let read = s.borrow(x, TIRRefOp::Imm);
    let other = s.local(p);
    let y = s.field(other, 1, Suite::I32);
    let write = s.borrow(y, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));
    assert_eq!(s.errors(body), "");
}

// But a field and the whole are one place: the field is part of the value.
#[test]
fn a_field_and_the_whole_are_one_place() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);

    let base = s.local(p);
    let x = s.field(base, 0, Suite::I32);
    let read = s.borrow(x, TIRRefOp::Imm);
    let whole = s.local(p);
    let write = s.borrow(whole, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));
    assert!(s.errors(body).contains("is borrowed already"));
}

// "`*x` asks that x be a place the writer may write to -- a `var`" (section 5).
#[test]
fn a_star_wants_a_var() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Let);
    let one = s.local(p);
    let write = s.borrow(one, TIRRefOp::Mut);
    let hand = s.call(vec![write]);
    let body = s.block(vec![], Some(hand));

    let out = s.errors(body);
    assert!(out.contains("error: `p` may not be written to"), "{}", out);
    assert!(out.contains("a `*` wants a `var`"), "{}", out);
}

// "`addr x`... what it gives back is a `ptr` and not a reference, so none of
// the above is asked of it": a pointer stands beside a `*` without complaint.
#[test]
fn addr_is_not_a_borrow() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);

    let one = s.local(p);
    let ptr_ty = s.ty(Ty::Ptr(buf));
    let taken = s.expr(
        TTIRExprKind::Unary { op: TIRUnaryOp::Addr, operand: one },
        ptr_ty,
    );
    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let hand = s.call(vec![taken, write]);
    let body = s.block(vec![], Some(hand));
    assert_eq!(s.errors(body), "");
}

// ---- What copies ----------------------------------------------------------

// "An array copies exactly when its element does, so an `i32[8]` copies and a
// `Buf[8]` moves" (section 3).
#[test]
fn an_array_copies_when_its_element_does() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let of_int = s.ty(Ty::Array { elem: Suite::I32, len: 8 });
    let of_buf = s.ty(Ty::Array { elem: buf, len: 8 });
    let tuple_ok = s.ty(Ty::Tuple(vec![Suite::I32, Suite::BOOL]));
    let tuple_no = s.ty(Ty::Tuple(vec![Suite::I32, buf]));
    let a_ref = s.ty(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: buf });

    s.func(Suite::NULL);
    let c = Checker::new(&s.p);
    let is = |ty| c.copies.is_copy(ty, &s.p, &[]);
    assert!(is(Suite::I32));
    assert!(is(of_int));
    assert!(!is(of_buf));
    assert!(is(tuple_ok));
    assert!(!is(tuple_no));
    // "a reference" is in the copy set outright.
    assert!(is(a_ref));
    assert!(!is(buf));
}

// A parameter copies where it was declared to, and the bound is the only thing
// that can say so.
#[test]
fn a_parameter_copies_where_it_is_bounded_to() {
    let mut s = Suite::new();
    let copy = s.trait_named("Copy");
    let copy_ty = s.ty(Ty::Named { item: copy, args: Vec::new(), regions: Vec::new() });
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 0 });
    s.func(Suite::NULL);

    let c = Checker::new(&s.p);
    let bounded = [TTIRGeneric::Type {
        name: "T".to_string(),
        bounds: vec![TTIRBound::Trait(copy_ty)],
    }];
    let bare = [TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }];
    assert!(c.copies.is_copy(t, &s.p, &bounded));
    assert!(!c.copies.is_copy(t, &s.p, &bare));
    // And with no list at all, which is what a non-generic fn has.
    assert!(!c.copies.is_copy(t, &s.p, &[]));
}

// "A type cannot have both a `Copy` and a `Drop`: a value that has something to
// release is a value there had better be one of" (section 2).
#[test]
fn a_type_may_not_be_both_copy_and_drop() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    s.impl_for("Copy", buf);
    s.impl_for("Drop", buf);
    let body = s.block(vec![], None);

    let out = s.errors(body);
    assert!(out.contains("error: `Buf` is both `Copy` and `Drop`"), "{}", out);
}

// ---- The rest of the move sites -------------------------------------------

// "a field of a literal being built" is the fourth of the four places a value
// is handed over (section 2).
#[test]
fn a_field_of_a_literal_takes_the_value() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let held = s.strukt("Held");
    let a = s.slot("a", buf, TIRIntro::Let);

    let moved = s.local(a);
    let item = match &s.p.types[held] {
        Ty::Named { item, .. } => *item,
        other => panic!("{:?}", other),
    };
    let lit = s.expr(TTIRExprKind::StructLit { item, fields: vec![moved] }, held);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(lit), s.eval(after)];
    let body = s.block(stmts, None);
    assert!(s.errors(body).contains("error: `a` has been moved"));
}

// "A bare `self` takes the value whole and so moves it" (section 3).
#[test]
fn a_self_by_value_receiver_moves_it() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let method = s.method("take", TIRSelf::Value);
    let p = s.slot("p", buf, TIRIntro::Let);

    let recv = s.local(p);
    let call = s.expr(
        TTIRExprKind::Method { recv, item: method, args: Vec::new() },
        Suite::NULL,
    );
    let read = s.local(p);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(call), s.eval(after)];
    let body = s.block(stmts, None);
    assert!(s.errors(body).contains("error: `p` has been moved"));
}

// "A `*self` receiver holds a mutable reference to the whole value for the
// length of the call, so nothing reads that value while the method runs."
#[test]
fn a_star_self_receiver_holds_the_whole_value() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let method = s.method("set", TIRSelf::Mut);
    let p = s.slot("p", buf, TIRIntro::Var);

    let recv = s.local(p);
    let arg = s.local(p);
    let also = s.borrow(arg, TIRRefOp::Imm);
    let call = s.expr(
        TTIRExprKind::Method { recv, item: method, args: vec![also] },
        Suite::NULL,
    );
    let body = s.block(vec![], Some(call));

    let out = s.errors(body);
    assert!(out.contains("error: `p` is borrowed already"), "{}", out);
    // And it is let go when the call is over: a second one is fine.
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let method = s.method("set", TIRSelf::Mut);
    let p = s.slot("p", buf, TIRIntro::Var);
    let one = s.local(p);
    let first = s.expr(
        TTIRExprKind::Method { recv: one, item: method, args: Vec::new() },
        Suite::NULL,
    );
    let two = s.local(p);
    let second = s.expr(
        TTIRExprKind::Method { recv: two, item: method, args: Vec::new() },
        Suite::NULL,
    );
    let stmts = vec![s.eval(first), s.eval(second)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// A `break` carries what is gone out of the loop with it.
#[test]
fn a_break_carries_the_state_out_with_it() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);

    let cond = s.boolean();
    let moved = s.local(a);
    let hand = s.call(vec![moved]);
    let leaving = s.expr(TTIRExprKind::Break(None), Suite::NULL);
    let inner_stmts = vec![s.eval(hand), s.eval(leaving)];
    let inner = s.block(inner_stmts, None);
    let looping = s.expr(TTIRExprKind::While { cond, body: inner }, Suite::NULL);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(looping), s.eval(after)];
    let body = s.block(stmts, None);

    let out = s.errors(body);
    assert!(out.contains("`a`") && out.contains("moved"), "{}", out);
}

// The index is not kept, so `a[i]` and `a[j]` are one place. That is the half
// of section 3's open question that turns more down, and it is a choice.
#[test]
fn two_elements_of_one_array_are_one_place() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let of_buf = s.ty(Ty::Array { elem: buf, len: 8 });
    let a = s.slot("a", of_buf, TIRIntro::Var);

    let base = s.local(a);
    let i = s.int(0);
    let one = s.expr(TTIRExprKind::Index { base, index: i }, buf);
    let read = s.borrow(one, TIRRefOp::Imm);
    let other = s.local(a);
    let j = s.int(1);
    let two = s.expr(TTIRExprKind::Index { base: other, index: j }, buf);
    let write = s.borrow(two, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));
    assert!(s.errors(body).contains("is borrowed already"));
}

// Nothing writes a deref -- "a reference stands for the place it refers to and
// is read, called, indexed and reached into exactly as that place is" -- so the
// step is put in from the type of the base. Two fields reached *through* a
// reference are still two places.
#[test]
fn reaching_through_a_reference_is_a_step_of_its_own() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let to_buf = s.ty(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: buf });
    let r = s.slot("r", to_buf, TIRIntro::Let);

    // `r.x` and `r.y`: through the reference, and two places once there.
    let base = s.local(r);
    let x = s.field(base, 0, Suite::I32);
    let read = s.borrow(x, TIRRefOp::Imm);
    let other = s.local(r);
    let y = s.field(other, 1, Suite::I32);
    let write = s.borrow(y, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));
    // A `let` of `*` type writes through what it refers to, so the `*` is
    // allowed -- and the two fields do not meet.
    assert_eq!(s.errors(body), "");

    // The same two through the reference, one of them the whole of it.
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let to_buf = s.ty(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: buf });
    let r = s.slot("r", to_buf, TIRIntro::Let);
    let base = s.local(r);
    let x = s.field(base, 0, Suite::I32);
    let read = s.borrow(x, TIRRefOp::Imm);
    let whole = s.local(r);
    let write = s.borrow(whole, TIRRefOp::Mut);
    let hand = s.call(vec![read, write]);
    let body = s.block(vec![], Some(hand));
    assert!(s.errors(body).contains("is borrowed already"));
}

// "a local at the end of its block, a temporary at the end of its statement"
// (section 2). A reference bound to nothing goes with the statement, which is
// what lets these two stand one after the other.
#[test]
fn a_temporary_borrow_ends_with_its_statement() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);
    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let first = s.call(vec![read]);
    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let second = s.call(vec![write]);
    let stmts = vec![s.eval(first), s.eval(second)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// What a `let`'s initialiser borrowed may have reached the slot, so the borrow
// keeps the slot's extent -- which ends where the slot is last read.
#[test]
fn a_borrow_bound_to_a_name_lasts_as_long_as_the_name_is_read() {
    // Read after the `*` is taken, so the two are in hand at once.
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);
    let to_buf = s.ty(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: buf });
    let r = s.slot("r", to_buf, TIRIntro::Let);

    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let bound = TTIRStmt::Let { is_unsafe: false, local: r, init: Some(read) };
    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let after = s.call(vec![write]);
    let held = s.local(r);
    let later = s.call(vec![held]);
    let stmts = vec![bound, s.eval(after), s.eval(later)];
    let body = s.block(stmts, None);
    assert!(s.errors(body).contains("is borrowed already"), "{}", s.errors(body));
}

// And read nowhere after, the borrow is done with before the `*` is taken --
// which is the sharpening, and what the block-long extent used to turn down.
#[test]
fn a_borrow_nothing_reads_again_is_done_with() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let p = s.slot("p", buf, TIRIntro::Var);
    let to_buf = s.ty(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: buf });
    let r = s.slot("r", to_buf, TIRIntro::Let);

    let one = s.local(p);
    let read = s.borrow(one, TIRRefOp::Imm);
    let bound = TTIRStmt::Let { is_unsafe: false, local: r, init: Some(read) };
    let two = s.local(p);
    let write = s.borrow(two, TIRRefOp::Mut);
    let after = s.call(vec![write]);
    let stmts = vec![bound, s.eval(after)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// "A value that moves has one owner at a time" -- and what a reference refers
// to is owned where it was borrowed from, not here.
#[test]
fn a_value_behind_a_reference_is_not_ours_to_give_away() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let to_buf = s.ty(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: buf });
    let r = s.slot("r", to_buf, TIRIntro::Let);

    let base = s.local(r);
    let x = s.field(base, 0, buf);
    let hand = s.call(vec![x]);
    let body = s.block(vec![], Some(hand));

    let out = s.errors(body);
    assert!(out.contains("cannot be moved out of a reference"), "{}", out);
    assert!(out.contains("`&` it instead"), "{}", out);
}

// An element that went would leave the array it was in with a hole in it.
#[test]
fn an_element_is_not_ours_to_give_away_either() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let of_buf = s.ty(Ty::Array { elem: buf, len: 8 });
    let v = s.slot("v", of_buf, TIRIntro::Var);

    let base = s.local(v);
    let i = s.int(0);
    let one = s.expr(TTIRExprKind::Index { base, index: i }, buf);
    let hand = s.call(vec![one]);
    let body = s.block(vec![], Some(hand));
    assert!(s.errors(body).contains("cannot be moved out of an array"));

    // An element that copies is another matter: nothing is left with a hole.
    let mut s = Suite::new();
    let of_int = s.ty(Ty::Array { elem: Suite::I32, len: 8 });
    let v = s.slot("v", of_int, TIRIntro::Var);
    let base = s.local(v);
    let i = s.int(0);
    let one = s.expr(TTIRExprKind::Index { base, index: i }, Suite::I32);
    let hand = s.call(vec![one]);
    let body = s.block(vec![], Some(hand));
    assert_eq!(s.errors(body), "");
}

// ---- Closures -------------------------------------------------------------

// "A name the body uses but did not declare is captured, and how is worked out
// per name, each taking the least the body asks of it. Reading one takes a `&`
// of it and assigning to one takes a `*`" (section 5). The example the prose
// gives, in three closures over one name.
#[test]
fn a_capture_takes_the_least_the_body_asks() {
    // `let show = || print(n)` takes a `&`, and a second reader may stand
    // beside it.
    let mut s = Suite::new();
    let n = s.slot("n", Suite::I32, TIRIntro::Var);
    let read_once = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Imm))]);
    let read_twice = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Imm))]);
    let hand = s.call(vec![read_once, read_twice]);
    let body = s.block(vec![], Some(hand));
    assert_eq!(s.errors(body), "");

    // `let bump = || n = n + 1` takes a `*`, and "one that writes to it may
    // share it with nothing".
    let mut s = Suite::new();
    let n = s.slot("n", Suite::I32, TIRIntro::Var);
    let writes = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Mut))]);
    let reads = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Imm))]);
    let hand = s.call(vec![writes, reads]);
    let body = s.block(vec![], Some(hand));

    let out = s.errors(body);
    assert!(out.contains("error: `n` is borrowed already"), "{}", out);
    // A reader who did not write a `&` is told one is there.
    assert!(out.contains("the closure captures it by `&`"), "{}", out);
}

// "a `move` closure captures every name by value instead... By value is a copy
// where the name's type copies and a move where it does not" (section 5).
#[test]
fn a_move_capture_takes_the_value() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let a = s.slot("a", buf, TIRIntro::Let);
    let owns = s.closure(vec![(a, TTIRCaptureMode::Value)]);
    let first = s.call(vec![owns]);
    let read = s.local(a);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(first), s.eval(after)];
    let body = s.block(stmts, None);
    assert!(s.errors(body).contains("error: `a` has been moved"));

    // And where the name's type copies, it is a copy and the name stays.
    let mut s = Suite::new();
    let n = s.slot("n", Suite::I32, TIRIntro::Let);
    let owns = s.closure(vec![(n, TTIRCaptureMode::Value)]);
    let first = s.call(vec![owns]);
    let read = s.local(n);
    let after = s.call(vec![read]);
    let stmts = vec![s.eval(first), s.eval(after)];
    let body = s.block(stmts, None);
    assert_eq!(s.errors(body), "");
}

// A capture is a borrow of a name outside the closure, so it answers to what
// that name allows: a `*` capture of a `let` is a `*` of a `let`.
#[test]
fn a_star_capture_of_a_let_is_refused() {
    let mut s = Suite::new();
    let n = s.slot("n", Suite::I32, TIRIntro::Let);
    let writes = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Mut))]);
    let reads = s.closure(vec![(n, TTIRCaptureMode::Ref(TIRRefOp::Imm))]);
    let hand = s.call(vec![writes, reads]);
    let body = s.block(vec![], Some(hand));
    // The two closures conflict, which is what this asserts; whether a `*`
    // capture of a `let` is refused on its own is `sema`'s to decide when it
    // works the mode out, since the mode is what it would refuse.
    assert!(s.errors(body).contains("is borrowed already"));
}

// A closure's body is walked on its own: its slots are its own, and what it
// captured arrives whole however the name outside it stood.
#[test]
fn a_closures_body_is_checked_by_itself() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    // The closure's own body, with its own slot, moved twice.
    let held = s.open();
    let inner_slot = s.slot("held", buf, TIRIntro::Let);
    let one = s.local(inner_slot);
    let first = s.call(vec![one]);
    let two = s.local(inner_slot);
    let second = s.call(vec![two]);
    let stmts = vec![s.eval(first), s.eval(second)];
    let inner_body = s.block(stmts, None);
    let closure = s.shut(held, inner_body, Vec::new());

    let outer = s.call(vec![closure]);
    let body = s.block(vec![], Some(outer));
    let out = s.errors(body);
    assert!(out.contains("error: `held` has been moved"), "{}", out);
}
