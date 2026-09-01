// A TTIR built by hand, for the tests of the pass that reads one.
//
// `sema` builds a TTIR from a TIR, and going through it would put that pass
// under test as well -- so the tests of `gir::lower` make theirs here. What it builds is deliberately thin: every expression is typed
// because the TTIR says it must be, and nothing here cares which type, so most
// of them are `null`.

use crate::tir::tir_nodes::{
    TIRAttrs, TIRBinOp, TIRBinding, TIRFnAttrs, TIRInline, TIRIntro, TIRLit, TIRPrim, TIRVis,
};
use crate::tir::ttir_nodes::*;

pub struct Fixture {
    pub p:    TTIRProgram,
    pub null: TyId,
    pub bool: TyId,
    pub int:  TyId,
    locals:   Vec<TTIRLocal>,
}

impl Fixture {
    pub fn new() -> Fixture {
        let mut p = TTIRProgram::default();
        p.types.push(Ty::Prim(TIRPrim::Null));
        p.types.push(Ty::Prim(TIRPrim::Bool));
        p.types.push(Ty::Prim(TIRPrim::I32));
        Fixture { p, null: 0, bool: 1, int: 2, locals: Vec::new() }
    }

    pub fn expr(&mut self, kind: TTIRExprKind, ty: TyId) -> TTIRExprId {
        self.p.exprs.push(TTIRExpr { kind, ty, line: 1, col: 1 });
        self.p.exprs.len() - 1
    }

    pub fn int(&mut self, n: i64) -> TTIRExprId {
        let ty = self.int;
        self.expr(TTIRExprKind::Literal(TIRLit::Int(n)), ty)
    }

    pub fn boolean(&mut self, b: bool) -> TTIRExprId {
        let ty = self.bool;
        self.expr(TTIRExprKind::Literal(TIRLit::Bool(b)), ty)
    }

    // A slot of the body being built.
    pub fn slot(&mut self, name: &str, ty: TyId) -> TTIRLocalId {
        self.locals.push(TTIRLocal {
            name:  TIRBinding::Name(name.to_string()),
            ty,
            intro: TIRIntro::Let,
            line:  1,
            col:   1,
        });
        self.locals.len() - 1
    }

    pub fn local(&mut self, id: TTIRLocalId) -> TTIRExprId {
        let ty = self.locals[id].ty;
        self.expr(TTIRExprKind::Local(id), ty)
    }

    // A call to nothing in particular, for a statement that has an effect.
    pub fn call(&mut self) -> TTIRExprId {
        let ty = self.null;
        let callee = self.expr(TTIRExprKind::Item(0), ty);
        self.expr(TTIRExprKind::Call { callee, args: Vec::new() }, ty)
    }

    pub fn block(&mut self, stmts: Vec<TTIRStmt>, tail: Option<TTIRExprId>) -> TTIRExprId {
        let ty = match tail {
            Some(t) => self.p.exprs[t].ty,
            None => self.null,
        };
        self.expr(TTIRExprKind::Block { stmts, tail }, ty)
    }

    pub fn and(&mut self, lhs: TTIRExprId, rhs: TTIRExprId) -> TTIRExprId {
        let ty = self.bool;
        self.expr(TTIRExprKind::Binary { op: TIRBinOp::And, lhs, rhs }, ty)
    }

    pub fn or(&mut self, lhs: TTIRExprId, rhs: TTIRExprId) -> TTIRExprId {
        let ty = self.bool;
        self.expr(TTIRExprKind::Binary { op: TIRBinOp::Or, lhs, rhs }, ty)
    }

    pub fn add(&mut self, lhs: TTIRExprId, rhs: TTIRExprId) -> TTIRExprId {
        let ty = self.int;
        self.expr(TTIRExprKind::Binary { op: TIRBinOp::Add, lhs, rhs }, ty)
    }

    pub fn if_(&mut self, cond: TTIRExprId, then: TTIRExprId, els: Option<TTIRExprId>)
        -> TTIRExprId {
        let ty = self.p.exprs[then].ty;
        self.expr(TTIRExprKind::If { cond, then, els }, ty)
    }

    pub fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    // A type with something to release: a struct, the trait the compiler knows
    // by name, and the impl that ties them together.
    pub fn dropper(&mut self, name: &str) -> TyId {
        let held = self.item(TTIRItemKind::Struct {
            vis:      TIRVis::Pub,
            attrs:    TIRAttrs::default(),
            name:     name.to_string(),
            generics: Vec::new(),
            fields:   Vec::new(),
        });
        let ty = self.ty(Ty::Named { item: held, args: Vec::new(), regions: Vec::new() });
        let of = self.item(TTIRItemKind::Trait {
            vis:      TIRVis::Pub,
            attrs:    TIRAttrs::default(),
            name:     "Drop".to_string(),
            generics: Vec::new(),
            wheres:   Vec::new(),
            members:  Vec::new(),
        });
        self.item(TTIRItemKind::Impl {
            vis:      TIRVis::Unwritten,
            attrs:    TIRAttrs::default(),
            generics: Vec::new(),
            wheres:   Vec::new(),
            ty,
            of:       Some(of),
            members:  Vec::new(),
        });
        ty
    }

    pub fn ty(&mut self, ty: Ty) -> TyId {
        match self.p.types.iter().position(|held| *held == ty) {
            Some(at) => at,
            None => {
                self.p.types.push(ty);
                self.p.types.len() - 1
            }
        }
    }

    pub fn let_(&self, local: TTIRLocalId, init: Option<TTIRExprId>) -> TTIRStmt {
        TTIRStmt::Let { is_unsafe: false, local, init }
    }

    pub fn eval(&self, expr: TTIRExprId) -> TTIRStmt {
        TTIRStmt::Expr { is_unsafe: false, expr }
    }

    // A call that hands something over, for a statement that moves.
    pub fn hands(&mut self, arg: TTIRExprId) -> TTIRExprId {
        let ty = self.null;
        let callee = self.expr(TTIRExprKind::Item(0), ty);
        self.expr(TTIRExprKind::Call { callee, args: vec![arg] }, ty)
    }

    // The fn a body belongs to, so a pass over the graph knows which slots the
    // parameters went in.
    pub fn owns(&mut self, body: TTIRBodyId, params: Vec<TTIRLocalId>) -> TTIRItemId {
        let ty = self.null;
        self.item(TTIRItemKind::Fn(TTIRFn {
            vis:       TIRVis::Pub,
            attrs:     TIRFnAttrs {
                common:   TIRAttrs::default(),
                symbol:   None,
                must_use: false,
                inline:   TIRInline::Unwritten,
                is_test:  false,
            },
            is_const:  false,
            is_unsafe: false,
            name:      "f".to_string(),
            symbol:    String::new(),
            generics:  Vec::new(),
            wheres:    Vec::new(),
            ty,
            params:    params
                .into_iter()
                .map(|slot| TTIRParam {
                    name: TIRBinding::Name("p".to_string()),
                    slot: Some(slot),
                })
                .collect(),
            ret:       ty,
            outlives:  Vec::new(),
            body:      Some(body),
        }))
    }

    // The same, for the `drop` of the `impl Drop` written for `ty` -- which
    // `dropper` made and left with no members. A release *is* this body, so it
    // is the one body in a program whose receiver gets no release of its own,
    // and that rule cannot be tested without a way to write one.
    pub fn releasing(&mut self, ty: TyId, body: TTIRBodyId, params: Vec<TTIRLocalId>) {
        let held = self.owns(body, params);
        if let TTIRItemKind::Fn(f) = &mut self.p.items[held].kind {
            f.name = "drop".to_string();
        }
        for item in &mut self.p.items {
            if let TTIRItemKind::Impl { ty: of, members, .. } = &mut item.kind {
                if *of == ty {
                    members.push(held);
                }
            }
        }
    }

    // Closes the body being built and hands back its handle.
    pub fn body(&mut self, value: TTIRExprId) -> TTIRBodyId {
        let locals = std::mem::take(&mut self.locals);
        self.p.bodies.push(TTIRBody { locals, value });
        self.p.bodies.len() - 1
    }
}
