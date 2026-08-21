// A TTIR built by hand, for the tests of the pass that reads one.
//
// `sema` is what would build a TTIR from a TIR, and it is not written -- so
// there is no way to get one from source, and the tests of `cfg::lower` make
// theirs here. What it builds is deliberately thin: every expression is typed
// because the TTIR says it must be, and nothing here cares which type, so most
// of them are `null`.

use crate::tir::tir_nodes::{TIRBinOp, TIRBinding, TIRIntro, TIRLit, TIRPrim};
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

    // Closes the body being built and hands back its handle.
    pub fn body(&mut self, value: TTIRExprId) -> TTIRBodyId {
        let locals = std::mem::take(&mut self.locals);
        self.p.bodies.push(TTIRBody { locals, value });
        self.p.bodies.len() - 1
    }
}
