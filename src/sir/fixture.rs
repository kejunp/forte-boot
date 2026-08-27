// A GIR built by hand, for the tests of the pass that reads one.
//
// `gir::lower` builds a GIR from a TTIR, and going through it would put that
// pass under test as well -- the same reason `gir::fixture` exists one level
// up. It also would not reach: the shapes worth testing here are a diamond, a
// loop and a block nothing enters, and writing those as source and hoping the
// lowering makes them is a test of the hope.
//
// What it builds is deliberately thin. Every expression is typed because the
// GIR says it must be and nothing here cares which type, so most of them are
// `null`; every block is written by hand, terminator and all.

use crate::gir::gir_nodes::*;
use crate::tir::tir_nodes::{TIRAssignOp, TIRAttrs, TIRBinOp, TIRBinding, TIRFnAttrs, TIRInline,
                            TIRIntro, TIRLit, TIRPrim, TIRVis};
use crate::tir::ttir_nodes::*;

use super::lower::Lowerer;
use super::opt::{optimize, Stats};
use super::promote::promote;
use super::sir_nodes::*;
use super::verify::{verify, verify_order};

pub struct Fixture {
    pub ttir: TTIRProgram,
    pub gir:  GIRProgram,
    pub null: TyId,
    pub bool: TyId,
    pub int:  TyId,
    blocks:   Vec<GIRBlock>,
    locals:   Vec<GIRLocal>,
    params:   Vec<GIRLocalId>,
    // The declaration `call` and `hands` name. Made the first time one of them
    // is wanted and never again, so that every stand-in call in a fixture is a
    // call to the same nothing in particular.
    sink:     Option<TTIRItemId>,
}

impl Fixture {
    pub fn new() -> Fixture {
        let mut ttir = TTIRProgram::default();
        ttir.types.push(Ty::Prim(TIRPrim::Null));
        ttir.types.push(Ty::Prim(TIRPrim::Bool));
        ttir.types.push(Ty::Prim(TIRPrim::I32));
        // The one a cursor is counted in, so that `sir::lower` finds it rather
        // than falling back to the first entry.
        ttir.types.push(Ty::Prim(TIRPrim::I64));
        Fixture {
            ttir,
            gir: GIRProgram::default(),
            null: 0,
            bool: 1,
            int: 2,
            blocks: Vec::new(),
            locals: Vec::new(),
            params: Vec::new(),
            sink: None,
        }
    }

    // ---- Slots ------------------------------------------------------------

    pub fn local(&mut self, name: &str, ty: TyId) -> GIRLocalId {
        self.push_local(name, ty, false)
    }

    // One with something to release, which is what a `Drop` needs to name.
    pub fn dropping(&mut self, name: &str, ty: TyId) -> GIRLocalId {
        self.push_local(name, ty, true)
    }

    pub fn param(&mut self, name: &str, ty: TyId) -> GIRLocalId {
        let id = self.push_local(name, ty, false);
        self.params.push(id);
        id
    }

    fn push_local(&mut self, name: &str, ty: TyId, drops: bool) -> GIRLocalId {
        self.locals.push(GIRLocal {
            name: TIRBinding::Name(name.to_string()),
            ty,
            intro: TIRIntro::Var,
            synthetic: false,
            drops,
        });
        self.locals.len() - 1
    }

    // ---- Blocks -----------------------------------------------------------

    // Empty, and ending nowhere until something says where. A block left this
    // way is a block nothing leaves, which is a shape worth being able to
    // build.
    pub fn block(&mut self) -> GIRBlockId {
        self.blocks.push(GIRBlock {
            stmts: Vec::new(),
            term:  GIRTerm::Unreachable,
            line:  1,
            col:   1,
        });
        self.blocks.len() - 1
    }

    pub fn term(&mut self, at: GIRBlockId, term: GIRTerm) {
        self.blocks[at].term = term;
    }

    fn stmt(&mut self, at: GIRBlockId, kind: GIRStmtKind) {
        self.blocks[at].stmts.push(GIRStmt { kind, is_unsafe: false, line: 1, col: 1 });
    }

    pub fn set(&mut self, at: GIRBlockId, local: GIRLocalId, value: GIRExprId) {
        self.stmt(at, GIRStmtKind::Set { local, value });
    }

    pub fn store(&mut self, at: GIRBlockId, place: GIRExprId, op: TIRAssignOp, value: GIRExprId) {
        self.stmt(at, GIRStmtKind::Store { place, op, value });
    }

    pub fn eval(&mut self, at: GIRBlockId, expr: GIRExprId) {
        self.stmt(at, GIRStmtKind::Eval(expr));
    }

    pub fn release(&mut self, at: GIRBlockId, local: GIRLocalId) {
        self.stmt(at, GIRStmtKind::Drop { local });
    }

    // ---- Expressions --------------------------------------------------------

    pub fn expr(&mut self, kind: GIRExprKind, ty: TyId) -> GIRExprId {
        self.gir.exprs.push(GIRExpr { kind, ty, line: 1, col: 1 });
        self.gir.exprs.len() - 1
    }

    pub fn int(&mut self, n: i64) -> GIRExprId {
        let ty = self.int;
        self.expr(GIRExprKind::Literal(TIRLit::Int(n)), ty)
    }

    pub fn boolean(&mut self, b: bool) -> GIRExprId {
        let ty = self.bool;
        self.expr(GIRExprKind::Literal(TIRLit::Bool(b)), ty)
    }

    pub fn read(&mut self, local: GIRLocalId) -> GIRExprId {
        let ty = self.locals[local].ty;
        self.expr(GIRExprKind::Local(local), ty)
    }

    pub fn add(&mut self, lhs: GIRExprId, rhs: GIRExprId) -> GIRExprId {
        let ty = self.int;
        self.expr(GIRExprKind::Binary { op: TIRBinOp::Add, lhs, rhs }, ty)
    }

    // `&x`, which is what makes a slot one no value can stand in.
    pub fn addr_of(&mut self, of: GIRExprId) -> GIRExprId {
        let ty = self.null;
        let op = crate::tir::tir_nodes::TIRUnaryOp::Addr;
        self.expr(GIRExprKind::Unary { op, operand: of }, ty)
    }

    // A call to nothing in particular, for a statement with an effect.
    pub fn call(&mut self) -> GIRExprId {
        self.calls_sink(Vec::new())
    }

    // Handing a value somewhere, so that a use of it can be seen.
    pub fn hands(&mut self, arg: GIRExprId) -> GIRExprId {
        self.calls_sink(vec![arg])
    }

    // Both of the above. What they name is a declaration with no body, which
    // is what makes them stay calls: `sir::opt` writes a call out where it can
    // find the body, and a signature is the one kind of fn that has none.
    fn calls_sink(&mut self, args: Vec<GIRExprId>) -> GIRExprId {
        let ty = self.null;
        let item = match self.sink {
            Some(held) => held,
            None => {
                let held = self.declare("sink", None, TIRInline::Unwritten);
                self.sink = Some(held);
                held
            }
        };
        let callee = self.expr(GIRExprKind::Item(item), ty);
        self.expr(GIRExprKind::Call { callee, args }, ty)
    }

    // ---- Patterns -----------------------------------------------------------

    pub fn pat(&mut self, kind: TTIRPatKind, ty: TyId) -> TTIRPatId {
        self.ttir.pats.push(TTIRPat { kind, ty, line: 1, col: 1 });
        self.ttir.pats.len() - 1
    }

    pub fn lit_pat(&mut self, n: i64) -> TTIRPatId {
        let ty = self.int;
        self.pat(TTIRPatKind::Lit { negated: false, value: TIRLit::Int(n) }, ty)
    }

    pub fn bind_pat(&mut self, local: GIRLocalId) -> TTIRPatId {
        let ty = self.locals[local].ty;
        self.pat(TTIRPatKind::Bind(local), ty)
    }

    // A declaration whose body is one already built, so that a call can name
    // it and `sir::opt` can find what to write out. The signature is thin --
    // nothing in the SIR reads it but the body it points at and whether the
    // source asked for the call to be written out.
    pub fn function(&mut self, name: &str, body: GIRBodyId, inline: TIRInline) -> TTIRItemId {
        self.declare(name, Some(body), inline)
    }

    fn declare(
        &mut self,
        name: &str,
        body: Option<GIRBodyId>,
        inline: TIRInline,
    ) -> TTIRItemId {
        let ty = self.null;
        let mut attrs = TIRFnAttrs::default();
        attrs.inline = inline;
        self.ttir.items.push(TTIRItem {
            kind: TTIRItemKind::Fn(TTIRFn {
                vis: TIRVis::Pub,
                attrs,
                is_const: false,
                is_unsafe: false,
                name: name.to_string(),
                symbol: name.to_string(),
                generics: Vec::new(),
                wheres: Vec::new(),
                outlives: Vec::new(),
                ty,
                params: Vec::new(),
                ret: ty,
                body,
            }),
            line: 1,
            col:  1,
        });
        self.ttir.items.len() - 1
    }

    // A call to one of them, which is the shape `sir::opt` writes out.
    pub fn calling(&mut self, item: TTIRItemId, args: Vec<GIRExprId>) -> GIRExprId {
        let ty = self.null;
        let callee = self.expr(GIRExprKind::Item(item), ty);
        self.expr(GIRExprKind::Call { callee, args }, ty)
    }

    // An enum whose variants are numbered as given, which is what a
    // discriminant test compares against.
    pub fn enumeration(&mut self, values: &[i64]) -> TTIRItemId {
        let variants = values
            .iter()
            .enumerate()
            .map(|(at, value)| TTIRVariant {
                attrs:   TIRAttrs::default(),
                name:    format!("V{}", at),
                payload: TTIRPayload::None,
                value:   *value,
            })
            .collect();
        self.ttir.items.push(TTIRItem {
            kind: TTIRItemKind::Enum {
                vis: TIRVis::Pub,
                attrs: TIRAttrs::default(),
                name: "E".to_string(),
                generics: Vec::new(),
                variants,
            },
            line: 1,
            col:  1,
        });
        self.ttir.items.len() - 1
    }

    // ---- Closing a body -----------------------------------------------------

    pub fn body(&mut self, entry: GIRBlockId) -> GIRBodyId {
        let blocks = std::mem::take(&mut self.blocks);
        let locals = std::mem::take(&mut self.locals);
        let params = std::mem::take(&mut self.params);
        self.gir.bodies.push(GIRBody { entry, blocks, locals, params });
        self.gir.bodies.len() - 1
    }

    pub fn finish(self) -> (TTIRProgram, GIRProgram) {
        (self.ttir, self.gir)
    }
}

// `for x in it { .. }`, with a second block inside the body jumping back to
// the head where `again` asks for one -- which is what a `continue` is.
pub fn walking(again: bool) -> Fixture {
    let mut f = Fixture::new();
    let it = f.local("it", f.int);
    let x = f.local("x", f.int);
    let (before, head, inner, exit) = (f.block(), f.block(), f.block(), f.block());
    f.term(before, GIRTerm::Goto(head));
    let read = f.read(it);
    f.term(head, GIRTerm::ForEach { local: x, iter: read, body: inner, exit });
    if again {
        let skip = f.block();
        let cond = f.boolean(true);
        f.term(inner, GIRTerm::Branch { cond, then: skip, els: head });
        f.term(skip, GIRTerm::Goto(head));
    } else {
        f.term(inner, GIRTerm::Goto(head));
    }
    f.term(exit, GIRTerm::Return(None));
    f.body(before);
    f
}

// ---- Running the passes -----------------------------------------------------

// Lowered, and held to what being in SSA form means. Every test goes through
// here, so a test that looks at one instruction still says the rest of the
// body is well formed -- which is most of what a verifier is worth.
pub fn built(f: Fixture) -> SIRProgram {
    let (ttir, gir) = f.finish();
    let mut lowerer = Lowerer::new(&ttir, &gir);
    lowerer.lower();
    let out = lowerer.finish();
    sound(&out);
    out
}

pub fn taken_out(f: Fixture) -> SIRProgram {
    let mut out = built(f);
    promote(&mut out);
    sound(&out);
    out
}

// And optimized on top of that. The two rules are checked again afterwards --
// every rewrite in `sir::opt` is one that can break them quietly, and a test
// of what it folded should not be the only thing standing between a broken
// rewrite and the pass after.
pub fn worked(f: Fixture) -> (SIRProgram, Stats) {
    let (ttir, gir) = f.finish();
    let mut lowerer = Lowerer::new(&ttir, &gir);
    lowerer.lower();
    let mut out = lowerer.finish();
    sound(&out);
    promote(&mut out);
    sound(&out);
    let stats = optimize(&mut out, &ttir);
    sound(&out);
    (out, stats)
}

pub fn sound(p: &SIRProgram) {
    for (id, body) in p.bodies.iter().enumerate() {
        let wrong = verify(body);
        assert!(wrong.is_empty(), "body {} is not in SSA form: {:#?}", id, wrong);
        let wrong = verify_order(body);
        assert!(wrong.is_empty(), "body {} reads above a def: {:#?}", id, wrong);
    }
}

// ---- Reading what came out --------------------------------------------------

// Every instruction of the body, live blocks only, with the block it stands in.
pub fn insts(body: &SIRBody) -> Vec<(SIRBlockId, SIRInst)> {
    let live = body.live();
    let mut out = Vec::new();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for inst in &block.insts {
            out.push((at, inst.clone()));
        }
    }
    out
}

pub fn kinds(body: &SIRBody) -> Vec<SIRInstKind> {
    insts(body).into_iter().map(|(_, inst)| inst.kind).collect()
}

pub fn count(body: &SIRBody, want: impl Fn(&SIRInstKind) -> bool) -> usize {
    kinds(body).iter().filter(|kind| want(kind)).count()
}

// Every phi standing in a live block.
pub fn phis(body: &SIRBody) -> Vec<(SIRBlockId, SIRPhi)> {
    let live = body.live();
    let mut out = Vec::new();
    for (at, block) in body.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        for phi in &block.phis {
            out.push((at, phi.clone()));
        }
    }
    out
}
