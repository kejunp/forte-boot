// A MIR body built by hand, for the tests of the things that read one.
//
// The same argument `sir::fixture` makes one level up. Building the input by
// running the pass before would put that pass under test as well, and it would
// not reach: what a verifier has to be tried against is a body that is *wrong*
// -- a register made twice, a phi missing a way in, a read of something made
// down a path that was not taken -- and no lowering makes one of those on
// purpose. They have to be written.
//
// What it builds is deliberately thin. Every register is eight bytes and an
// integer unless a test says otherwise, because nothing being tested here cares
// which, and a fixture that made the caller say would make every test longer
// for no answer.

use super::machine::{self, Class, Machine};
use super::mir_nodes::*;
use super::verify::{verify, verify_order};

pub struct Fixture {
    blocks: Vec<MIRBlock>,
    regs:   Vec<MIRReg>,
    frame:  Vec<MIRSlot>,
    params: Vec<MIRRegId>,
}

impl Fixture {
    pub fn new() -> Fixture {
        Fixture { blocks: Vec::new(), regs: Vec::new(), frame: Vec::new(), params: Vec::new() }
    }

    // ---- What a body is made of --------------------------------------------

    // A register nothing has made yet. Handing the id out before there is an
    // instruction to make it is what lets a test write a body in the order a
    // reader would read one.
    pub fn reg(&mut self) -> MIRRegId {
        self.regs.push(MIRReg::one(Class::Int, 8, 1, 1));
        self.regs.len() - 1
    }

    pub fn floating(&mut self) -> MIRRegId {
        self.regs.push(MIRReg::one(Class::Float, 8, 1, 1));
        self.regs.len() - 1
    }

    // Filled by the caller, so made by no instruction.
    pub fn param(&mut self) -> MIRRegId {
        let reg = self.reg();
        self.params.push(reg);
        reg
    }

    pub fn slot(&mut self, name: &str, bytes: usize) -> MIRFrameId {
        self.frame.push(MIRSlot {
            bytes,
            align: bytes.max(1),
            name: name.to_string(),
            spill: false,
        });
        self.frame.len() - 1
    }

    // An empty block that falls off the end, so that a test that forgets to
    // terminate one has a body that is still well formed.
    pub fn block(&mut self) -> MIRBlockId {
        self.blocks.push(MIRBlock {
            phis:  Vec::new(),
            insts: Vec::new(),
            term:  MIRTerm::Unreachable,
            line:  1,
            col:   1,
        });
        self.blocks.len() - 1
    }

    pub fn term(&mut self, at: MIRBlockId, term: MIRTerm) {
        self.blocks[at].term = term;
    }

    // ---- Instructions ------------------------------------------------------

    // An instruction that makes something, with the register it makes handed
    // back.
    pub fn push(&mut self, at: MIRBlockId, kind: MIRInstKind) -> MIRRegId {
        let def = self.reg();
        self.making(at, def, kind);
        def
    }

    // The same, but making a register the test already named -- which is how a
    // body that is wrong on purpose is written.
    pub fn making(&mut self, at: MIRBlockId, def: MIRRegId, kind: MIRInstKind) {
        self.blocks[at].insts.push(MIRInst { def: Some(def), kind, line: 1, col: 1 });
    }

    // One that makes nothing: a store, a call whose answer nobody wanted.
    pub fn effect(&mut self, at: MIRBlockId, kind: MIRInstKind) {
        self.blocks[at].insts.push(MIRInst { def: None, kind, line: 1, col: 1 });
    }

    // Change one edge of a phi already written. What a swap at the top of a
    // loop needs: the two phis have to name each other, and neither register
    // exists until both are made.
    pub fn set_phi_edge(
        &mut self,
        at: MIRBlockId,
        which: usize,
        from: MIRBlockId,
        reg: MIRRegId,
    ) {
        for (held, value) in &mut self.blocks[at].phis[which].edges {
            if *held == from {
                *value = reg;
            }
        }
    }

    pub fn phi(&mut self, at: MIRBlockId, edges: Vec<(MIRBlockId, MIRRegId)>) -> MIRRegId {
        let def = self.reg();
        self.blocks[at].phis.push(MIRPhi { def, edges });
        def
    }

    // ---- The handful every test writes -------------------------------------

    pub fn int(&mut self, at: MIRBlockId, n: i64) -> MIRRegId {
        self.push(at, MIRInstKind::Const(MIRConst::Int(n)))
    }

    pub fn add(&mut self, at: MIRBlockId, lhs: MIRRegId, rhs: MIRRegId) -> MIRRegId {
        self.push(at, MIRInstKind::Bin { op: MIRBinOp::Add, lhs, rhs })
    }

    pub fn less(&mut self, at: MIRBlockId, lhs: MIRRegId, rhs: MIRRegId) -> MIRRegId {
        self.push(at, MIRInstKind::Cmp { op: MIRCmpOp::SLt, lhs, rhs })
    }

    pub fn address(&mut self, at: MIRBlockId, slot: MIRFrameId) -> MIRRegId {
        self.push(at, MIRInstKind::Frame(slot))
    }

    pub fn load(&mut self, at: MIRBlockId, from: MIRRegId) -> MIRRegId {
        self.push(at, MIRInstKind::Load { from, bytes: 8 })
    }

    pub fn store(&mut self, at: MIRBlockId, to: MIRRegId, value: MIRRegId) {
        self.effect(at, MIRInstKind::Store { to, value, bytes: 8 });
    }

    pub fn call(&mut self, at: MIRBlockId, to: &str, args: Vec<MIRRegId>) -> MIRRegId {
        self.push(at, MIRInstKind::Call { to: MIRCallee::Symbol(to.to_string()), args })
    }

    // ---- Closing it off ----------------------------------------------------

    pub fn body(self, entry: MIRBlockId) -> MIRBody {
        MIRBody {
            symbol: "__F1t".to_string(),
            entry,
            blocks: self.blocks,
            regs: self.regs,
            frame: self.frame,
            params: self.params,
        }
    }

    pub fn program(self, entry: MIRBlockId) -> MIRProgram {
        MIRProgram { bodies: vec![self.body(entry)], pool: Vec::new() }
    }
}

impl Default for Fixture {
    fn default() -> Fixture {
        Fixture::new()
    }
}

// ---- Prebuilt shapes -------------------------------------------------------

// The shape every test of a graph wants: two ways into one block, so there is
// something for a phi to be about.
//
//        entry
//        /   \
//     then   els
//        \   /
//         join
pub fn diamond() -> (Fixture, [MIRBlockId; 4]) {
    let mut f = Fixture::new();
    let (entry, then, els, join) = (f.block(), f.block(), f.block(), f.block());
    let cond = f.int(entry, 1);
    f.term(entry, MIRTerm::Branch { cond, then, els });
    f.term(then, MIRTerm::Goto(join));
    f.term(els, MIRTerm::Goto(join));
    f.term(join, MIRTerm::Return(None));
    (f, [entry, then, els, join])
}

// ---- Reading one back ------------------------------------------------------

// Pinned rather than the host's, so a test says the same thing wherever it runs
// -- the same reason `sir::fixture::machine` pins one.
pub fn machine() -> Machine {
    machine::X86_64
}

// Held to every rule, which is what every runner does before it hands a body
// back. A test that looks at one instruction still says the rest is well
// formed, which is what makes these worth running rather than only writing.
pub fn sound(p: &MIRProgram) {
    for (at, body) in p.bodies.iter().enumerate() {
        let wrong = verify(body);
        assert!(wrong.is_empty(), "body {} is not well formed: {:#?}", at, wrong);
        let wrong = verify_order(body);
        assert!(wrong.is_empty(), "body {} is out of order: {:#?}", at, wrong);
    }
}

// Every instruction the entry reaches, with the block it is in. The blocks
// nothing reaches are still in the arena, so a count over all of them would be
// a count of what was built rather than of what runs.
pub fn insts(body: &MIRBody) -> Vec<(MIRBlockId, MIRInst)> {
    let live = body.live();
    body.blocks
        .iter()
        .enumerate()
        .filter(|(at, _)| live[*at])
        .flat_map(|(at, block)| block.insts.iter().map(move |inst| (at, inst.clone())))
        .collect()
}

pub fn kinds(body: &MIRBody) -> Vec<MIRInstKind> {
    insts(body).into_iter().map(|(_, inst)| inst.kind).collect()
}

pub fn count(body: &MIRBody, want: impl Fn(&MIRInstKind) -> bool) -> usize {
    kinds(body).iter().filter(|kind| want(kind)).count()
}

// The body whose symbol holds `name`. A symbol has the length of each part in
// front of it, so `1f` is the fn called `f` and `2id` the one called `id`.
pub fn body_of<'a>(p: &'a MIRProgram, name: &str) -> &'a MIRBody {
    p.bodies
        .iter()
        .find(|body| body.symbol.contains(name))
        .unwrap_or_else(|| {
            panic!(
                "no body named {}: there is {:#?}",
                name,
                p.bodies.iter().map(|body| &body.symbol).collect::<Vec<_>>()
            )
        })
}

// ---- A source, run as far as the SIR ---------------------------------------

// What everything downstream of the SIR takes as its input, built the way a
// compilation builds it.
//
// A hand-built SIR is the right input for a verifier, which has to be shown
// bodies that are wrong. It is the wrong input for the passes that come after:
// what `mir::mono` is about is generics, and a generic reaching the SIR at all
// is several passes' worth of agreement about what a `T` is. Writing that by
// hand would be writing down what those passes are believed to do, which is a
// test of the belief.
//
// So this is here, at the hub, beside the fixture that builds by hand -- the
// two are for different questions and both are wanted. It is the same walk
// `sir::opt`'s tests make for the same reason, with the optimiser left off:
// nothing after the SIR needs it to have run.
pub fn compiled(source: &str) -> (crate::tir::ttir_nodes::TTIRProgram, crate::sir::sir_nodes::SIRProgram) {
    use crate::expand::Expander;
    use crate::gir;
    use crate::lex::lexer::Lexer;
    use crate::parse::parser::Parser;
    use crate::prep::preprocess;
    use crate::sema;
    use crate::sir::lower::Lowerer;
    use crate::sir::promote::promote;
    use crate::tir::lower::Lowerer as TIRLowerer;

    let prepped = preprocess(source);
    let mut p = Parser::new(Lexer::new(&prepped));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{:#?}", p.errors());
    let root = {
        let mut e = Expander::new(&mut p);
        let out = e.expand(&root);
        assert!(e.errors().is_empty(), "{:#?}", e.errors());
        out
    };
    let mut l = TIRLowerer::new(&p);
    l.lower(&root);
    assert!(l.errors().is_empty(), "{:#?}", l.errors());
    let tir = l.finish();
    let (ttir, errors) = sema::lower::Lowerer::new(&tir).lower(vec!["t".to_string()]);
    assert!(!errors.has_errors(), "{:#?}", errors);

    let mut lowerer = gir::lower::Lowerer::new(&ttir);
    lowerer.lower();
    let mut graph = lowerer.finish();
    let copies = sema::borrows::Copies::of(&ttir);
    let generics: Vec<Vec<crate::tir::ttir_nodes::TTIRGeneric>> = (0..graph.bodies.len())
        .map(|body| crate::generics_of(&ttir, body))
        .collect();
    gir::drops::Drops::new(&ttir, &copies).place(&mut graph, &generics);
    gir::opt::optimize(&mut graph);

    let mut lowerer = Lowerer::new(&ttir, &graph);
    lowerer.lower();
    let mut out = lowerer.finish();
    promote(&mut out);
    (ttir, out)
}
