// Lowering the SIR to the MIR: the same graph, in what a machine does.
//
//     SIR -> mono -> lower -> MIR
//                     ^^^^^
//
// Three things happen here, and the first is the one everything else follows
// from.
//
// **A type becomes a number.** `mir::layout` has already worked out what each
// one takes and where its parts sit, so a `Field` whose index was 1 becomes an
// address and a displacement, and a `Load` whose type was `i32` becomes a load
// of four bytes. After this nothing can ask what a value's type was, which is
// the point: there is no type left to ask about, and every pass downstream is
// held to the numbers rather than trusted with them.
//
// **A value is in a register or it is not.** Anything that fits in one is in
// one. Everything else -- a structure, an array, a string, a closure -- lives
// in the frame, and what stands in the register is its *address*. That one
// decision settles most of the file: `Field` on something in memory is an
// offset and a load, `Store` of something in memory is a copy of so many bytes,
// and the two never have to be told apart at the point of use because the
// register always holds the same kind of thing for a given type.
//
// **An answer too big for a register is written where the caller says.** A
// value held by its address is held in somebody's frame, and a body that
// answered with one of its own would be answering with an address that dies at
// its epilogue -- which is what it did. So a body that answers with one takes
// the room for it as a first parameter in front of the written ones, copies
// its answer there and hands that address back, and a call that wants one
// makes a slot and passes it. `sret` on the builder below is the whole of it.
//
// **What the language has and a machine does not becomes a call.** A map, a
// set, a closure's captures, a release at the end of a scope. `mir::runtime`
// names them and this writes the calls; nothing else in the compiler mentions
// them again. One of the four is also *written* here rather than called into a
// library -- a release is a fact about a declaration, so `glue` builds a body
// per type once every other body has been walked.
//
// The registers are made before any instruction is. Every value in the SIR gets
// one up front, because a phi at the top of a loop reads a value made at the
// bottom of it -- the block that makes it has a higher number and has not been
// walked yet. `sir::lower` pre-allocates its blocks for the same reason and
// says so: "an edge may be written before its target has been reached".
//
// What does *not* happen here is anything about how many registers there are.
// A body leaves this pass wanting as many as it wants, and `mir::regalloc` is
// where that meets a machine. Keeping the two apart is what lets this file be
// about meaning and that one be about scarcity.

use std::collections::{HashMap, HashSet};

use crate::sema::borrows::Copies;
use crate::sema::names::Mangler;
use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRLit, TIRPrim};
use crate::tir::ttir_nodes::{TTIRExprKind, TTIRItemKind, Ty, TyId};

use super::layout::{Layout, Layouts, Shape};
use super::machine::{Class, Machine};
use super::mir_nodes::*;
use super::mono::Made;

// A literal written into a global's image, in as many bytes as the type is.
//
// **Little-endian, and that is not a choice made here.** All three machines
// this compiler emits for are little-endian in the configurations it emits --
// x86-64 always, aarch64 and riscv64 in every ABI in use -- so there is one
// answer and `mir::machine` is not asked for it. A big-endian target would
// have to say so, and would have to say so in a good many places besides this.
//
// A value wider than the room truncates rather than refusing. What fits in an
// `i32` is the checker's question and it is not asked anywhere yet, of a global
// or of a plain literal; taking the low bytes is what every machine does with
// the store that would have written it.
//
// A string writes nothing. What a `str` *is* here is an address and a length,
// and an address is not known until the linker has run -- it wants a
// relocation into the pool rather than bytes, which is a thing no global has
// asked for yet and is not invented on the way past.
fn write_lit(into: &mut [u8], lit: &TIRLit) {
    let whole = |n: i64| n.to_le_bytes();
    match lit {
        TIRLit::Int(n) => {
            let held = whole(*n);
            let take = into.len().min(held.len());
            into[..take].copy_from_slice(&held[..take]);
        }
        TIRLit::Char(c) => {
            let held = u32::from(*c).to_le_bytes();
            let take = into.len().min(held.len());
            into[..take].copy_from_slice(&held[..take]);
        }
        TIRLit::Bool(b) => into[0] = u8::from(*b),
        // Four bytes of room means it was declared `f32`, whatever the value
        // was written as: a literal has the type the declaration gave it.
        TIRLit::Float(n) => {
            if into.len() >= 8 {
                into[..8].copy_from_slice(&n.to_le_bytes());
            } else if into.len() >= 4 {
                into[..4].copy_from_slice(&(*n as f32).to_le_bytes());
            }
        }
        TIRLit::Str(_) | TIRLit::Null => {}
    }
}

mod aggregates;
mod calls;
mod glue;
mod places;
mod values;
mod vectors;

pub struct Lowerer<'a> {
    made:      &'a Made,
    layouts:   Layouts<'a>,
    mangler:   Mangler,
    machine:   Machine,
    out:       MIRProgram,
    b:         Builder,
    // Which types have anything to release, asked the same way `gir::drops`
    // asked it. The two have to agree: that pass decided where a release goes
    // and this one writes what it does, and a type it called droppable and
    // this one did not would be a call to a routine nothing emitted.
    copies:    Copies,
    // The types a release was emitted for, and the routines already written.
    // A glue body releases the fields of its type, which wants more glue, so
    // the first is a worklist rather than a list.
    wanted:    Vec<TyId>,
    written:   HashSet<String>,
    // What could not be written, in the words a driver should print. A generic
    // whose argument the arena cannot name is the only thing that gets here.
    pub gaps:  Vec<String>,
}

#[derive(Default)]
struct Builder {
    blocks: Vec<MIRBlock>,
    regs:   Vec<MIRReg>,
    frame:  Vec<MIRSlot>,
    params: Vec<MIRRegId>,
    // The MIR block being written into. The blocks are one for one with the
    // SIR's -- nothing here splits one -- so this is only ever the block whose
    // instructions are being walked.
    current: MIRBlockId,
    // What each SIR value became: the register that holds it, or the register
    // that holds its address. Which of the two is settled by its type and is
    // the same at every use, so nothing has to be told which it has in hand.
    at:      Vec<MIRRegId>,
    // The frame slot each SIR slot became.
    slot_of: Vec<MIRFrameId>,
    // Which body is being lowered, for looking up what a name it holds was
    // resolved to. `mono` keyed those by the body they are in.
    body:    SIRBodyId,
    // Which declaration each value naming one stands for. Gathered before the
    // blocks are walked: a call reaches its callee through a value, and the
    // block that named it may have a higher number than the block that calls.
    symbol_value: HashMap<SIRValueId, String>,
    // The values naming a declaration that nothing does with it but call it.
    //
    // A call to a known declaration names the symbol itself, so the address the
    // `Item` worked out is read by nothing -- and an address nothing reads is
    // an instruction that costs a register for the length of the call. Not
    // emitting it is not an optimisation so much as not writing something down
    // twice: the name is already in the call.
    only_called: HashSet<SIRValueId>,
    // The registers holding an address of somewhere in this frame.
    //
    // A store through one of these skips the write barrier, and that is not an
    // optimisation. The collector scans a stack once and leaves it black; what
    // makes that sound is the deletion half of the barrier, which does not
    // depend on seeing stack writes at all. So a barrier here would cost a
    // call per local assignment and buy nothing.
    //
    // It is gathered as the instructions are written rather than looked for
    // afterwards, because it is exactly the transitive closure of "made by a
    // `Frame`" through the three instructions that move an address about --
    // and every one of those goes through `making`.
    on_frame: HashSet<MIRRegId>,
    // Where an answer too big for a register is written.
    //
    // A value held by its address is held in *somebody's* frame, and a body
    // that answered with one of its own would be answering with an address
    // that dies at the epilogue. So a caller that wants one hands over room
    // for it, as a first argument in front of the written ones, and the body
    // copies its answer there and hands the same address back.
    //
    // That is the convention every one of the three machines uses and calls by
    // a different name. `None` for a body whose answer fits a register, which
    // is nearly all of them.
    sret:     Option<MIRRegId>,
}

impl<'a> Lowerer<'a> {
    pub fn new(made: &'a Made, machine: Machine) -> Lowerer<'a> {
        Lowerer {
            made,
            layouts: Layouts::new(&made.ttir, machine),
            mangler: Mangler::new(&made.ttir),
            machine,
            out: MIRProgram::default(),
            b: Builder::default(),
            copies: Copies::of(&made.ttir),
            wanted: Vec::new(),
            written: HashSet::new(),
            gaps: Vec::new(),
        }
    }

    pub fn lower(&mut self) {
        for at in 0..self.made.sir.bodies.len() {
            let built = self.body(at);
            self.out.bodies.push(built);
        }
        // And a body for every release the bodies above called for, which is
        // the last thing because it is the only pass here whose input is what
        // the others emitted.
        self.glue();
    }

    pub fn finish(mut self) -> MIRProgram {
        self.globals();
        self.out
    }

    // ---- The globals -------------------------------------------------------

    // Somewhere for every global to live.
    //
    // A global is a place, so what a use of one compiles to is the address of a
    // symbol (`places::ItemAddr`) -- and until this ran, nothing anywhere
    // defined that symbol and the program failed at the link step rather than
    // in the compiler. §8 asked for "a segment for the globals that are left,
    // which have to be somewhere because a global is a place and may be
    // assigned to". This is where they are put.
    //
    // Every global of the suite and not only the ones something read: a global
    // is a declaration and not a use, and one nothing mentions is still a name
    // the program has. That also keeps this from depending on what the
    // optimiser left standing.
    //
    // What is skipped is a global whose type has no layout -- a type variable
    // nothing settled, which is what an uninitialised `var` with no annotation
    // leaves. There is nothing to reserve for a width nobody knows, and the
    // link error it produces is the one that was there before rather than a
    // new one.
    fn globals(&mut self) {
        for at in 0..self.made.ttir.items.len() {
            let TTIRItemKind::Global { ty, init, .. } = &self.made.ttir.items[at].kind else {
                continue;
            };
            let (ty, init) = (*ty, *init);
            let Some(symbol) = self.mangler.symbol_of(at, &self.made.ttir) else {
                continue;
            };
            let Some(layout) = self.layouts.of(ty) else { continue };
            let bytes = layout.bytes.max(1);

            // Nought unless something said otherwise, which is what a global
            // with no initialiser means and what one this could not read gets
            // as well.
            let mut image = vec![0u8; bytes];
            if let Some(held) = init.and_then(|at| self.made.ttir.exprs.get(at)) {
                if let TTIRExprKind::Literal(lit) = &held.kind {
                    write_lit(&mut image, lit);
                }
            }
            self.out.data.push(MIRGlobal {
                symbol,
                bytes: image,
                align: layout.align.max(1),
            });
        }
    }

    // ---- One body ----------------------------------------------------------

    fn body(&mut self, at: SIRBodyId) -> MIRBody {
        let source = &self.made.sir.bodies[at];
        self.b = Builder { body: at, ..Builder::default() };

        // The frame first, because an address of a slot may be taken in the
        // very first instruction.
        for slot in &source.slots {
            let held = self.laid(slot.ty);
            let name = format!("${}", self.b.frame.len());
            self.b.frame.push(MIRSlot {
                bytes: held.bytes.max(1),
                align: held.align.max(1),
                name,
                spill: false,
            });
        }
        self.b.slot_of = (0..source.slots.len()).collect();

        // Then a register per value, before any instruction is written -- see
        // the header.
        //
        // A value the SIR made with one of the `*Addr` instructions is sized
        // by the machine and not by its type. The type on one of those is the
        // type of the place it addresses and not of what the register holds
        // (`sir::lower::address`), so an `i32` element's address would be
        // asked for in four bytes -- and a four-byte address is three quarters
        // of an address. It never showed while every place with an address was
        // a structure, because `indirect` gives those a word anyway; a `ptr
        // i32` indexed for a store is the first place a *small* type is
        // reached by address.
        let addressed = addresses(source);
        let regs: Vec<MIRReg> = (0..source.values.len())
            .map(|value| {
                let held = source.values[value].clone();
                if addressed.contains(&value) {
                    return MIRReg::one(Class::Int, self.machine.word, held.line, held.col);
                }
                self.holding(held.ty, held.lanes, held.line, held.col)
            })
            .collect();
        self.b.regs = regs;
        self.b.at = (0..source.values.len()).collect();

        self.b.params = source.params.iter().map(|&value| self.of(value)).collect();

        // A body whose answer is held by its address takes the room for it in
        // front of everything else. Which bodies those are is read off the
        // terminators rather than looked up: what a body answers with is the
        // type of what it returns, and it is the same at every return.
        self.b.sret = None;
        let answers = source.blocks.iter().find_map(|b| match b.term {
            SIRTerm::Return(Some(value)) => Some(value),
            _ => None,
        });
        if let Some(value) = answers {
            let ty = self.ty_of(value);
            if self.indirect(ty) {
                let (line, col) = (source.blocks[source.entry].line, 1);
                let room = self.temp(line, col);
                self.b.params.insert(0, room);
                self.b.sret = Some(room);
            }
        }

        // What each value naming a declaration stands for -- see the field.
        for (bl, block) in source.blocks.iter().enumerate() {
            for (i, inst) in block.insts.iter().enumerate() {
                if !matches!(inst.kind, SIRInstKind::Item(_) | SIRInstKind::ItemAddr(_)) {
                    continue;
                }
                let (Some(def), Some(name)) = (inst.def, self.made.symbol_of.get(&(at, bl, i)))
                else {
                    continue;
                };
                self.b.symbol_value.insert(def, name.clone());
            }
        }

        // Which of those nothing does with but call -- see the field.
        let mut uses_of: HashMap<SIRValueId, usize> = HashMap::new();
        let mut called: HashMap<SIRValueId, usize> = HashMap::new();
        for block in &source.blocks {
            for inst in &block.insts {
                for value in SIRBody::uses(&inst.kind) {
                    *uses_of.entry(value).or_insert(0) += 1;
                }
                if let SIRInstKind::Call { callee, .. } = inst.kind {
                    *called.entry(callee).or_insert(0) += 1;
                }
            }
            // The SIR's terminators have no `uses` of their own, so the two
            // that read a value are asked here.
            match block.term {
                SIRTerm::Branch { cond, .. } => *uses_of.entry(cond).or_insert(0) += 1,
                SIRTerm::Return(Some(value)) => *uses_of.entry(value).or_insert(0) += 1,
                _ => {}
            }
            for phi in &block.phis {
                for &(_, value) in &phi.edges {
                    *uses_of.entry(value).or_insert(0) += 1;
                }
            }
        }
        self.b.only_called = self
            .b
            .symbol_value
            .keys()
            .copied()
            .filter(|value| {
                let held = called.get(value).copied().unwrap_or(0);
                held > 0 && held == uses_of.get(value).copied().unwrap_or(0)
            })
            .collect();

        // A block per block, so an edge may be written before its target is
        // reached.
        for block in &source.blocks {
            self.b.blocks.push(MIRBlock {
                phis:  Vec::new(),
                insts: Vec::new(),
                term:  MIRTerm::Unreachable,
                line:  block.line,
                col:   block.col,
            });
        }

        for bl in 0..source.blocks.len() {
            self.block(at, bl);
        }

        let built = std::mem::take(&mut self.b);
        MIRBody {
            symbol: self.made.symbols.get(at).cloned().unwrap_or_default(),
            entry:  self.made.sir.bodies[at].entry,
            blocks: built.blocks,
            regs:   built.regs,
            frame:  built.frame,
            params: built.params,
        }
    }

    fn block(&mut self, body: SIRBodyId, at: SIRBlockId) {
        self.b.current = at;
        let source = self.made.sir.bodies[body].blocks[at].clone();

        for phi in &source.phis {
            let def = self.of(phi.def);
            let edges = phi.edges.iter().map(|&(from, value)| (from, self.of(value))).collect();
            self.b.blocks[at].phis.push(MIRPhi { def, edges });
        }

        for (i, inst) in source.insts.iter().enumerate() {
            self.inst(inst, at, i);
        }

        self.b.blocks[at].term = match &source.term {
            SIRTerm::Goto(to) => MIRTerm::Goto(*to),
            SIRTerm::Branch { cond, then, els } => {
                MIRTerm::Branch { cond: self.of(*cond), then: *then, els: *els }
            }
            // The answer copied into the caller's room, and that room handed
            // back -- which is what the machine's own convention says the
            // return register holds for a value of this size.
            SIRTerm::Return(Some(value)) => match self.b.sret {
                Some(room) => {
                    let ty = self.ty_of(*value);
                    let bytes = self.bytes_of(ty).max(1);
                    let from = self.of(*value);
                    let (line, col) = (source.line, source.col);
                    self.effect(MIRInstKind::Copy { to: room, from, bytes }, line, col);
                    MIRTerm::Return(Some(room))
                }
                None => MIRTerm::Return(Some(self.of(*value))),
            },
            SIRTerm::Return(None) => MIRTerm::Return(None),
            SIRTerm::Unreachable => MIRTerm::Unreachable,
        };
    }

    // Which part of the lowering an instruction belongs to. The five below are
    // the five questions a machine asks of the SIR's vocabulary, and each file
    // answers one of them.
    fn inst(&mut self, inst: &SIRInst, at: SIRBlockId, i: usize) {
        use SIRInstKind::*;
        match &inst.kind {
            Literal(_) | Item(_) | SelfValue | Unary { .. } | Binary { .. } | Cast(_) => {
                self.value(inst, at, i)
            }
            Addr(_) | ItemAddr(_) | SelfAddr | FieldAddr { .. } | TupleAddr { .. }
            | IndexAddr { .. } | Load { .. } | Store { .. } | Field { .. }
            | TupleIndex { .. } | Index { .. } | Undef => self.place(inst, at, i),
            StructLit { .. } | VariantLit { .. } | ArrayLit(_) | TupleLit(_) | Range { .. }
            | Discriminant(_) | Payload { .. } => self.aggregate(inst),
            Call { .. } | Method { .. } | Closure { .. } | Map { .. } | Set { .. }
            | Drop(_) | DropSlot(_) | IterStart | IterValid { .. } | IterElem { .. }
            | IterStep { .. } => self.calling(inst, at, i),
            Pack(_) | Lane { .. } | Lanes { .. } | VecStore { .. } => self.vector(inst),
        }
    }

    // ---- What the parts build with -----------------------------------------

    // The register a SIR value became.
    pub(super) fn of(&self, value: SIRValueId) -> MIRRegId {
        self.b.at.get(value).copied().unwrap_or(0)
    }

    pub(super) fn ty_of(&self, value: SIRValueId) -> TyId {
        self.made.sir.bodies[self.b.body].values[value].ty
    }

    // An instruction that fills a register already spoken for, which is what
    // every value the SIR named is.
    pub(super) fn making(&mut self, def: MIRRegId, kind: MIRInstKind, line: usize, col: usize) {
        if self.from_frame(&kind) {
            self.b.on_frame.insert(def);
        }
        let at = self.b.current;
        self.b.blocks[at].insts.push(MIRInst { def: Some(def), kind, line, col });
    }

    // Whether the address this makes is an address in the frame. A slot is
    // one; an offset or an index into one still is; a copy of one is. Nothing
    // else is, and a `Load` in particular is not -- what was read out of a
    // frame slot is whatever was put there.
    fn from_frame(&self, kind: &MIRInstKind) -> bool {
        match kind {
            MIRInstKind::Frame(_) => true,
            MIRInstKind::Move(of) => self.b.on_frame.contains(of),
            MIRInstKind::Offset { base, .. } | MIRInstKind::Scaled { base, .. } => {
                self.b.on_frame.contains(base)
            }
            _ => false,
        }
    }

    pub(super) fn on_frame(&self, reg: MIRRegId) -> bool {
        self.b.on_frame.contains(&reg)
    }

    // One that makes a register nothing has spoken for: a working value on the
    // way to one that was.
    pub(super) fn push(&mut self, kind: MIRInstKind, line: usize, col: usize) -> MIRRegId {
        let def = self.temp(line, col);
        self.making(def, kind, line, col);
        def
    }

    // One that makes nothing.
    pub(super) fn effect(&mut self, kind: MIRInstKind, line: usize, col: usize) {
        let at = self.b.current;
        self.b.blocks[at].insts.push(MIRInst { def: None, kind, line, col });
    }

    // A register the size of an address, which every working value that is not
    // a number is.
    pub(super) fn temp(&mut self, line: usize, col: usize) -> MIRRegId {
        self.b.regs.push(MIRReg::one(Class::Int, self.machine.word, line, col));
        self.b.regs.len() - 1
    }

    pub(super) fn temp_of(&mut self, class: Class, bytes: usize, line: usize, col: usize)
        -> MIRRegId {
        self.b.regs.push(MIRReg::one(class, bytes, line, col));
        self.b.regs.len() - 1
    }

    // Room in the frame for something that has to have an address.
    pub(super) fn slot(&mut self, name: String, bytes: usize, align: usize) -> MIRFrameId {
        self.b.frame.push(MIRSlot { bytes: bytes.max(1), align: align.max(1), name, spill: false });
        self.b.frame.len() - 1
    }

    pub(super) fn slot_of(&self, slot: SIRSlotId) -> MIRFrameId {
        self.b.slot_of.get(slot).copied().unwrap_or(0)
    }

    // What the first parameter is, which is what `self` always is.
    pub(super) fn receiver(&self) -> Option<MIRRegId> {
        self.b.params.first().copied()
    }

    // What a name held by one instruction was resolved to. `mono` worked these
    // out, because after it an `Item` no longer says which instance it meant.
    pub(super) fn symbol_at(&self, at: SIRBlockId, i: usize) -> Option<String> {
        self.made.symbol_of.get(&(self.b.body, at, i)).cloned()
    }

    // And what a table there holds, where the instruction is one that builds
    // one -- which is a coercion to a trait object and nothing else.
    pub(super) fn table_at(&self, at: SIRBlockId, i: usize) -> Option<Vec<String>> {
        self.made.table_of.get(&(self.b.body, at, i)).cloned()
    }

    pub(super) fn machine(&self) -> Machine {
        self.machine
    }

    pub(super) fn frame_len(&self) -> usize {
        self.b.frame.len()
    }

    pub(super) fn body_at(&self) -> SIRBodyId {
        self.b.body
    }

    // The symbol a value holding a declaration stands for, where it holds one.
    // Gathered before the blocks are walked, because a call may stand in a
    // block with a lower number than the one that named what it calls.
    pub(super) fn symbol_value(&self, value: SIRValueId) -> Option<String> {
        self.b.symbol_value.get(&value).cloned()
    }

    // Whether a value naming a declaration is only ever called, so that the
    // address of it need not be worked out at all.
    pub(super) fn only_called(&self, value: SIRValueId) -> bool {
        self.b.only_called.contains(&value)
    }

    // The slot standing for one of the enclosing body's locals, which is what a
    // capture names.
    pub(super) fn slot_named(&self, local: usize) -> Option<MIRFrameId> {
        let body = &self.made.sir.bodies[self.b.body];
        body.slots
            .iter()
            .position(|slot| slot.of == Some(local))
            .map(|at| self.slot_of(at))
    }

    // And what that slot holds, which is wanted wherever the slot is reached
    // by name rather than through an instruction carrying the type along.
    pub(super) fn ty_named(&self, local: usize) -> Option<TyId> {
        let body = &self.made.sir.bodies[self.b.body];
        body.slots.iter().find(|slot| slot.of == Some(local)).map(|slot| slot.ty)
    }

    // A type as the mangling writes it, which is what a release is named after.
    pub(super) fn spell(&self, ty: TyId) -> String {
        self.mangler.spell(ty, &self.made.ttir)
    }

    pub(super) fn word(&self) -> usize {
        self.machine.word
    }

    // ---- What a type comes to ----------------------------------------------

    // The layout, with an answer for the types that have none.
    //
    // After `mir::mono` a body that is reached has no type parameter left in
    // it, so the only way to get `None` here is a type with no size at all --
    // one that holds itself. Nothing can be emitted for that, and there is no
    // diagnostic left at this point in the compiler to say so, so it is treated
    // as an address: wrong, but wrong in a bounded way that a reader of the
    // listing can see, rather than a panic in a back end.
    pub(super) fn laid(&mut self, ty: TyId) -> Layout {
        self.layouts.of(ty).unwrap_or(Layout {
            bytes: self.machine.word,
            align: self.machine.word,
            shape: Shape::Scalar,
        })
    }

    pub(super) fn bytes_of(&mut self, ty: TyId) -> usize {
        self.laid(ty).bytes
    }

    pub(super) fn stride_of(&mut self, ty: TyId) -> usize {
        let held = self.laid(ty);
        if held.align == 0 { held.bytes } else { held.bytes.div_ceil(held.align) * held.align }
    }

    pub(super) fn field_at(&mut self, ty: TyId, index: usize) -> i64 {
        self.layouts.field(ty, index).unwrap_or(0) as i64
    }

    pub(super) fn payload_at(&mut self, ty: TyId, variant: usize, index: usize) -> i64 {
        self.layouts.payload(ty, variant, index).unwrap_or(0) as i64
    }

    pub(super) fn tag_of(&mut self, ty: TyId) -> usize {
        self.layouts.tag(ty).unwrap_or(self.machine.word)
    }

    // Whether one of these lives in the frame rather than in a register, which
    // is the decision the header is about. Anything a register cannot hold is
    // reached through its address instead.
    pub(super) fn indirect(&mut self, ty: TyId) -> bool {
        let held = self.laid(ty);
        match held.shape {
            Shape::Scalar => held.bytes > self.machine.word,
            Shape::Empty => false,
            Shape::Fat | Shape::Fields(_) | Shape::Tagged { .. } | Shape::Elements { .. } => true,
        }
    }

    // What a register holding one of these has to be.
    fn holding(&mut self, ty: TyId, lanes: usize, line: usize, col: usize) -> MIRReg {
        if lanes > 1 {
            // Several of them side by side, which is a vector register --
            // the same file the floats are in on both machines here.
            let one = self.bytes_of(ty).max(1);
            return MIRReg { class: Class::Float, bytes: one * lanes, lanes, line, col };
        }
        if self.indirect(ty) {
            return MIRReg::one(Class::Int, self.machine.word, line, col);
        }
        let held = self.laid(ty);
        MIRReg::one(self.class_of(ty), held.bytes.max(1), line, col)
    }

    pub(super) fn class_of(&mut self, ty: TyId) -> Class {
        match crate::sir::target::prim(&self.made.ttir, ty) {
            Some(TIRPrim::F32) | Some(TIRPrim::F64) => Class::Float,
            _ => Class::Int,
        }
    }

    // The machine's idea of what a value is: a width, and whether the top bit
    // means anything. What a cast needs at both ends.
    pub(super) fn scalar_of(&mut self, ty: TyId) -> MIRScalar {
        let bytes = self.bytes_of(ty).max(1);
        match crate::sir::target::prim(&self.made.ttir, ty) {
            Some(TIRPrim::F32) => MIRScalar::Float { bytes: 4 },
            Some(TIRPrim::F64) => MIRScalar::Float { bytes: 8 },
            Some(p) => MIRScalar::Int { bytes, signed: signed(p) },
            // Everything that is not a primitive is reached by its address, and
            // an address is an unsigned number as wide as one.
            None => MIRScalar::Int { bytes, signed: false },
        }
    }

    pub(super) fn signed_ty(&mut self, ty: TyId) -> bool {
        match crate::sir::target::prim(&self.made.ttir, ty) {
            Some(p) => signed(p),
            None => false,
        }
    }

    pub(super) fn floating(&mut self, ty: TyId) -> bool {
        matches!(
            crate::sir::target::prim(&self.made.ttir, ty),
            Some(TIRPrim::F32) | Some(TIRPrim::F64)
        )
    }

    // Where the elements of something begin.
    //
    // An array *is* its elements, so its address is theirs. A run and a string
    // are a *pointer* to them, so theirs is one load further on. Getting that
    // wrong reads the pointer and the length as if they were the first two
    // elements, which is a wrong answer that looks like an answer.
    //
    // Both the `for` cursor and an index want this, which is why it is here
    // rather than beside either of them.
    pub(super) fn elements(&mut self, value: SIRValueId, line: usize, col: usize) -> MIRRegId {
        let ty = self.bare(self.ty_of(value));
        let base = self.of(value);
        match self.made.ttir.types.get(ty) {
            Some(Ty::Run(_)) | Some(Ty::Prim(TIRPrim::Str)) => {
                let word = self.machine.word;
                self.push(MIRInstKind::Load { from: base, bytes: word }, line, col)
            }
            _ => base,
        }
    }

    // Through however many references or pointers to what is at the end of
    // them. `places` has a `through` that goes one layer, which is what
    // reaching into a `&&T` wants; this is the other question and both are
    // asked.
    pub(super) fn bare(&self, ty: TyId) -> TyId {
        match self.made.ttir.types.get(ty) {
            Some(Ty::Ref { inner, .. }) | Some(Ty::Ptr(inner)) => self.bare(*inner),
            _ => ty,
        }
    }

    // ---- The two moves everything in memory is made of ---------------------

    // Room for one of `ty`, and its address.
    pub(super) fn room(&mut self, ty: TyId, name: &str, line: usize, col: usize) -> MIRRegId {
        let held = self.laid(ty);
        let slot = self.slot(name.to_string(), held.bytes, held.align);
        self.push(MIRInstKind::Frame(slot), line, col)
    }

    // Putting a value where an address says, whichever of the two kinds it is.
    // A number is stored; anything reached by its address is copied, because a
    // store writes one place and this may be writing a great many.
    //
    // And where the value holds an address and the place is not in this frame,
    // it goes through the collector's write barrier instead. This is the one
    // choke point every write in the language comes through, which is why the
    // barrier is here and nowhere else -- a barrier at five call sites would
    // be a barrier missing from a sixth.
    pub(super) fn put(&mut self, to: MIRRegId, value: SIRValueId, line: usize, col: usize) {
        let ty = self.ty_of(value);
        let from = self.of(value);
        let bytes = self.bytes_of(ty).max(1);
        let watched = !self.on_frame(to);

        if self.indirect(ty) {
            if watched && self.holds_pointers(ty) {
                let shape = self.shape_reg(ty, line, col);
                self.effect(
                    MIRInstKind::Call {
                        to:   MIRCallee::Symbol(super::runtime::COPY.to_string()),
                        args: vec![to, from, shape],
                    },
                    line,
                    col,
                );
                return;
            }
            self.effect(MIRInstKind::Copy { to, from, bytes }, line, col);
            return;
        }
        if watched && self.is_address(ty) {
            self.effect(
                MIRInstKind::Call {
                    to:   MIRCallee::Symbol(super::runtime::WRITE.to_string()),
                    args: vec![to, from],
                },
                line,
                col,
            );
            return;
        }
        self.effect(MIRInstKind::Store { to, value: from, bytes }, line, col);
    }

    // ---- What a type is, for the runtime -----------------------------------

    // Whether a register holding one of these holds an address the collector
    // may have to follow. The three that are one word; everything wider is
    // `indirect` and is asked about through its shape instead.
    pub(super) fn is_address(&self, ty: TyId) -> bool {
        matches!(
            self.made.ttir.types.get(ty),
            Some(Ty::Ref { .. }) | Some(Ty::Ptr(_)) | Some(Ty::GC(_))
        )
    }

    // Whether anything anywhere inside one of these is an address, which is
    // what says whether moving one needs the barrier at all.
    pub(super) fn holds_pointers(&mut self, ty: TyId) -> bool {
        match super::shape::describe(&mut self.layouts, &self.made.ttir, self.machine, ty) {
            Some(held) => held[super::shape::HEADER..].iter().any(|byte| *byte != 0),
            None => false,
        }
    }

    // The address of `ty`'s descriptor, put in the pool if it is not there
    // already. Under the type's own name rather than a number, so that two
    // bodies wanting the same type name the same thing.
    pub(super) fn shape_reg(&mut self, ty: TyId, line: usize, col: usize) -> MIRRegId {
        let name = super::shape::symbol(&self.mangler, &self.made.ttir, ty);
        let bytes =
            super::shape::describe(&mut self.layouts, &self.made.ttir, self.machine, ty);
        match bytes {
            Some(bytes) => {
                self.named(name.clone(), bytes);
                self.push(MIRInstKind::Symbol(name), line, col)
            }
            // No layout means no descriptor, and `layout` has already said so.
            // A nought is what the runtime takes for "nothing was said".
            None => self.push(MIRInstKind::Const(MIRConst::Int(0)), line, col),
        }
    }

    // The descriptor for a closure's environment, which is not a type anything
    // declared: it is a run of addresses, one per capture. Nothing spells it,
    // so it is named after how many there are.
    pub(super) fn env_shape(&mut self, words: usize, line: usize, col: usize) -> MIRRegId {
        let name = format!("__Tenv{}", words);
        let bytes = super::shape::environment(words, self.machine);
        self.named(name.clone(), bytes);
        self.push(MIRInstKind::Symbol(name), line, col)
    }

    // Reading one out of an address into the register that was spoken for. The
    // same split the other way: a number is loaded, and something bigger is
    // copied into room of its own, because the value is a copy of what was
    // there and not the thing itself.
    pub(super) fn take(
        &mut self,
        def: MIRRegId,
        from: MIRRegId,
        ty: TyId,
        line: usize,
        col: usize,
    ) {
        let bytes = self.bytes_of(ty).max(1);
        if self.indirect(ty) {
            let held = self.laid(ty);
            let name = format!("${}", self.b.frame.len());
            let slot = self.slot(name, held.bytes, held.align);
            self.making(def, MIRInstKind::Frame(slot), line, col);
            self.effect(MIRInstKind::Copy { to: def, from, bytes }, line, col);
        } else {
            self.making(def, MIRInstKind::Load { from, bytes }, line, col);
        }
    }

    // Bytes in the pool under a name that was chosen rather than numbered.
    // A descriptor is one of these: two bodies wanting the same type have to
    // name the same thing, and the pool's own numbering says nothing about
    // which type a run of bytes describes.
    pub(super) fn named(&mut self, symbol: String, bytes: Vec<u8>) {
        if self.out.pool.iter().any(|held| held.symbol == symbol) {
            return;
        }
        self.out.pool.push(MIRConstant { symbol, held: MIRConstBody::Bytes(bytes) });
    }

    // Somewhere to put a literal that does not fit in an instruction.
    pub(super) fn pooled(&mut self, bytes: Vec<u8>) -> String {
        let want = MIRConstBody::Bytes(bytes);
        if let Some(held) = self.out.pool.iter().find(|held| held.held == want) {
            return held.symbol.clone();
        }
        let symbol = super::runtime::text(self.out.pool.len());
        self.out.pool.push(MIRConstant { symbol: symbol.clone(), held: want });
        symbol
    }

    // A run of addresses under a name, which is what a trait object's table
    // is. Named rather than numbered and deduplicated by the name, as a
    // descriptor is: two coercions of one type to one trait want the one
    // table, and which table it is, is what the name says.
    pub(super) fn table(&mut self, symbol: String, names: Vec<String>) {
        if self.out.pool.iter().any(|held| held.symbol == symbol) {
            return;
        }
        self.out.pool.push(MIRConstant { symbol, held: MIRConstBody::Words(names) });
    }
}

// Every value in a body that an `*Addr` instruction made, which is every value
// holding an address rather than what is at one. Read off the instructions
// because a `SIRValue` carries only a type, and the type of one of these is
// the type of the place and not of the register.
fn addresses(source: &SIRBody) -> HashSet<SIRValueId> {
    let mut out = HashSet::new();
    for block in &source.blocks {
        for inst in &block.insts {
            let held = match inst.def {
                Some(held) => held,
                None => continue,
            };
            if matches!(
                inst.kind,
                SIRInstKind::Addr(_)
                    | SIRInstKind::ItemAddr(_)
                    | SIRInstKind::SelfAddr
                    | SIRInstKind::FieldAddr { .. }
                    | SIRInstKind::TupleAddr { .. }
                    | SIRInstKind::IndexAddr { .. }
            ) {
                out.insert(held);
            }
        }
    }
    out
}

// Whether the top bit of one of these means a sign. It decides which of two
// instructions a division, a shift and an ordering become, so it is asked once
// here rather than guessed at four call sites.
fn signed(p: TIRPrim) -> bool {
    use TIRPrim::*;
    matches!(p, I8 | I16 | I32 | I64 | I128)
}

#[cfg(test)]
mod tests;
