// Everything that becomes a call, and the one protocol that mostly does not.
//
// A machine has a call and nothing else. So a method is a call, a map being
// built is a call, a release at the end of a scope is a call, and after this
// file none of those three is a thing the compiler has a case for. That is the
// whole of what lowering them means: `mir::runtime` says what the names are,
// and this says what the arguments are and in what order.
//
// The exception is the `for` cursor. Its four instructions are a protocol over
// a closed set -- an array, a run, a `Range`, a `Set`, a `HashSet` (§5) -- and
// three of those five are walked by counting. Turning `at + 1` into a call to
// something that adds one would be paying for a call to add one, so the counted
// three are written out here and only the two the library owns become calls.
//
// The cursor is a number and it starts at -1, which is what the SIR means by
// "the cursor `Start` gives back stands *before* the first, so that advancing
// is the first thing every turn does". Every turn steps and then tests, so the
// first step lands on nought. That convention is what makes `IterStart` need no
// operand and no call: -1 is -1 whatever is being walked.

use crate::sir::sir_nodes::*;
use crate::tir::ttir_nodes::{TTIRCaptureMode, TTIRItemId, TTIRItemKind, Ty, TyId};

use super::super::mir_nodes::*;
use super::super::runtime;
use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn calling(&mut self, inst: &SIRInst, at: SIRBlockId, i: usize) {
        let (line, col) = (inst.line, inst.col);

        // The two that make nothing: a release runs and answers with nothing.
        match &inst.kind {
            SIRInstKind::Drop(value) => {
                let ty = self.ty_of(*value);
                let held = self.addressed(*value, line, col);
                self.release(held, ty, line, col);
                return;
            }
            SIRInstKind::DropSlot(slot) => {
                let ty = self.made.sir.bodies[self.body_at()].slots[*slot].ty;
                let slot = self.slot_of(*slot);
                let held = self.push(MIRInstKind::Frame(slot), line, col);
                self.release(held, ty, line, col);
                return;
            }
            _ => {}
        }

        let Some(value) = inst.def else {
            // A call whose answer nobody wanted. It still runs.
            if let SIRInstKind::Call { callee, args } = &inst.kind {
                let (to, args) = self.callee(*callee, args, line, col);
                self.effect(MIRInstKind::Call { to, args }, line, col);
            }
            return;
        };
        let def = self.of(value);

        match &inst.kind {
            SIRInstKind::Call { callee, args } => {
                let (to, args) = self.callee(*callee, args, line, col);
                let args = self.answering(value, args, line, col);
                self.making(def, MIRInstKind::Call { to, args }, line, col);
            }

            // A method names its declaration, so there is no value holding the
            // address and the symbol is the one `mono` worked out. The receiver
            // goes in front of the arguments, which is where a signature that
            // declared one already put it.
            SIRInstKind::Method { recv, item, args } => {
                // Through the table, where the receiver is a trait object.
                // Which body answers is not known here and is not meant to be:
                // the value carries a run of addresses beside it, the member's
                // *place* in the trait says which of them, and the receiver
                // handed over is the value the object was made from.
                if let Some(slot) = self.member_at(*recv, *item) {
                    let word = self.word();
                    let pair = self.of(*recv);
                    let data = self.push(MIRInstKind::Load { from: pair, bytes: word }, line, col);
                    let second =
                        self.push(MIRInstKind::Offset { base: pair, bytes: word as i64 },
                                  line, col);
                    let table =
                        self.push(MIRInstKind::Load { from: second, bytes: word }, line, col);
                    let entry = self.push(
                        MIRInstKind::Offset { base: table, bytes: (slot * word) as i64 },
                        line,
                        col,
                    );
                    let code =
                        self.push(MIRInstKind::Load { from: entry, bytes: word }, line, col);
                    let mut held = vec![data];
                    held.extend(args.iter().map(|&arg| self.of(arg)));
                    let held = self.answering(value, held, line, col);
                    self.making(
                        def,
                        MIRInstKind::Call { to: MIRCallee::Reg(code), args: held },
                        line,
                        col,
                    );
                    return;
                }
                let name = self.symbol_at(at, i).unwrap_or_default();
                let mut held = vec![self.of(*recv)];
                held.extend(args.iter().map(|&arg| self.of(arg)));
                let held = self.answering(value, held, line, col);
                self.making(
                    def,
                    MIRInstKind::Call { to: MIRCallee::Symbol(name), args: held },
                    line,
                    col,
                );
            }

            // The two descriptors are what let one `__rt_map_insert` serve
            // every `K` and `V` in the program. The key arrives in one
            // register and the register says nothing about what is in it; the
            // descriptor says how wide it is, whether it is the value or its
            // address, and how to order and hash it.
            //
            // They come from the map's own type and not from the entries,
            // because `{:}` has no entries and still has a key type.
            SIRInstKind::Map { hashed, entries } => {
                let (hashed, entries) = (*hashed, entries.clone());
                let args = self.container_args(value);
                let key = self.shape_arg(args.first().copied(), line, col);
                let held = self.shape_arg(args.get(1).copied(), line, col);
                let made = self.push(
                    MIRInstKind::Call {
                        to:   MIRCallee::Symbol(runtime::map_new(hashed).to_string()),
                        args: vec![key, held],
                    },
                    line,
                    col,
                );
                self.handle(def, made, value, line, col);
                let table = self.of(value);
                for (key, held) in entries {
                    let (key, held) = (self.of(key), self.of(held));
                    self.effect(
                        MIRInstKind::Call {
                            to:   MIRCallee::Symbol(runtime::map_insert(hashed).to_string()),
                            args: vec![table, key, held],
                        },
                        line,
                        col,
                    );
                }
            }

            SIRInstKind::Set { hashed, elems } => {
                let (hashed, elems) = (*hashed, elems.clone());
                let args = self.container_args(value);
                let elem = self.shape_arg(args.first().copied(), line, col);
                let made = self.push(
                    MIRInstKind::Call {
                        to:   MIRCallee::Symbol(runtime::set_new(hashed).to_string()),
                        args: vec![elem],
                    },
                    line,
                    col,
                );
                self.handle(def, made, value, line, col);
                let table = self.of(value);
                for one in elems {
                    let one = self.of(one);
                    self.effect(
                        MIRInstKind::Call {
                            to:   MIRCallee::Symbol(runtime::set_insert(hashed).to_string()),
                            args: vec![table, one],
                        },
                        line,
                        col,
                    );
                }
            }

            SIRInstKind::Closure { captures, .. } => {
                let captures = captures.clone();
                let name = self.symbol_at(at, i).unwrap_or_default();
                self.closure(def, &name, &captures, value, line, col);
            }

            // ---- The cursor ------------------------------------------------

            // Before the first, whatever is being walked.
            SIRInstKind::IterStart => {
                self.making(def, MIRInstKind::Const(MIRConst::Int(-1)), line, col);
            }

            SIRInstKind::IterValid { iter, at: cursor } => {
                self.valid(def, *iter, *cursor, line, col)
            }
            SIRInstKind::IterElem { iter, at: cursor } => {
                self.elem(def, *iter, *cursor, value, line, col)
            }
            SIRInstKind::IterStep { iter, at: cursor } => {
                self.step(def, *iter, *cursor, line, col)
            }

            _ => self.making(def, MIRInstKind::Undef, line, col),
        }
    }

    // Room for an answer too big for a register, handed over in front of the
    // written arguments.
    //
    // The other half of `Lowerer`'s `sret`: a body that answers with a value
    // held by its address writes it where the caller says and hands that
    // address back, so the caller has to say -- and the room has to be the
    // caller's, because the callee's dies at its epilogue.
    //
    // Which calls those are is the same question asked from the other side:
    // what the call *answers with* is the type of the value it makes, so a
    // call whose answer is `indirect` is a call to a body whose `Return` was.
    // Nothing has to look the callee up.
    fn answering(
        &mut self,
        value: SIRValueId,
        args: Vec<MIRRegId>,
        line: usize,
        col: usize,
    ) -> Vec<MIRRegId> {
        let ty = self.ty_of(value);
        if !self.indirect(ty) {
            return args;
        }
        let held = self.laid(ty);
        let name = format!("${}", self.frame_len());
        let slot = self.slot(name, held.bytes.max(1), held.align.max(1));
        let room = self.push(MIRInstKind::Frame(slot), line, col);
        let mut out = vec![room];
        out.extend(args);
        out
    }

    // ---- What a call names -------------------------------------------------

    // A declaration, or an address worked out while it ran.
    fn callee(
        &mut self,
        callee: SIRValueId,
        args: &[SIRValueId],
        line: usize,
        col: usize,
    ) -> (MIRCallee, Vec<MIRRegId>) {
        let held: Vec<MIRRegId> = args.iter().map(|&arg| self.of(arg)).collect();
        if let Some(name) = self.symbol_value(callee) {
            return (MIRCallee::Symbol(name), held);
        }
        // A fn held as a value is a pointer to the code and a pointer to what
        // it captured, and this hands over both: the first is what is called
        // and the second goes in after the written arguments, as one more of
        // them.
        //
        // **Last, and not first.** A declared fn is handed round as a value
        // like a closure is and has no environment at all, so the same call
        // has to reach either -- and what tells them apart is not known here,
        // a fn value being a pair whichever it came from. An argument the
        // callee never declared is harmless where it is last: every ABI here
        // has the caller lay the arguments out and none of the three has the
        // callee count them. In front it would shift every other argument
        // along by one and a declared fn would read its first as its second.
        //
        // So the convention is: a fn value is called with its environment
        // after the arguments, a closure that captured something declares a
        // parameter for it (`sema::lower::closures`), and everything else
        // ignores a word it was passed.
        let from = self.of(callee);
        let word = self.word();
        let code = self.push(MIRInstKind::Load { from, bytes: word }, line, col);
        let second = self.push(MIRInstKind::Offset { base: from, bytes: word as i64 }, line, col);
        let env = self.push(MIRInstKind::Load { from: second, bytes: word }, line, col);
        let mut held = held;
        held.push(env);
        (MIRCallee::Reg(code), held)
    }

    // Where in the table a method stands, where the receiver is a trait object
    // at all. `None` for every ordinary call, which is what leaves the direct
    // one the default.
    //
    // The place and not the name: a table is a run of addresses and nothing
    // says which is which, so the two ends agree by counting. `mir::mono`
    // fills it in the trait's declaration order and this reads it in the same
    // order, and the trait is the one declaration both of them look at.
    fn member_at(&mut self, recv: SIRValueId, item: TTIRItemId) -> Option<usize> {
        let ty = self.ty_of(recv);
        let (Ty::Ref { inner, .. } | Ty::Ptr(inner)) = self.made.ttir.types.get(ty)? else {
            return None;
        };
        let Ty::Dyn(of) = self.made.ttir.types.get(*inner)? else { return None };
        let TTIRItemKind::Trait { members, .. } = &self.made.ttir.items.get(*of)?.kind else {
            return None;
        };
        members.iter().position(|&held| held == item)
    }

    // ---- Closures ----------------------------------------------------------

    // Room for what it captured, then the pair that is the value: where the
    // code is, and where the captures are.
    fn closure(
        &mut self,
        def: MIRRegId,
        name: &str,
        captures: &[crate::tir::ttir_nodes::TTIRCapture],
        value: SIRValueId,
        line: usize,
        col: usize,
    ) {
        // One that took nothing is a fn like any other: there is nothing to
        // put in an environment, so it gets the second word every declared fn
        // handed round as a value gets, and its body declares no parameter to
        // read one out of (`sema::lower::closures`). An allocation for a run
        // of no captures is one the collector would walk for nothing.
        if captures.is_empty() {
            return self.paired(def, name.to_string(), line, col);
        }

        let word = self.word();
        let ty = self.ty_of(value);

        // The captures outlive the frame that made them -- that is what a
        // closure being returnable means -- so they cannot be a slot.
        let bytes = (captures.len() * word) as i64;
        let size = self.push(MIRInstKind::Const(MIRConst::Int(bytes)), line, col);
        // The collector's, and described: every word of it is an address. That
        // is what makes an environment reachable through the closure value
        // rather than leaked -- the second word of a fn value is this pointer,
        // and `mir::shape` calls both words of a fn value pointers.
        let shape = self.env_shape(captures.len(), line, col);
        let env = self.push(
            MIRInstKind::Call {
                to:   MIRCallee::Symbol(runtime::GC_ALLOC.to_string()),
                args: vec![size, shape],
            },
            line,
            col,
        );

        // Each capture is the enclosing body's local, which is a slot of this
        // frame, and every word of the environment is the address of one
        // capture. Which address depends on how it was taken, and the two are
        // what `&` and `move` mean:
        //
        //   - by reference, the slot's own address. The body reads and writes
        //     the name outside, which is "reading one takes a `&` of it and
        //     assigning to one takes a `*`" (§5) -- one address answering both.
        //
        //   - by value, the address of a copy the collector holds. A `move`
        //     closure owns what it took, so writing through to the frame would
        //     be wrong even while that frame is there -- and the frame is
        //     exactly what a returned closure outlives.
        //
        // Both are one word and both are an address, which is what keeps the
        // descriptor above honest: the collector walks an environment as a run
        // of pointers and finds one either way.
        for (index, capture) in captures.iter().enumerate() {
            let Some(slot) = self.slot_named(capture.outer) else { continue };
            let held = self.push(MIRInstKind::Frame(slot), line, col);
            let held = match (capture.mode, self.ty_named(capture.outer)) {
                (TTIRCaptureMode::Value, Some(ty)) => self.boxed(ty, held, line, col),
                _ => held,
            };
            let to = self.push(
                MIRInstKind::Offset { base: env, bytes: (index * word) as i64 },
                line,
                col,
            );
            self.effect(MIRInstKind::Store { to, value: held, bytes: word }, line, col);
        }

        let held = self.laid(ty);
        let room = format!("${}", self.frame_len());
        let slot = self.slot(room, held.bytes.max(word * 2), held.align.max(word));
        self.making(def, MIRInstKind::Frame(slot), line, col);
        let code = self.push(MIRInstKind::Symbol(name.to_string()), line, col);
        self.effect(MIRInstKind::Store { to: def, value: code, bytes: word }, line, col);
        let second =
            self.push(MIRInstKind::Offset { base: def, bytes: word as i64 }, line, col);
        self.effect(MIRInstKind::Store { to: second, value: env, bytes: word }, line, col);
    }

    // A copy of what is at an address, in room of the collector's rather than
    // this frame's, and the address of that copy. What a `move` capture goes
    // into: the value is the closure's own from here, and the closure may
    // outlive every frame standing now.
    //
    // Described by its own type and not as a run of pointers, unlike the
    // environment holding it -- this is one value of one type, and what the
    // collector has to walk into is whatever that type says.
    fn boxed(&mut self, ty: TyId, from: MIRRegId, line: usize, col: usize) -> MIRRegId {
        let bytes = self.bytes_of(ty).max(1);
        let size = self.push(MIRInstKind::Const(MIRConst::Int(bytes as i64)), line, col);
        let shape = self.shape_reg(ty, line, col);
        let to = self.push(
            MIRInstKind::Call {
                to:   MIRCallee::Symbol(runtime::GC_ALLOC.to_string()),
                args: vec![size, shape],
            },
            line,
            col,
        );
        self.effect(MIRInstKind::Copy { to, from, bytes }, line, col);
        to
    }

    // The same pair for a fn that captured nothing: where the code is, and a
    // second word that is no environment. Split out of `closure` above rather
    // than written twice, because the two disagreeing about which word is
    // which is exactly the kind of thing that runs and gives an answer.
    pub(super) fn paired(
        &mut self,
        def: MIRRegId,
        name: String,
        line: usize,
        col: usize,
    ) {
        let word = self.word();
        let room = format!("${}", self.frame_len());
        let slot = self.slot(room, word * 2, word);
        self.making(def, MIRInstKind::Frame(slot), line, col);
        let code = self.push(MIRInstKind::Symbol(name), line, col);
        self.effect(MIRInstKind::Store { to: def, value: code, bytes: word }, line, col);
        // Nothing captured, so nothing to point at. It is written rather than
        // left as it was found: a fn value is copied whole, and a word of
        // whatever the frame held last is a word the collector would follow.
        let none = self.push(MIRInstKind::Const(MIRConst::Int(0)), line, col);
        let second =
            self.push(MIRInstKind::Offset { base: def, bytes: word as i64 }, line, col);
        self.effect(MIRInstKind::Store { to: second, value: none, bytes: word }, line, col);
    }

    // ---- What a container was made of --------------------------------------

    // The type arguments of a `Map<K, V>` or a `Set<T>`. Taken from the type
    // rather than from the entries, because `{:}` and `{,}` have no entries
    // and still have a key type -- and because a literal whose entries all
    // turned out to be `never` would say the wrong thing.
    fn container_args(&self, value: SIRValueId) -> Vec<TyId> {
        match self.made.ttir.types.get(self.ty_of(value)) {
            Some(Ty::Named { args, .. }) => args.clone(),
            _ => Vec::new(),
        }
    }

    // A descriptor for one of them, or a nought where the type says nothing --
    // which the runtime takes as "nothing was said" and refuses to make a
    // container for, rather than reading a descriptor that is not there.
    fn shape_arg(&mut self, ty: Option<TyId>, line: usize, col: usize) -> MIRRegId {
        match ty {
            Some(ty) => self.shape_reg(ty, line, col),
            None => self.push(MIRInstKind::Const(MIRConst::Int(0)), line, col),
        }
    }

    // Where the handle a constructor gave back goes.
    //
    // It is one word. The register the lowering spoke for may not be a
    // register for one word: with no library declaring `Map`, the type is an
    // error and falls on the one-word fallback by accident, but a library
    // declaring `struct Map<K, V> { h: ptr u8 }` makes it a structure -- and
    // an indirect register holds an *address* by convention, so the handle
    // would be read as one. So where the type is indirect the handle is stored
    // into the first word of a slot and the register holds that slot.
    fn handle(
        &mut self,
        def: MIRRegId,
        made: MIRRegId,
        value: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(value);
        if !self.indirect(ty) {
            self.making(def, MIRInstKind::Move(made), line, col);
            return;
        }
        let word = self.word();
        let held = self.laid(ty);
        let name = format!("${}", self.frame_len());
        let slot = self.slot(name, held.bytes.max(word), held.align.max(word));
        self.making(def, MIRInstKind::Frame(slot), line, col);
        self.effect(MIRInstKind::Store { to: def, value: made, bytes: word }, line, col);
    }

    // ---- Releases ----------------------------------------------------------

    // One routine per type, named after the type -- see `mir::runtime::glue`.
    //
    // The type is remembered as well as spelled: what the routine *does* is
    // written by `glue`, which runs once every body has been walked, and the
    // only way it knows which routines a program wants is that they were asked
    // for here.
    fn release(&mut self, held: MIRRegId, ty: TyId, line: usize, col: usize) {
        let spelled = self.spell(ty);
        self.wants(ty);
        self.effect(
            MIRInstKind::Call {
                to:   MIRCallee::Symbol(runtime::glue(&spelled)),
                args: vec![held],
            },
            line,
            col,
        );
    }

    // An address for something a release has to be handed. Whatever is already
    // reached by its address is already one; a number is not, so it is put
    // somewhere it can be pointed at.
    fn addressed(&mut self, value: SIRValueId, line: usize, col: usize) -> MIRRegId {
        let ty = self.ty_of(value);
        if self.indirect(ty) {
            return self.of(value);
        }
        let held = self.laid(ty);
        let name = format!("${}", self.frame_len());
        let slot = self.slot(name, held.bytes, held.align);
        let to = self.push(MIRInstKind::Frame(slot), line, col);
        self.put(to, value, line, col);
        to
    }

    // ---- Walking one -------------------------------------------------------

    // Whether there is another. Counted where it can be counted, and the
    // library's where the library owns what is being walked.
    fn valid(
        &mut self,
        def: MIRRegId,
        iter: SIRValueId,
        cursor: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(iter);
        if self.library_walk(ty) {
            let (iter, cursor) = (self.of(iter), self.of(cursor));
            self.making(
                def,
                MIRInstKind::Call {
                    to:   MIRCallee::Symbol(runtime::ITER_VALID.to_string()),
                    args: vec![iter, cursor],
                },
                line,
                col,
            );
            return;
        }
        let len = self.length(iter, line, col);
        let cursor = self.of(cursor);
        self.making(
            def,
            MIRInstKind::Cmp { op: MIRCmpOp::SLt, lhs: cursor, rhs: len },
            line,
            col,
        );
    }

    fn elem(
        &mut self,
        def: MIRRegId,
        iter: SIRValueId,
        cursor: SIRValueId,
        value: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(iter);
        if self.library_walk(ty) {
            let (held, at) = (self.of(iter), self.of(cursor));
            self.making(
                def,
                MIRInstKind::Call {
                    to:   MIRCallee::Symbol(runtime::ITER_ELEM.to_string()),
                    args: vec![held, at],
                },
                line,
                col,
            );
            return;
        }
        // A range yields its own numbers rather than what is at an address, so
        // the element is the far end of an addition and not of a load.
        if self.is_range(ty) {
            let base = self.of(iter);
            let bytes = self.bytes_of(ty).max(1) / 2;
            let start = self.push(MIRInstKind::Load { from: base, bytes }, line, col);
            let at = self.of(cursor);
            self.making(
                def,
                MIRInstKind::Bin { op: MIRBinOp::Add, lhs: start, rhs: at },
                line,
                col,
            );
            return;
        }
        let base = self.elements(iter, line, col);
        let elem = self.holds(ty).unwrap_or_else(|| self.ty_of(value));
        let scale = self.stride_of(elem);
        let index = self.of(cursor);
        let held = self.push(MIRInstKind::Scaled { base, index, scale }, line, col);
        let want = self.ty_of(value);
        self.take(def, held, want, line, col);
    }

    fn step(
        &mut self,
        def: MIRRegId,
        iter: SIRValueId,
        cursor: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(iter);
        if self.library_walk(ty) {
            let (held, at) = (self.of(iter), self.of(cursor));
            self.making(
                def,
                MIRInstKind::Call {
                    to:   MIRCallee::Symbol(runtime::ITER_STEP.to_string()),
                    args: vec![held, at],
                },
                line,
                col,
            );
            return;
        }
        let at = self.of(cursor);
        let one = self.push(MIRInstKind::Const(MIRConst::Int(1)), line, col);
        self.making(def, MIRInstKind::Bin { op: MIRBinOp::Add, lhs: at, rhs: one }, line, col);
    }

    // How many there are, for the three that can be counted. An array knows in
    // its type; a run and a string carry it beside the pointer; a range is the
    // far end less the near one.
    fn length(&mut self, iter: SIRValueId, line: usize, col: usize) -> MIRRegId {
        let ty = self.ty_of(iter);
        let word = self.word();
        match self.made.ttir.types.get(self.bare(ty)) {
            Some(Ty::Array { len, .. }) => {
                let len = *len as i64;
                self.push(MIRInstKind::Const(MIRConst::Int(len)), line, col)
            }
            Some(Ty::Run(_)) | Some(Ty::Prim(crate::tir::tir_nodes::TIRPrim::Str)) => {
                let base = self.of(iter);
                let at =
                    self.push(MIRInstKind::Offset { base, bytes: word as i64 }, line, col);
                self.push(MIRInstKind::Load { from: at, bytes: word }, line, col)
            }
            _ => {
                // A range: the far end less the near one, which is how many
                // turns it has.
                let base = self.of(iter);
                let bytes = self.bytes_of(ty).max(2) / 2;
                let start = self.push(MIRInstKind::Load { from: base, bytes }, line, col);
                let at =
                    self.push(MIRInstKind::Offset { base, bytes: bytes as i64 }, line, col);
                let end = self.push(MIRInstKind::Load { from: at, bytes }, line, col);
                self.push(
                    MIRInstKind::Bin { op: MIRBinOp::Sub, lhs: end, rhs: start },
                    line,
                    col,
                )
            }
        }
    }

    // ---- Which of the closed set it is -------------------------------------

    // Whether what is being walked is one the library owns rather than one that
    // can be counted through.
    fn library_walk(&mut self, ty: TyId) -> bool {
        matches!(
            self.named_as(ty).as_deref(),
            Some("Set") | Some("HashSet") | Some("Map") | Some("HashMap")
        )
    }

    fn is_range(&mut self, ty: TyId) -> bool {
        self.named_as(ty).as_deref() == Some("Range")
    }

    fn named_as(&self, ty: TyId) -> Option<String> {
        let Some(Ty::Named { item, .. }) = self.made.ttir.types.get(self.bare(ty)) else {
            return None;
        };
        match &self.made.ttir.items.get(*item)?.kind {
            TTIRItemKind::Struct { name, .. } | TTIRItemKind::Enum { name, .. } => {
                Some(name.clone())
            }
            _ => None,
        }
    }

    // What a run or an array holds one of.
    fn holds(&self, ty: TyId) -> Option<TyId> {
        match self.made.ttir.types.get(self.bare(ty))? {
            Ty::Run(elem) | Ty::Array { elem, .. } => Some(*elem),
            _ => None,
        }
    }

}
