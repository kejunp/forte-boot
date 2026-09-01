// What releasing a value comes to, written out as a body per type.
//
// `mir::runtime` says why there is one routine per type rather than one for
// all of them: what has to happen depends entirely on what is at the address,
// and the address does not say. So the type is in the name, and this is what
// stands under the name. Until it did, `__D12drop::Handle` was a call to
// nothing -- the one group of symbols in `mir::runtime` the runtime crate does
// not define, because a release is a thing the *compiler* has to build a body
// for out of a declaration only it can see.
//
// A routine takes one address and answers with nothing, which is the shape
// `Lowerer::release` has always emitted. What it does is three things in this
// order:
//
//   1. the type's own `Drop::drop`, where one was written;
//   2. a release of every part that has one -- a field, a member, a payload,
//      an element;
//   3. return.
//
// **The order is Rust's and it is the only one that works.** The user's `drop`
// is handed the whole value and may read any of it, so it has to run while the
// parts are still there. Releasing a field first and then handing the husk to
// `drop` would hand it a field that has already gone.
//
// **Which parts have one is `Copies::drops`**, the same predicate `gir::drops`
// used to decide where a release goes at all. That the two agree is not a
// nicety: a type that pass called droppable and this one did not would be a
// call to a routine nothing emitted, and one this called droppable and that
// did not would be a routine nothing calls. Asking one predicate twice is what
// makes that impossible rather than merely unlikely.
//
// **An enum reads its tag.** Which variant is in there is not a fact about the
// type, so the routine is not a straight line: it is a comparison and a branch
// per variant that has anything to release, and the payload of the variant
// that matched is what gets released. That is the one place a glue body has
// more than one block.
//
// **An array loops.** Unrolling would be shorter to write and would make
// `[T; 10000]` a body of ten thousand calls. The loop counts through a frame
// slot rather than a phi -- the graph is in SSA and a slot is not a value, so
// counting in one costs a load and a store per turn and costs no reasoning at
// all.
//
// What is *not* here: a `once fn`. `Copies::drops` calls one droppable because
// "a closure that took what it captured is holding it", and which types those
// were is not in the fn type -- so there is nothing here that could name them.
// It is not a leak any more: an environment is `__rt_gc_alloc`'s since the
// collector landed, and the collector reaches it through the closure value.
// The routine is emitted and is empty, and that is the whole answer.

use crate::sema::borrows::copies::name_of;
use crate::tir::ttir_nodes::{TTIRItemId, TTIRItemKind, TTIRPayload, Ty, TyId};

use super::super::layout::Shape;
use super::super::mir_nodes::*;
use super::super::runtime;
use super::{Builder, Lowerer};

// A glue body is written, not lowered, so it has no source to be at. One and
// one is what every line of one says, which is at least a place a message can
// point at that is not nowhere.
const AT: (usize, usize) = (1, 1);

impl<'a> Lowerer<'a> {
    // Remember that a release of this type was asked for.
    pub(super) fn wants(&mut self, ty: TyId) {
        if !self.wanted.contains(&ty) {
            self.wanted.push(ty);
        }
    }

    // A body for every release the program asks for, and for every release
    // those releases ask for in turn.
    //
    // A worklist rather than a walk, because a routine is written by emitting
    // calls to other routines and there is no order over the types that has
    // them all in hand first. It ends because the set of types is finite and
    // each is written once.
    pub(super) fn glue(&mut self) {
        while let Some(ty) = self.wanted.pop() {
            let symbol = runtime::glue(&self.spell(ty));
            if !self.written.insert(symbol.clone()) {
                continue;
            }
            let built = self.one_glue(ty, symbol);
            self.out.bodies.push(built);
        }
    }

    fn one_glue(&mut self, ty: TyId, symbol: String) -> MIRBody {
        self.b = Builder::default();
        let entry = self.fresh_block();
        self.b.current = entry;

        // The one parameter: where the value is.
        let at = self.temp(AT.0, AT.1);
        self.b.params = vec![at];

        self.own_drop(ty, at);
        self.parts(ty, at);

        let last = self.b.current;
        self.b.blocks[last].term = MIRTerm::Return(None);

        let built = std::mem::take(&mut self.b);
        MIRBody {
            symbol,
            entry,
            blocks: built.blocks,
            regs: built.regs,
            frame: built.frame,
            params: built.params,
        }
    }

    // ---- What the declaration itself said --------------------------------------

    // The `drop` of an `impl Drop for T`, where one was written. It is handed
    // the whole value, before any part of it has gone.
    fn own_drop(&mut self, ty: TyId, at: MIRRegId) {
        let Some(item) = self.declared(ty) else { return };
        let Some(held) = self.drop_method(item) else { return };
        let Some(name) = self.mangler.symbol_of(held, &self.made.ttir) else { return };
        self.effect(
            MIRInstKind::Call { to: MIRCallee::Symbol(name), args: vec![at] },
            AT.0,
            AT.1,
        );
    }

    // The `drop` member of the `impl Drop` written for this declaration, if
    // there is one. Found by the name of the trait, which is how `Copy` and
    // `Drop` are found everywhere in this compiler -- §2 says those two are
    // known by their names and nothing else here resolves a trait that way.
    fn drop_method(&self, of: TTIRItemId) -> Option<TTIRItemId> {
        for item in &self.made.ttir.items {
            let TTIRItemKind::Impl { ty, of: Some(held), members, .. } = &item.kind else {
                continue;
            };
            if name_of(*held, &self.made.ttir) != "Drop" {
                continue;
            }
            let Some(Ty::Named { item: named, .. }) = self.made.ttir.types.get(*ty) else {
                continue;
            };
            if *named != of {
                continue;
            }
            for &member in members {
                if let TTIRItemKind::Fn(f) = &self.made.ttir.items[member].kind {
                    if f.name == "drop" {
                        return Some(member);
                    }
                }
            }
        }
        None
    }

    fn declared(&self, ty: TyId) -> Option<TTIRItemId> {
        match self.made.ttir.types.get(ty) {
            Some(Ty::Named { item, .. }) => Some(*item),
            _ => None,
        }
    }

    // ---- And what it holds -----------------------------------------------------

    fn parts(&mut self, ty: TyId, at: MIRRegId) {
        let held = self.made.ttir.types.get(ty).cloned();
        match held {
            Some(Ty::Tuple(members)) => self.each(&members, ty, at),
            Some(Ty::Array { elem, len }) => self.each_element(elem, len, at),
            Some(Ty::Named { item, args, .. }) => self.named_parts(ty, item, &args, at),
            // A reference, a pointer, a run and a `gc` value refer to
            // something owned somewhere else; a primitive holds nothing; a
            // `once fn`'s captures are the collector's. None of the five has a
            // part this could name -- see the header.
            _ => {}
        }
    }

    fn named_parts(&mut self, ty: TyId, item: TTIRItemId, args: &[TyId], at: MIRRegId) {
        let kind = self.made.ttir.items.get(item).map(|held| held.kind.clone());
        match kind {
            Some(TTIRItemKind::Struct { fields, .. }) => {
                let held: Vec<TyId> =
                    fields.iter().map(|f| self.standing(f.ty, args)).collect();
                self.each(&held, ty, at);
            }
            Some(TTIRItemKind::Enum { variants, .. }) => {
                let held: Vec<Vec<TyId>> = variants
                    .iter()
                    .map(|v| {
                        payload_types(&v.payload)
                            .iter()
                            .map(|&one| self.standing(one, args))
                            .collect()
                    })
                    .collect();
                let values: Vec<i64> = variants.iter().map(|v| v.value).collect();
                self.by_variant(ty, &held, &values, at);
            }
            _ => {}
        }
    }

    // One release per member that has one, at the offset the layout worked
    // out. A member with nothing to release is skipped rather than handed to a
    // routine that returns at once, which is what keeps a structure of numbers
    // from becoming a routine per field.
    fn each(&mut self, members: &[TyId], of: TyId, at: MIRRegId) {
        let Some(laid) = self.layouts.of(of) else { return };
        let Shape::Fields(offsets) = laid.shape else { return };
        for (index, &one) in members.iter().enumerate() {
            let Some(&off) = offsets.get(index) else { continue };
            self.release_part(one, at, off as i64);
        }
    }

    fn release_part(&mut self, ty: TyId, at: MIRRegId, offset: i64) {
        if !self.releases(ty) {
            return;
        }
        let held = self.push(MIRInstKind::Offset { base: at, bytes: offset }, AT.0, AT.1);
        self.wants(ty);
        let name = runtime::glue(&self.spell(ty));
        self.effect(
            MIRInstKind::Call { to: MIRCallee::Symbol(name), args: vec![held] },
            AT.0,
            AT.1,
        );
    }

    // ---- An enum ---------------------------------------------------------------

    // Read the tag, then a comparison and a branch per variant that has
    // anything to release. Everything that matched nothing falls through to
    // the return, which is where a variant with no payload was always going.
    fn by_variant(&mut self, ty: TyId, payloads: &[Vec<TyId>], values: &[i64], at: MIRRegId) {
        let Some(laid) = self.layouts.of(ty) else { return };
        let Shape::Tagged { tag, variants } = laid.shape else { return };
        if !payloads.iter().flatten().any(|&one| self.releases(one)) {
            return;
        }
        let held = self.push(MIRInstKind::Load { from: at, bytes: tag }, AT.0, AT.1);

        for (which, members) in payloads.iter().enumerate() {
            if !members.iter().any(|&one| self.releases(one)) {
                continue;
            }
            let Some(offsets) = variants.get(which).cloned() else { continue };
            let want = values.get(which).copied().unwrap_or(which as i64);

            let number = self.push(MIRInstKind::Const(MIRConst::Int(want)), AT.0, AT.1);
            let same = self.push(
                MIRInstKind::Cmp { op: MIRCmpOp::Eq, lhs: held, rhs: number },
                AT.0,
                AT.1,
            );
            let body = self.fresh_block();
            let after = self.fresh_block();
            let from = self.b.current;
            self.b.blocks[from].term =
                MIRTerm::Branch { cond: same, then: body, els: after };

            self.b.current = body;
            for (index, &one) in members.iter().enumerate() {
                let Some(&off) = offsets.get(index) else { continue };
                self.release_part(one, at, off as i64);
            }
            self.b.blocks[body].term = MIRTerm::Goto(after);
            self.b.current = after;
        }
    }

    // ---- An array --------------------------------------------------------------

    // A loop, counted in a frame slot.
    //
    //     .entry   i = 0                    -> .test
    //     .test    i < len ?                -> .body : .done
    //     .body    release at + i * stride  -> .test
    //     .done
    //
    // The counter is a slot and not a value because the graph is in SSA: a
    // value written on two paths wants a phi, and a phi in a body written by
    // hand is a thing to get wrong. A slot is not a value and needs none, and
    // what it costs is a load and a store per turn of a loop that is already
    // making a call.
    fn each_element(&mut self, elem: TyId, len: u64, at: MIRRegId) {
        if !self.releases(elem) || len == 0 {
            return;
        }
        let Some(stride) = self.layouts.stride(elem) else { return };
        let word = self.machine.word;
        let count = self.slot("$i".to_string(), word, word);

        let zero = self.push(MIRInstKind::Const(MIRConst::Int(0)), AT.0, AT.1);
        let room = self.push(MIRInstKind::Frame(count), AT.0, AT.1);
        self.effect(
            MIRInstKind::Store { to: room, value: zero, bytes: word },
            AT.0,
            AT.1,
        );

        let (test, body, done) =
            (self.fresh_block(), self.fresh_block(), self.fresh_block());
        let from = self.b.current;
        self.b.blocks[from].term = MIRTerm::Goto(test);

        self.b.current = test;
        let room = self.push(MIRInstKind::Frame(count), AT.0, AT.1);
        let held = self.push(MIRInstKind::Load { from: room, bytes: word }, AT.0, AT.1);
        let end = self.push(MIRInstKind::Const(MIRConst::Int(len as i64)), AT.0, AT.1);
        let more = self.push(
            MIRInstKind::Cmp { op: MIRCmpOp::SLt, lhs: held, rhs: end },
            AT.0,
            AT.1,
        );
        self.b.blocks[test].term = MIRTerm::Branch { cond: more, then: body, els: done };

        self.b.current = body;
        let room = self.push(MIRInstKind::Frame(count), AT.0, AT.1);
        let index = self.push(MIRInstKind::Load { from: room, bytes: word }, AT.0, AT.1);
        let one = self.push(
            MIRInstKind::Scaled { base: at, index, scale: stride },
            AT.0,
            AT.1,
        );
        self.wants(elem);
        let name = runtime::glue(&self.spell(elem));
        self.effect(
            MIRInstKind::Call { to: MIRCallee::Symbol(name), args: vec![one] },
            AT.0,
            AT.1,
        );
        let step = self.push(MIRInstKind::Const(MIRConst::Int(1)), AT.0, AT.1);
        let next = self.push(
            MIRInstKind::Bin { op: MIRBinOp::Add, lhs: index, rhs: step },
            AT.0,
            AT.1,
        );
        self.effect(
            MIRInstKind::Store { to: room, value: next, bytes: word },
            AT.0,
            AT.1,
        );
        self.b.blocks[body].term = MIRTerm::Goto(test);

        self.b.current = done;
    }

    // ---- The two questions asked of a type ------------------------------------

    // Whether a value of this type has anything to release, asked of the same
    // table `gir::drops` asked -- see the header.
    fn releases(&self, ty: TyId) -> bool {
        self.copies.drops(ty, &self.made.ttir, &[])
    }

    // What a declaration's field type is once the arguments at the use are put
    // in place of its parameters.
    //
    // One level, which is all a parameter needs: `Held<i32>`'s field of type
    // `T` is an `i32`, and the `i32` is already in the arena because the use
    // named it. A field of type `Vec<T>` would want `Vec<i32>` interned, and
    // this cannot intern -- the arena belongs to `mono` and arrives here
    // finished. Such a field is left alone and said out loud in `gaps`, which
    // is the honest half of a thing that cannot be reached today anyway:
    // `sema` does not give a generic struct literal its arguments, so a
    // generic struct cannot be built at all.
    fn standing(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        match self.made.ttir.types.get(ty) {
            Some(Ty::Param { index, name }) => match args.get(*index) {
                Some(&held) => held,
                None => {
                    let said = format!(
                        "a release of `{}` is not written: nothing says what `{}` stands for",
                        self.spell(ty),
                        name
                    );
                    if !self.gaps.contains(&said) {
                        self.gaps.push(said);
                    }
                    ty
                }
            },
            _ => ty,
        }
    }

    // ---- Building ---------------------------------------------------------------

    fn fresh_block(&mut self) -> MIRBlockId {
        self.b.blocks.push(MIRBlock {
            phis:  Vec::new(),
            insts: Vec::new(),
            term:  MIRTerm::Unreachable,
            line:  AT.0,
            col:   AT.1,
        });
        self.b.blocks.len() - 1
    }
}

fn payload_types(payload: &TTIRPayload) -> Vec<TyId> {
    match payload {
        TTIRPayload::None => Vec::new(),
        TTIRPayload::Tuple(parts) => parts.clone(),
        TTIRPayload::Named(fields) => fields.iter().map(|held| held.ty).collect(),
    }
}

#[cfg(test)]
mod tests;
