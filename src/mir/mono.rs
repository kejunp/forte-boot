// A generic written once, made once for each set of types it is used with.
//
//     SIR -> mono -> SIR
//
// This is the question §8 leaves open, answered: "What is not settled is what
// happens when a generic fn is compiled. If nothing monomorphises, one symbol
// is right; if something does, each instance wants its own and the arguments
// have to reach the name." Something does, and they do.
//
// The reason is `mir::layout` and it is not a preference. A machine reaches a
// field by counting bytes, and how many bytes a `T` takes is not a question
// with an answer -- so a body with a `T` still standing in it is a body nothing
// can emit. Either every use of a generic is compiled separately with the types
// filled in, or every generic value is put behind a pointer so that they are
// all one width. The first is chosen here. It is the one that costs code size
// and the one that leaves what a program does unchanged, and the second is a
// decision about the *language* -- a `T` that must be boxed is a `T` that
// cannot be a register -- which is not a decision a back end gets to make.
//
// Nothing is inferred that `sema` did not already work out. A generic's
// parameters are substituted at every use by `sema::lower::paths::instantiate`
// ("what it stands for is settled at the call and not at the declaration"), so
// by the time a value naming a fn reaches here its *type* is the concrete one.
// What the declaration says beside it still has the parameters in it. Matching
// the two recovers the arguments by their index, and no unification is needed
// to do it -- the answer is already there, in two pieces.
//
// So the walk is: start from every fn that takes no type parameters, because
// those are the ones a program can reach without being told anything; follow
// every name of a declaration out of them; and each time one turns out to be
// generic, make the instance the types ask for and follow that too. A closure
// goes wherever its enclosing body went, with the same arguments -- it is part
// of that body and not a declaration of its own.
//
// Two things stop it. An instance already made is not made twice, which is what
// keeps a recursive fn from being written into itself forever -- exactly the
// bound `sir::opt`'s inliner draws, and for the same reason. And a chain of
// instances that keeps making *new* types -- `f<T>` calling `f<Held<T>>` -- is
// not stopped by that at all, because every one of them is new. It is stopped
// by a depth, and it is the one thing here that turns a program down.
//
// That is worth saying plainly, because it breaks a rule the SIR states: "nothing
// after this refuses a program -- there is no diagnostic left to get wrong"
// (`sir::opt`). This does refuse one. The alternative is not to refuse it but to
// run out of memory instead, and a message is better than that. It is the only
// one, and `refused` is empty for every program that has an answer.

use std::collections::{HashMap, VecDeque};

use crate::sema::names::{part, Mangler};
use crate::sir::sir_nodes::*;
use crate::tir::ttir_nodes::{TTIRItemKind, TTIRProgram, Ty, TyId};

// How deep a chain of instances may go before it is taken to be one that does
// not end. Every instance in a chain is a use written inside the one before it,
// so this is a nesting depth in the source and not a call depth -- twenty is
// far past anything written on purpose.
const DEEPEST: usize = 20;

pub struct Made {
    // The same program, with the types the instances needed added to the arena.
    // Nothing else about it changes: no item is added, because an instance is a
    // body and not a declaration.
    pub ttir:      TTIRProgram,
    // One body per instance. The numbering is this pass's own -- one SIR body
    // becomes several -- so a `SIRBodyId` from before does not name the same
    // thing after.
    pub sir:       SIRProgram,
    // What each body of `sir` is called, by its id.
    pub symbols:   Vec<String>,
    // What the declaration named by one instruction is called, by where that
    // instruction is: the body, the block, and its place in the block.
    //
    // This is here because the SIR has nowhere to put it. An `Item` names a
    // declaration and a declaration is now several bodies, so the instruction
    // no longer says which -- and adding a field to say would be putting a
    // machine's question into the SIR's vocabulary. Keeping it beside is what
    // leaves `sir_nodes.rs` alone.
    pub symbol_of: HashMap<(SIRBodyId, SIRBlockId, usize), String>,
    // How many bodies were made from a declaration that took type parameters.
    pub instances: usize,
    // The chains that did not end. Empty for a program with an answer.
    pub refused:   Vec<String>,
}

// What a use said about the declaration it named, which is what the parameters
// are recovered from. Two shapes because there are two ways to name one: a
// value that holds the fn, and a method call that names it and hands over the
// pieces of its signature separately.
enum Said {
    Whole(TyId),
    Parts { params: Vec<TyId>, ret: Option<TyId> },
    Nothing,
}

struct Job {
    from:  SIRBodyId,
    args:  Vec<TyId>,
    to:    SIRBodyId,
    depth: usize,
}

struct Mono<'a> {
    sir:     &'a SIRProgram,
    // The grown copy. Interning goes in here, and the mangler spells out of it,
    // so a type an instance needed is a type its name can be written from.
    p:       TTIRProgram,
    mangler: Mangler,
    out:     Vec<SIRBody>,
    symbols: Vec<String>,
    named:   HashMap<(SIRBodyId, SIRBlockId, usize), String>,
    // Which body each instance became, by its symbol, so that one is made once
    // however many places reach it.
    //
    // The symbol and not the `(declaration, arguments)` pair, though that is
    // what an instance *is*. The arena reaching this pass holds a few types
    // twice, so `i32` at one call and `i32` at another can be two ids of one
    // type -- and keyed on the ids those are two instances, with one name
    // between them and a linker to disappoint. The name is what has to be
    // unique, so the name is what is kept.
    done:    HashMap<String, SIRBodyId>,
    queue:   VecDeque<Job>,
    refused: Vec<String>,
    made:    usize,
}

// `tests` is whether a `%test` is a fn to compile. "Collected and run on its
// own rather than compiled into an ordinary build" (section 2) is a rule about
// what is in the output, and this is the pass that decides: a test is a root of
// a test build and of nothing else, so an ordinary build carries no body for
// one.
//
// The test and not what it called. `roots` takes every non-generic fn there is
// rather than every one something reaches, so a helper only a test calls is
// compiled either way -- dropping what nobody calls is a pass this compiler
// does not have, and a `%test` is not where it would begin.
pub fn monomorphise(ttir: &TTIRProgram, sir: &SIRProgram, tests: bool) -> Made {
    let mut m = Mono {
        sir,
        p: ttir.clone(),
        mangler: Mangler::new(ttir),
        out: Vec::new(),
        symbols: Vec::new(),
        named: HashMap::new(),
        done: HashMap::new(),
        queue: VecDeque::new(),
        refused: Vec::new(),
        made: 0,
    };
    m.roots(tests);
    m.drain();
    Made {
        ttir:      m.p,
        sir:       SIRProgram { bodies: m.out },
        symbols:   m.symbols,
        symbol_of: m.named,
        instances: m.made,
        refused:   m.refused,
    }
}

impl<'a> Mono<'a> {
    // Every fn a program can reach without being told what a type is. A generic
    // is not one: there is nothing to compile until something says what its
    // parameters stand for, which is the whole of what this pass is about.
    fn roots(&mut self, tests: bool) {
        for at in 0..self.p.items.len() {
            let TTIRItemKind::Fn(f) = &self.p.items[at].kind else { continue };
            if f.attrs.is_test && !tests {
                continue;
            }
            let (Some(body), false) = (f.body, takes_types(&self.p, at)) else { continue };
            if body >= self.sir.bodies.len() {
                continue;
            }
            let name = self.mangler.symbol(f, at, &self.p);
            self.want(body, Vec::new(), name, 0);
        }
    }

    // The impl member that answers this one for this receiver, or the member as
    // it stands.
    //
    // Everything but a trait member is itself: a method written in an ordinary
    // `impl` was resolved by `sema` and there is nothing here to choose. A trait
    // member is the one case `sema` had to leave open, and it is closed by the
    // receiver -- the type is concrete by now, `mono` having substituted it.
    //
    // `mir::lower::glue::drop_method` does this same walk for `Drop`, by the
    // trait's name, and is what this generalises.
    fn answering(&mut self, member: usize, recv: Option<TyId>) -> usize {
        let Some(of) = self.trait_of(member) else { return member };
        let Some(recv) = recv else { return member };
        let TTIRItemKind::Fn(f) = &self.p.items[member].kind else { return member };
        let name = f.name.clone();

        // A receiver stands for what it refers to, so a method of the referent
        // is a method of the reference -- the same rule `sema` resolves by.
        let mut held = recv;
        while let Some(Ty::Ref { inner, .. }) = self.p.types.get(held) {
            held = *inner;
        }
        let Some(Ty::Named { item: want, .. }) = self.p.types.get(held).cloned() else {
            return member;
        };

        for at in 0..self.p.items.len() {
            let TTIRItemKind::Impl { ty, of: Some(answers), members, .. } =
                self.p.items[at].kind.clone()
            else {
                continue;
            };
            if answers != of {
                continue;
            }
            let Some(Ty::Named { item: subject, .. }) = self.p.types.get(ty).cloned() else {
                continue;
            };
            if subject != want {
                continue;
            }
            for one in members {
                if let TTIRItemKind::Fn(held) = &self.p.items[one].kind {
                    if held.name == name {
                        return one;
                    }
                }
            }
        }
        // No impl answers it. `sema` holds every argument to its bounds and
        // every impl to the members its trait declares, so a program that
        // reaches here is one those two checks did not cover -- naming the
        // trait member is the honest answer, and the linker says the rest.
        member
    }

    // The trait a member was declared in, where it was declared in one.
    fn trait_of(&self, member: usize) -> Option<usize> {
        self.p.items.iter().position(|item| {
            matches!(&item.kind, TTIRItemKind::Trait { members, .. } if members.contains(&member))
        })
    }

    // Ask for one instance, and say where it went. Asking twice gives the same
    // answer both times, which is what stops a recursive declaration.
    fn want(&mut self, from: SIRBodyId, args: Vec<TyId>, name: String, depth: usize) -> SIRBodyId {
        if let Some(at) = self.done.get(&name) {
            return *at;
        }
        let to = self.out.len();
        // Held before the body is built, so that a body reaching itself finds
        // the answer rather than asking for it again.
        self.out.push(empty());
        self.symbols.push(name.clone());
        self.done.insert(name, to);
        if !args.is_empty() {
            self.made += 1;
        }
        self.queue.push_back(Job { from, args, to, depth });
        to
    }

    fn drain(&mut self) {
        while let Some(job) = self.queue.pop_front() {
            if job.depth > DEEPEST {
                self.refused.push(format!(
                    "`{}` is made out of itself with a new type every time, so there is no \
                     end to the instances it asks for",
                    self.symbols[job.to]
                ));
                continue;
            }
            let built = self.body(&job);
            self.out[job.to] = built;
        }
    }

    // One instance: the declaration's body with its type parameters filled in,
    // and every declaration it names followed.
    fn body(&mut self, job: &Job) -> SIRBody {
        let mut body = self.sir.bodies[job.from].clone();

        for value in &mut body.values {
            value.ty = self.subst(value.ty, &job.args);
        }
        for slot in &mut body.slots {
            slot.ty = self.subst(slot.ty, &job.args);
        }

        // Where each declaration is named, by the value that naming made. A
        // call reaches its callee through that value, so this is what turns
        // "what this call was given" into "what that `Item` stood for".
        let mut item_at: HashMap<SIRValueId, (SIRBlockId, usize)> = HashMap::new();
        for (at, block) in body.blocks.iter().enumerate() {
            for (i, inst) in block.insts.iter().enumerate() {
                if matches!(inst.kind, SIRInstKind::Item(_) | SIRInstKind::ItemAddr(_)) {
                    if let Some(def) = inst.def {
                        item_at.insert(def, (at, i));
                    }
                }
            }
        }

        // What a call says about the declaration it reaches, gathered before
        // anything is asked for, because asking borrows.
        //
        // This is where an *inferred* instantiation is written down and the
        // only place it is. `sema::lower::paths::instantiate` substitutes into
        // the type of the expression naming the fn only where the arguments
        // were written -- `id<i32>` puts them in before the call is reached --
        // and where they were worked out instead, the name keeps the
        // declaration's own type and the call carries the answer.
        let mut said: Vec<((SIRBlockId, usize), usize, Said)> = Vec::new();
        for block in body.blocks.iter() {
            for inst in &block.insts {
                let SIRInstKind::Call { callee, args } = &inst.kind else { continue };
                let Some(&(bl, i)) = item_at.get(callee) else { continue };
                let (SIRInstKind::Item(item) | SIRInstKind::ItemAddr(item)) =
                    body.blocks[bl].insts[i].kind
                else {
                    continue;
                };
                let params = args
                    .iter()
                    .filter_map(|&arg| body.values.get(arg).map(|held| held.ty))
                    .collect();
                let ret = inst.def.and_then(|def| body.values.get(def)).map(|held| held.ty);
                said.push(((bl, i), item, Said::Parts { params, ret }));
            }
        }
        for ((bl, i), item, held) in said {
            if let Some(name) = self.declaration(item, held, job) {
                self.named.insert((job.to, bl, i), name);
            }
        }

        // And everything else that names one: a fn held as a value rather than
        // called, a method, a closure.
        for at in 0..body.blocks.len() {
            for i in 0..body.blocks[at].insts.len() {
                if self.named.contains_key(&(job.to, at, i)) {
                    continue;
                }
                let inst = body.blocks[at].insts[i].clone();
                if let Some(name) = self.names(&inst, &body, job) {
                    self.named.insert((job.to, at, i), name);
                }
            }
        }
        body
    }

    // What one instruction names, where it names a declaration at all. This is
    // where an instance is asked for: a declaration whose own type still has
    // parameters in it, reached by a use whose types have none, and the two
    // together say what each parameter stands for.
    fn names(&mut self, inst: &SIRInst, body: &SIRBody, job: &Job) -> Option<String> {
        let ty_of = |value: SIRValueId| body.values.get(value).map(|held| held.ty);
        match &inst.kind {
            // The value *is* the fn, so its type is the whole signature and one
            // match against the declaration recovers everything.
            SIRInstKind::Item(item) | SIRInstKind::ItemAddr(item) => {
                let said = match inst.def.and_then(ty_of) {
                    Some(ty) => Said::Whole(ty),
                    None => Said::Nothing,
                };
                self.declaration(*item, said, job)
            }
            // A method names its declaration directly, so there is no value
            // holding the signature. What there is instead is the receiver, the
            // arguments and the answer -- which is the same signature in
            // pieces.
            SIRInstKind::Method { recv, item, args } => {
                let mut params: Vec<TyId> = Vec::with_capacity(args.len() + 1);
                params.extend(ty_of(*recv));
                params.extend(args.iter().filter_map(|&arg| ty_of(arg)));
                // A method reached through a bound names the *trait's* member,
                // which has no body: `sema` could not say which impl answered
                // because what the parameter stood for was the caller's to say.
                // Here it has been said -- the receiver's type is substituted --
                // so this is where the impl that answers is chosen.
                let held = params.first().copied();
                let item = self.answering(*item, held);
                let said = Said::Parts { params, ret: inst.def.and_then(ty_of) };
                self.declaration(item, said, job)
            }
            // A closure is part of the body that wrote it, so it is made
            // wherever that body was made and with the same arguments. Its name
            // is the enclosing one's with a number after it: nothing in the
            // source names a closure, so nothing outside can collide with it.
            SIRInstKind::Closure { body: inner, .. } => {
                if *inner >= self.sir.bodies.len() {
                    return None;
                }
                let name = format!("{}$c{}", self.symbols[job.to], inner);
                let mut symbol = String::from("__C");
                part(&name, &mut symbol);
                let at = self.want(*inner, job.args.clone(), symbol, job.depth + 1);
                Some(self.symbols[at].clone())
            }
            _ => None,
        }
    }

    // What a named declaration is called here, asking for its instance where it
    // has one to ask for.
    fn declaration(&mut self, item: usize, said: Said, job: &Job) -> Option<String> {
        let TTIRItemKind::Fn(f) = &self.p.items.get(item)?.kind else {
            return self.mangler.symbol_of(item, &self.p);
        };
        let f = f.clone();
        let base = self.mangler.symbol(&f, item, &self.p);
        let Some(body) = f.body else { return Some(base) };
        if body >= self.sir.bodies.len() {
            return Some(base);
        }

        if !takes_types(&self.p, item) {
            self.want(body, Vec::new(), base.clone(), job.depth + 1);
            return Some(base);
        }

        // Generic. What it stands for is the difference between what the
        // declaration says and what this use was given.
        let wants = types_wanted(&self.p, item);
        let args = self.recover(f.ty, &said, wants);
        if args.len() != wants || args.iter().any(|&arg| self.has_param(arg)) {
            // Nothing here can say what it stands for. A `@symbol` fn has no
            // body to make anyway; anything else is a shape this pass does not
            // reach yet, and naming the declaration is the honest answer.
            return Some(base);
        }

        let name = self.instance(&base, &f.attrs.symbol, &args, item);
        self.want(body, args, name.clone(), job.depth + 1);
        Some(name)
    }

    // An instance's symbol: the declaration's, and then one part for each type
    // it was made with. §8 asks for exactly this -- "the arguments have to reach
    // the name" -- and this is the mangling already in use with more parts.
    //
    // A `@symbol` name is not touched. "Nothing outside the language can predict
    // a mangling, which is the whole of why a call out to C is written with
    // this", so adding to one would break the only promise it makes.
    fn instance(
        &mut self,
        base: &str,
        given: &Option<String>,
        args: &[TyId],
        item: usize,
    ) -> String {
        if given.is_some() {
            let _ = item;
            return base.to_string();
        }
        let mut out = base.to_string();
        for &arg in args {
            let spelt = self.mangler.spell(arg, &self.p);
            part(&spelt, &mut out);
        }
        out
    }

    // ---- Types -------------------------------------------------------------

    // What the declaration's parameters stand for, read off by putting its own
    // type beside the one this use was given. Where the declaration says `T`,
    // the use says what `T` is.
    fn recover(&self, decl: TyId, said: &Said, wants: usize) -> Vec<TyId> {
        let mut found: Vec<Option<TyId>> = vec![None; wants];
        match said {
            Said::Nothing => {}
            Said::Whole(actual) => self.against(decl, *actual, &mut found),
            Said::Parts { params, ret } => {
                let Some(Ty::Fn { params: declared, ret: declared_ret, .. }) =
                    self.p.types.get(decl)
                else {
                    return Vec::new();
                };
                // Whether the receiver is one of the declared parameters is the
                // declaration's business and not this pass's, so both readings
                // are tried and the one whose count agrees is taken. Guessing
                // wrong would pair a `self` against a first argument.
                let held: &[TyId] = if declared.len() == params.len() {
                    params
                } else if declared.len() + 1 == params.len() {
                    &params[1..]
                } else {
                    return Vec::new();
                };
                for (decl, actual) in declared.iter().zip(held.iter()) {
                    self.against(*decl, *actual, &mut found);
                }
                if let Some(ret) = ret {
                    self.against(*declared_ret, *ret, &mut found);
                }
            }
        }
        found.into_iter().flatten().collect()
    }

    fn against(&self, decl: TyId, actual: TyId, found: &mut Vec<Option<TyId>>) {
        let (Some(a), Some(b)) = (self.p.types.get(decl), self.p.types.get(actual)) else {
            return;
        };
        match (a, b) {
            (Ty::Param { index, .. }, _) => {
                if let Some(slot) = found.get_mut(*index) {
                    if slot.is_none() {
                        *slot = Some(actual);
                    }
                }
            }
            (Ty::Ref { inner: a, .. }, Ty::Ref { inner: b, .. })
            | (Ty::Ptr(a), Ty::Ptr(b))
            | (Ty::Run(a), Ty::Run(b))
            | (Ty::GC(a), Ty::GC(b))
            | (Ty::Array { elem: a, .. }, Ty::Array { elem: b, .. }) => {
                self.against(*a, *b, found)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.against(*a, *b, found);
                }
            }
            (Ty::Named { item: x, args: a, .. }, Ty::Named { item: y, args: b, .. })
                if x == y && a.len() == b.len() =>
            {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.against(*a, *b, found);
                }
            }
            (
                Ty::Fn { params: a, ret: ra, .. },
                Ty::Fn { params: b, ret: rb, .. },
            ) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b.iter()) {
                    self.against(*a, *b, found);
                }
                self.against(*ra, *rb, found);
            }
            _ => {}
        }
    }

    // The same type with its parameters replaced. Nothing to do where there is
    // nothing standing in, which is every body that was not made from a
    // generic -- and that is most of them.
    fn subst(&mut self, ty: TyId, args: &[TyId]) -> TyId {
        if args.is_empty() {
            return ty;
        }
        let Some(held) = self.p.types.get(ty).cloned() else { return ty };
        let made = match held {
            Ty::Param { index, .. } => return args.get(index).copied().unwrap_or(ty),
            Ty::Prim(_) | Ty::Var(_) | Ty::Error => return ty,
            Ty::Ref { op, life, inner } => {
                Ty::Ref { op, life, inner: self.subst(inner, args) }
            }
            Ty::Ptr(inner) => Ty::Ptr(self.subst(inner, args)),
            Ty::Run(inner) => Ty::Run(self.subst(inner, args)),
            Ty::GC(inner) => Ty::GC(self.subst(inner, args)),
            Ty::Array { elem, len } => Ty::Array { elem: self.subst(elem, args), len },
            Ty::Tuple(parts) => {
                Ty::Tuple(parts.iter().map(|&p| self.subst(p, args)).collect())
            }
            Ty::Named { item, args: had, regions } => Ty::Named {
                item,
                args: had.iter().map(|&a| self.subst(a, args)).collect(),
                regions,
            },
            Ty::Fn { uses, params, ret, is_unsafe } => Ty::Fn {
                uses,
                params: params.iter().map(|&p| self.subst(p, args)).collect(),
                ret: self.subst(ret, args),
                is_unsafe,
            },
        };
        self.intern(made)
    }

    // The arena is deduplicated -- one `TyId` per type, so that comparing two
    // ids compares two types -- and adding to it has to keep that true.
    fn intern(&mut self, ty: Ty) -> TyId {
        if let Some(at) = self.p.types.iter().position(|held| held == &ty) {
            return at;
        }
        self.p.types.push(ty);
        self.p.types.len() - 1
    }

    fn has_param(&self, ty: TyId) -> bool {
        match self.p.types.get(ty) {
            Some(Ty::Param { .. }) => true,
            Some(Ty::Ref { inner, .. }) => self.has_param(*inner),
            Some(Ty::Ptr(inner)) | Some(Ty::Run(inner)) | Some(Ty::GC(inner)) => {
                self.has_param(*inner)
            }
            Some(Ty::Array { elem, .. }) => self.has_param(*elem),
            Some(Ty::Tuple(parts)) => parts.iter().any(|&p| self.has_param(p)),
            Some(Ty::Named { args, .. }) => args.iter().any(|&a| self.has_param(a)),
            Some(Ty::Fn { params, ret, .. }) => {
                params.iter().any(|&p| self.has_param(p)) || self.has_param(*ret)
            }
            _ => false,
        }
    }
}

// Whether a declaration takes type parameters. A lifetime is not one: what it
// stands for is a region, and a region has no width -- so a fn generic only over
// lifetimes is compiled once, like any other.
fn takes_types(p: &TTIRProgram, item: usize) -> bool {
    types_wanted(p, item) > 0
}

fn types_wanted(p: &TTIRProgram, item: usize) -> usize {
    let Some(TTIRItemKind::Fn(f)) = p.items.get(item).map(|held| &held.kind) else {
        return 0;
    };
    f.generics
        .iter()
        .filter(|g| matches!(g, crate::tir::ttir_nodes::TTIRGeneric::Type { .. }))
        .count()
}

// Stands in a body's place until it is built, so that a body reaching itself
// finds an id rather than asking for one again.
fn empty() -> SIRBody {
    SIRBody {
        entry:  0,
        blocks: Vec::new(),
        values: Vec::new(),
        slots:  Vec::new(),
        params: Vec::new(),
    }
}

#[cfg(test)]
mod tests;
