// Moves and borrows: the two rules the language spends its ownership story on.
//
//     A place is reached either through one `*` and nothing else, or through
//     any number of `&` and no `*` -- one mutable reference or many immutable
//     ones, and never both.                              (docs/prose.txt, §3)
//
//     What `let b = a` does to a is move it. The value goes to the new name and
//     the old one is done with: reading a after that is refused where it is
//     written, and so is passing it, returning it or assigning through it.
//                                                        (docs/prose.txt, §2)
//
// Both are marked settled in the prose and both are handed to "the checker"
// without a pass being named. This is that pass.
//
// It walks the TTIR and not the GIR. The language is structured -- every branch
// and every loop is an expression and there is no goto -- so a walk that joins
// at an `if` and settles a loop by going round it twice reaches what a dataflow
// over a graph would reach. What the graph does not keep is what this needs:
// `gir::lower` flattens the blocks a borrow's extent is measured in, drops which
// locals were parameters, and binds a pattern's names on an edge rather than in
// a statement.
//
// A closure that hands away what it captured is a `once fn`, and calling one
// takes it: `is_copy` says a `once fn` moves, so the second call is a use of
// something that has gone and needs no rule here of its own. What tells the
// three fn types apart is `sema::lower`, from what each capture asks.
//
// A closure's body is walked like any other, with two things said about the
// names it did not declare: one captured by reference is somebody else's and
// may not be handed away from inside, and what the body gives back may point at
// a capture -- which outlives the closure -- but not at anything the body
// declared, which does not.
//
// A borrow lasts from where it is taken to the last place anything can reach
// through it, which is where the slot holding it is last read -- the rule Rust
// reached with NLL, and sharper than the block-long extent this used to have.
// Everything is numbered in the order it was written; a loop is the one place
// that is not enough, since what stands above a use runs below it on the next
// turn, and a slot last read inside one is held to all of it. Which borrows
// keep a slot's extent is the other half: a `&` that got as far as the value
// keeps it, and one that did not is a temporary and goes with the statement --
// `len(&x)` gives back an `i32` and can hold nothing, so the `&x` is over when
// the line is.
//
// Regions are checked too, and so are the bounds on them -- a `'a: 'b` and a
// `T: 'a` are promises a *caller* keeps, so they are held to at the call. The
// shape all of it takes here is worth saying:
//
//     What the rule costs is precision, and it spends it at the call rather
//     than at the declaration ... the program that cannot be proved is turned
//     down where it is used and not where the thing that could not be proved
//     was written.                                      (docs/prose.txt, §3)
//
// So there is no second frame and no constraint solver. A signature's
// `outlives` says which of its parameters its result is tied to; a body orders
// its own slots by how deeply nested the block that declared each one is; and
// the check is that a value never reaches a place that outlives it. What the
// return type asks for is the same question with the place being the caller,
// which outlives everything the body declares.
//
// What it does not do:
//
//   - Count the regions of a declaration reached from itself. `struct A { b:
//     &B }` beside `struct B { a: &A }` has no finite number of them, each
//     turn round adding the last one's, and 0 is what such a declaration is
//     given. `holds_ref` still sees the reference, so what comes of one is
//     held to every parameter -- the elision rule's own answer, and never
//     wrong.
//   - Where a `Drop` runs. Settled in §2 and placed by `gir::drops`, which is
//     where the graph is: "nothing at all where the value was moved away
//     first" is a question about a program point, and a graph is what answers
//     one. What this pass does with a move is refuse it, which wants the line
//     it was written on and so wants the tree.

#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::tir::tir_nodes::{TIRBinding, TIRFnUses, TIRRefOp, TIRSelf, TIRUnaryOp};
use crate::tir::ttir_nodes::{
    RegionId, TTIRBound, TTIRCapture, TTIRSubject, TTIRBodyId, TTIRCaptureMode, TTIRExprId, TTIRExprKind, TTIRFn, TTIRGeneric, TTIRItemId,
    TTIRItemKind, TTIRLocalId, TTIRPatId, TTIRPatKind, TTIRPayload, TTIRProgram, TTIRStmt, Ty,
    TyId,
};

// ---- Places ---------------------------------------------------------------

// What a rule about borrowing is about. Not a name: `p.x` and `p.y` are two
// places under one name, and `*self` is one place under none.
//
// The root is the slot it starts at and the path is the way in from there.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: TTIRLocalId,
    pub path: Vec<Step>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Step {
    // `.x`, by the index the resolver settled it to.
    Field(usize),
    // `.0`
    Tuple(u64),
    // `[i]`, and the index is not kept: `a[i]` and `a[j]` are one place here.
    // Whether two views of one array whose ranges do not meet are one place or
    // two is left open by §3, and this is the half that turns more down.
    Index,
    // Crossing a reference. Nothing in the source writes this -- "a reference
    // stands for the place it refers to and is read, called, indexed and
    // reached into exactly as that place is" (§3), so there is no operator for
    // it -- and the walk puts one in wherever a projection's base is a `Ty::Ref`.
    Deref,
}

impl Place {
    fn of(root: TTIRLocalId) -> Place {
        Place { root, path: Vec::new() }
    }

    fn then(&self, step: Step) -> Place {
        let mut path = self.path.clone();
        path.push(step);
        Place { root: self.root, path }
    }

    // Whether touching one touches the other. One place conflicts with another
    // where they share a root and one way in is a prefix of the other: `p`
    // conflicts with `p.x`, and `p.x` with nothing of `p.y`.
    //
    // Distinct fields not conflicting is the other half of what §3 leaves open,
    // decided the way that turns fewer programs down.
    pub fn conflicts(&self, other: &Place) -> bool {
        if self.root != other.root {
            return false;
        }
        let shorter = self.path.len().min(other.path.len());
        self.path[..shorter] == other.path[..shorter]
    }
}

// ---- What copies ----------------------------------------------------------

// The two names the compiler knows, as it knows the six attributes. A type with
// an `impl Copy` copies where it would otherwise move; one with an `impl Drop`
// says what releasing it comes to, and §2 says a type may not have both.
pub struct Copies {
    copy: Vec<bool>,
    drop: Vec<bool>,
}

impl Copies {
    // Found by name: an `impl` whose trait is the item called `Copy` says its
    // type copies. Nothing else in the compiler resolves a trait by name, and
    // §2 is explicit that these two are known by theirs.
    pub fn of(p: &TTIRProgram) -> Copies {
        let mut copy = vec![false; p.items.len()];
        let mut drop = vec![false; p.items.len()];
        for item in &p.items {
            let TTIRItemKind::Impl { ty, of: Some(trait_item), .. } = &item.kind else {
                continue;
            };
            // The type it is written for, where that names a declaration: an
            // `impl Copy for i32` says nothing this needs, the primitives
            // copying without asking.
            let Ty::Named { item: named, .. } = &p.types[*ty] else { continue };
            match name_of(*trait_item, p).as_str() {
                "Copy" => copy[*named] = true,
                "Drop" => drop[*named] = true,
                _ => {}
            }
        }
        Copies { copy, drop }
    }

    // Whether a value of this type has anything to release. An `impl Drop`
    // says so outright; a struct or an enum holding one says so because its
    // fields go when it does -- "a field when the value holding it goes" (§2).
    //
    // A `Ty::Param` is answered by whether it moves at all: what it turns out
    // to be is the caller's, and a fn is checked once for every caller there
    // will ever be. So anything that is not known to copy is treated as having
    // something to release, which costs a release that does nothing where it
    // has not.
    pub fn drops(&self, ty: TyId, p: &TTIRProgram, generics: &[TTIRGeneric]) -> bool {
        self.drops_past(ty, p, generics, &mut Vec::new())
    }

    fn drops_past(
        &self,
        ty: TyId,
        p: &TTIRProgram,
        generics: &[TTIRGeneric],
        seen: &mut Vec<TTIRItemId>,
    ) -> bool {
        match &p.types[ty] {
            // Nothing a primitive holds is anybody's to release, and what a
            // reference or a pointer refers to is owned somewhere else.
            Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Run(_) => false,
            // A closure that took what it captured is holding it, and what it
            // holds goes when the closure does. Which types those were is not
            // in the fn type, so this is the blunt answer: a `once fn` has
            // something to release and the other two have not.
            Ty::Fn { uses, .. } => *uses == TIRFnUses::Takes,
            Ty::Named { item, args, .. } => {
                if self.drop[*item] {
                    return true;
                }
                if args.iter().any(|&a| self.drops_past(a, p, generics, seen)) {
                    return true;
                }
                if seen.contains(item) {
                    return false;
                }
                seen.push(*item);
                let held = match &p.items[*item].kind {
                    TTIRItemKind::Struct { fields, .. } => {
                        fields.iter().any(|f| self.drops_past(f.ty, p, generics, seen))
                    }
                    TTIRItemKind::Enum { variants, .. } => {
                        variants.iter().any(|v| match &v.payload {
                            TTIRPayload::None => false,
                            TTIRPayload::Tuple(tys) => {
                                tys.iter().any(|&t| self.drops_past(t, p, generics, seen))
                            }
                            TTIRPayload::Named(fields) => {
                                fields.iter().any(|f| self.drops_past(f.ty, p, generics, seen))
                            }
                        })
                    }
                    _ => false,
                };
                seen.pop();
                held
            }
            Ty::Array { elem, .. } => self.drops_past(*elem, p, generics, seen),
            Ty::GC(_) => false,
            Ty::Tuple(members) => {
                members.iter().any(|&m| self.drops_past(m, p, generics, seen))
            }
            Ty::Param { .. } => !self.is_copy(ty, p, generics),
            Ty::Var(_) | Ty::Error => false,
        }
    }

    // Whether a value of this type is copied where it is handed over, rather
    // than moved out of where it was.
    //
    //     The primitives copy without asking, and so do `null`, a reference,
    //     and a fixed array or tuple every part of which copies; everything
    //     else moves until it says otherwise.                            (§2)
    // `generics` is the declaration the type stands in, which a `Ty::Param`
    // needs: it names its parameter by place, and whose list that is is not in
    // the type. An empty list answers `false` for one, which is the half that
    // turns more down.
    pub fn is_copy(&self, ty: TyId, p: &TTIRProgram, generics: &[TTIRGeneric]) -> bool {
        match &p.types[ty] {
            // `null` is among the primitives, and is in the list by name too.
            Ty::Prim(_) => true,
            // A reference copies; what it refers to is owned somewhere else.
            Ty::Ref { .. } | Ty::Ptr(_) => true,
            // A closure copies where calling it does nothing to what it
            // captured. A `once fn` gives away what it holds when it is
            // called, so it has one owner and one call like any other value
            // that moves -- which is what makes the second call a use of
            // something that has gone, and needs no rule of its own.
            Ty::Fn { uses, .. } => *uses != TIRFnUses::Takes,

            Ty::Named { item, .. } => self.copy[*item],

            // "An array copies exactly when its element does, so an `i32[8]`
            // copies and a `Buf[8]` moves" (§3).
            Ty::Array { elem, .. } => self.is_copy(*elem, p, generics),
            // A run is only ever reached behind a reference, and the reference
            // is what is handed over.
            Ty::Run(_) => true,
            // "copying where every member copies and moving otherwise" (§3).
            Ty::Tuple(members) => members.iter().all(|&m| self.is_copy(m, p, generics)),

            // A parameter copies where it was declared to. `<T: Copy>` is how a
            // fn says so, and the bound is the only thing that can say it: what
            // `T` turns out to be is the caller's, and a fn is checked once for
            // every caller there will ever be.
            Ty::Param { index, .. } => match generics.get(*index) {
                Some(TTIRGeneric::Type { bounds, .. }) => bounds.iter().any(|bound| {
                    let crate::tir::ttir_nodes::TTIRBound::Trait(held) = bound else {
                        return false;
                    };
                    matches!(&p.types[*held], Ty::Named { item, .. } if name_of(*item, p) == "Copy")
                }),
                _ => false,
            },

            // Whether a `gc` binding may be moved out of is not settled (§8),
            // so this is a decision and not a rule: a value the collector owns
            // is a value with an owner, and an owner is what moving is about.
            Ty::GC(_) => false,

            // Neither says anything, and a type nobody worked out has already
            // been reported once.
            Ty::Var(_) | Ty::Error => true,
        }
    }

    pub fn is_drop(&self, item: TTIRItemId) -> bool {
        self.drop[item]
    }

    // "A type cannot have both a `Copy` and a `Drop`: a value that has
    // something to release is a value there had better be one of" (§2).
    pub fn both(&self) -> Vec<TTIRItemId> {
        (0..self.copy.len()).filter(|&i| self.copy[i] && self.drop[i]).collect()
    }
}

// What an item is called. `sema::names` has one of these and it is private to
// that module; a trait is asked its name in one place here and the two are the
// same question.
fn name_of(id: TTIRItemId, p: &TTIRProgram) -> String {
    match &p.items[id].kind {
        TTIRItemKind::Fn(f) => f.name.clone(),
        TTIRItemKind::Struct { name, .. }
        | TTIRItemKind::Enum { name, .. }
        | TTIRItemKind::Trait { name, .. }
        | TTIRItemKind::Namespace { name, .. }
        | TTIRItemKind::TypeAlias { name, .. }
        | TTIRItemKind::Const { name, .. } => name.clone(),
        TTIRItemKind::Global { name: TIRBinding::Name(name), .. } => name.clone(),
        _ => String::new(),
    }
}

// ---- What is still there --------------------------------------------------

// Whether the value in a place is still the place's. A move takes it away, and
// the two paths of an `if` may disagree about whether one happened -- which is
// its own answer and not a guess at one of the other two.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Moved { line: usize, col: usize },
    Maybe { line: usize, col: usize },
}

impl State {
    fn at(self) -> Span {
        match self {
            State::Moved { line, col } | State::Maybe { line, col } => Span::at(line, col),
        }
    }

    fn certain(self) -> bool {
        matches!(self, State::Moved { .. })
    }
}

// What has gone, and from where. A place not in here is still whole: the map
// holds what is unusual, so an untouched body carries nothing.
#[derive(Debug, Clone, Default, PartialEq)]
struct Gone(HashMap<Place, State>);

impl Gone {
    // What is known about a place, taking the nearest thing that covers it: `p`
    // having gone is `p.x` having gone, since the value `p.x` was part of went
    // with it.
    fn of(&self, place: &Place) -> Option<State> {
        if let Some(&held) = self.0.get(place) {
            return Some(held);
        }
        // A prefix of this place, which is a move of something this was part of.
        self.0
            .iter()
            .filter(|(held, _)| {
                held.root == place.root
                    && held.path.len() < place.path.len()
                    && held.path[..] == place.path[..held.path.len()]
            })
            .map(|(_, &state)| state)
            .max_by_key(|state| state.certain())
    }

    fn moved(&mut self, place: Place, line: usize, col: usize) {
        self.0.insert(place, State::Moved { line, col });
    }

    // Filled again. A moved-from local may be given another value, and what was
    // reached through it is whole again with it.
    fn filled(&mut self, place: &Place) {
        self.0.retain(|held, _| !held.conflicts(place));
    }

    // Two paths met. A place gone down one of them and not the other is gone
    // for neither and whole for neither, which is what `Maybe` is for.
    fn join(&mut self, other: &Gone) {
        for (place, &there) in &other.0 {
            match self.0.get(place).copied() {
                None => {
                    let (line, col) = (there.at().line, there.at().col);
                    self.0.insert(place.clone(), State::Maybe { line, col });
                }
                Some(here) if here.certain() && !there.certain() => {
                    self.0.insert(place.clone(), there);
                }
                Some(_) => {}
            }
        }
        // And a place gone here but not there is only a maybe now.
        let elsewhere: Vec<Place> = self
            .0
            .keys()
            .filter(|place| !other.0.contains_key(*place))
            .cloned()
            .collect();
        for place in elsewhere {
            if let Some(State::Moved { line, col }) = self.0.get(&place).copied() {
                self.0.insert(place, State::Maybe { line, col });
            }
        }
    }
}

// ---- Borrows in hand ------------------------------------------------------

// One reference, held from where it was taken to the end of the block that took
// it. There is no region here: how long a reference is good for is another
// pass's, and the block it stands in is what this has instead.
#[derive(Debug, Clone)]
struct Held {
    place: Place,
    op:    TIRRefOp,
    line:  usize,
    col:   usize,
    // The last moment anything can reach through it. A borrow bound to a slot
    // dies where that slot is last used, which is what makes this sharper than
    // "the end of the block": `let r = &x; let n = r; let m = *x` is three
    // lines of which only the first two are about `r`.
    //
    // `usize::MAX` for one that reached no slot: nothing can read it, so
    // nothing says when it stops being read, and the block is the answer.
    until: usize,
    // The expression that took it, which is how `reaching` says whether it got
    // as far as the slot a `let` was filling.
    at:    TTIRExprId,
}

// ---- Where the walk got to ------------------------------------------------

// Whether what was walked came back. `return`, `break` and `continue` do not,
// and neither does anything after them -- which is what makes them expressions
// of type `never` (§3) and what keeps a path that left out of a join.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Flow {
    Normal,
    Left,
}

impl Flow {
    fn left(self) -> bool {
        self == Flow::Left
    }
}

// What a use of a moved value was doing, which is the four §2 names: "reading a
// after that is refused where it is written, and so is passing it, returning it
// or assigning through it".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Use {
    Read,
    Pass,
    Return,
    Assign,
}

impl Use {
    fn word(self) -> &'static str {
        match self {
            Use::Read => "this reads it",
            Use::Pass => "this passes it",
            Use::Return => "this returns it",
            Use::Assign => "this assigns through it",
        }
    }
}

// ---- The checker ----------------------------------------------------------

pub struct Checker<'a> {
    p:       &'a TTIRProgram,
    copies:  Copies,
    errors:  Diagnostics,
    // The body being walked, and the declaration it belongs to: a `Ty::Param`
    // is answered by the second.
    body:    TTIRBodyId,
    generic: Vec<TTIRGeneric>,
    gone:    Gone,
    // Every borrow in hand, and where each block's own began -- popping to that
    // mark is what ends a borrow's extent.
    held:    Vec<Held>,
    marks:   Vec<usize>,
    // Where a `break` left from, so what follows the loop is the join of every
    // way out of it.
    breaks:  Vec<Vec<Gone>>,
    // Off while a loop is being settled, so going round it twice does not say
    // the same thing twice.
    quiet:   bool,
    // Whether what this body gives back holds a reference standing in a region
    // of the signature. If it does not, nothing it gives back can outstay
    // anything, and the escape check has nothing to ask.
    leaves:  bool,
    // How deeply nested the block that declared each slot is. A parameter is 0,
    // since it came from outside and outlives everything the body declares; a
    // local of the body's own block is 1, one inside a block inside that is 2,
    // and a bigger number is a shorter life. Comparing two of them is the whole
    // of the ordering this pass has, and it is the ordering the language has:
    // "a local at the end of its block" (§2) is what a block being nested in
    // another one comes to.
    depth:   HashMap<TTIRLocalId, usize>,
    // Which locals have already been refused for outstaying something. One
    // mistake is one message: a reference put in a slot that outlives it and
    // then given back out of the body is one thing gone wrong in two places,
    // and the first place is the one worth reading.
    said_of: Vec<TTIRLocalId>,
    // Where the value a pattern is being taken apart points. A pattern binds
    // names out of something, and this is that something's roots, held while
    // `binds` walks -- a pattern has no expression of its own to ask.
    from_of: Vec<(TTIRLocalId, TTIRExprId)>,
    // When each expression of this body stands, in the order they were
    // written, and the last moment each slot is read. Worked out before the
    // walk: a borrow's extent is a fact about the whole body and the walk is
    // where it is used, not where it is found out.
    when:    HashMap<TTIRExprId, usize>,
    last:    HashMap<TTIRLocalId, usize>,
    // Where the walk is now, so a borrow whose slot is done with can be told
    // from one still in hand.
    now:     usize,
    // The slots of *this* body that hold a name the closure it belongs to
    // captured by reference. Inside the body such a slot has the captured
    // type and not a reference type -- `catch` gives it the type it found --
    // so nothing about the slot itself says the value is somebody else's.
    caught:  HashMap<TTIRLocalId, TIRRefOp>,
    // What each slot's value points into, where it points into this body at
    // all. `let r = &x` makes r point into x, and `let s = r` makes s point
    // where r did -- so a reference is followed however many names it is
    // handed through.
    from:    HashMap<TTIRLocalId, Vec<(TTIRLocalId, TTIRExprId)>>,
}

impl<'a> Checker<'a> {
    pub fn new(p: &'a TTIRProgram) -> Checker<'a> {
        Checker {
            p,
            copies: Copies::of(p),
            errors: Diagnostics::new(),
            body: 0,
            generic: Vec::new(),
            gone: Gone::default(),
            held: Vec::new(),
            marks: Vec::new(),
            breaks: Vec::new(),
            quiet: false,
            leaves: false,
            depth: HashMap::new(),
            said_of: Vec::new(),
            from_of: Vec::new(),
            when: HashMap::new(),
            last: HashMap::new(),
            now: 0,
            caught: HashMap::new(),
            from: HashMap::new(),
        }
    }

    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    // Every fn of every module, and the two names the compiler knows.
    pub fn check(&mut self) -> &Diagnostics {
        for held in self.copies.both() {
            let item = &self.p.items[held];
            self.errors.push(
                Diagnostic::error(
                    format!("`{}` is both `Copy` and `Drop`", name_of(held, self.p)),
                    Span::at(item.line, item.col),
                )
                .with_label("this is declared both")
                .with_help("a value that has something to release is a value there had better be one of"),
            );
        }

        for id in 0..self.p.items.len() {
            let TTIRItemKind::Fn(f) = &self.p.items[id].kind else { continue };
            if f.body.is_none() {
                continue;
            }
            self.walk_fn(&f.clone());
        }
        &self.errors
    }

    // One fn: its body, walked, and then what its body gives back.
    fn walk_fn(&mut self, f: &TTIRFn) {
        let Some(body) = f.body else { return };
        self.leaves = self.holds_ref(f.ret);
        let args: Vec<TTIRLocalId> = f.params.iter().filter_map(|p| p.slot).collect();
        self.walk_body_of(body, f.generics.clone(), &args, &[]);
    }

    // ---- How long a borrow is in hand ------------------------------------
    //
    // A borrow lasts from where it is taken to the last place anything can
    // reach through it, which is where the slot holding it is last read. That
    // is sharper than the end of the block and is the rule Rust reached with
    // NLL; the prose allows either, its own lifetime rule being "only ever
    // answered too conservatively", and the sharper one turns down less.
    //
    // Everything is numbered in the order it was written, so "later" is a
    // bigger number. A loop is the one place that is not enough: what is
    // written above a use runs below it on the next turn, so every slot last
    // read inside a loop is held to the loop's own end.

    fn measure(&mut self, body: TTIRBodyId) {
        self.when.clear();
        self.last.clear();
        let value = self.p.bodies[body].value;
        let mut clock = 0;
        self.number(value, &mut clock);
    }

    fn number(&mut self, id: TTIRExprId, clock: &mut usize) {
        *clock += 1;
        let at = *clock;
        self.when.insert(id, at);
        let inner = |held: &mut Self, kids: Vec<TTIRExprId>, clock: &mut usize| {
            for kid in kids {
                held.number(kid, clock);
            }
        };
        match self.p.exprs[id].kind.clone() {
            TTIRExprKind::Local(local) => {
                let held = self.last.entry(local).or_insert(at);
                *held = (*held).max(at);
            }
            TTIRExprKind::Literal(_) | TTIRExprKind::Item(_) | TTIRExprKind::SelfExpr => {}
            TTIRExprKind::Field { base, .. } | TTIRExprKind::TupleIndex { base, .. } => {
                inner(self, vec![base], clock)
            }
            TTIRExprKind::Index { base, index } => inner(self, vec![base, index], clock),
            TTIRExprKind::Call { callee, args } => {
                inner(self, std::iter::once(callee).chain(args).collect(), clock)
            }
            TTIRExprKind::Method { recv, args, .. } => {
                inner(self, std::iter::once(recv).chain(args).collect(), clock)
            }
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => inner(self, fields, clock),
            TTIRExprKind::Map { entries, .. } => {
                inner(self, entries.iter().flat_map(|&(k, v)| [k, v]).collect(), clock)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => {
                inner(self, vec![operand], clock)
            }
            TTIRExprKind::Binary { lhs, rhs, .. } => inner(self, vec![lhs, rhs], clock),
            TTIRExprKind::Assign { place, value, .. } => inner(self, vec![value, place], clock),
            TTIRExprKind::Range { start, end, .. } => {
                inner(self, [start, end].into_iter().flatten().collect(), clock)
            }
            // A closure's body is a body of its own and is numbered with its
            // own fn. What belongs here is that it read every name it captured,
            // and it reads them for as long as the closure is in hand -- which
            // is the slot the closure went into, and that slot's last use is
            // what this numbering finds.
            TTIRExprKind::Closure { captures, .. } => {
                for held in captures {
                    let held = self.last.entry(held.outer).or_insert(at);
                    *held = (*held).max(at);
                }
            }
            TTIRExprKind::Block { stmts, tail } => {
                for stmt in &stmts {
                    match stmt {
                        TTIRStmt::Let { local, init, .. } => {
                            if let Some(init) = init {
                                self.number(*init, clock);
                            }
                            // Bound here and read nowhere: it still stands
                            // until something reads it, and nothing does.
                            self.last.entry(*local).or_insert(*clock);
                        }
                        TTIRStmt::Expr { expr, .. } => self.number(*expr, clock),
                        TTIRStmt::Item(_) => {}
                    }
                }
                if let Some(tail) = tail {
                    self.number(tail, clock);
                }
            }
            TTIRExprKind::If { cond, then, els } => {
                inner(self, [Some(cond), Some(then), els].into_iter().flatten().collect(), clock)
            }
            TTIRExprKind::Match { scrutinee, arms } => {
                self.number(scrutinee, clock);
                for arm in &arms {
                    self.number(arm.body, clock);
                }
            }
            // The two that come round again.
            TTIRExprKind::While { cond, body } => {
                let from = *clock;
                self.number(cond, clock);
                self.number(body, clock);
                self.round(from, *clock);
            }
            TTIRExprKind::For { local, iter, body } => {
                let from = *clock;
                self.number(iter, clock);
                self.number(body, clock);
                self.last.entry(local).or_insert(*clock);
                self.round(from, *clock);
            }
            TTIRExprKind::Return(value) | TTIRExprKind::Break(value) => {
                inner(self, value.into_iter().collect(), clock)
            }
            TTIRExprKind::Continue => {}
        }
    }

    // What is written above a use runs below it on the next turn, so a slot
    // last read anywhere inside a loop is in hand for all of it.
    fn round(&mut self, from: usize, to: usize) {
        for held in self.last.values_mut() {
            if *held > from && *held <= to {
                *held = to;
            }
        }
    }

    fn walk_body(&mut self, body: TTIRBodyId, generic: Vec<TTIRGeneric>) {
        self.walk_body_of(body, generic, &[], &[]);
    }

    // `args` is the slots the parameters were put in. They came from outside,
    // so they outlive everything the body declares, which is depth 0.
    fn walk_body_of(
        &mut self,
        body: TTIRBodyId,
        generic: Vec<TTIRGeneric>,
        args: &[TTIRLocalId],
        caught: &[TTIRLocalId],
    ) {
        self.body = body;
        self.generic = generic;
        self.measure(body);
        self.depth.clear();
        self.from.clear();
        self.said_of.clear();
        for &slot in args {
            self.depth.insert(slot, 0);
        }
        // A captured name came from outside and goes on living there -- by
        // reference it is the enclosing frame's, and by value it is the
        // closure's, and either way it outlives the body's own blocks.
        for &slot in caught {
            self.depth.insert(slot, 0);
        }
        self.gone = Gone::default();
        self.held.clear();
        self.marks.clear();
        self.breaks.clear();
        let value = self.p.bodies[body].value;
        self.expr(value, Use::Read);
        // The tail. A `return` is checked where it stands, since what follows
        // it is not walked; what a body falls off the end of is checked here,
        // and a closure's body falls off the end of itself as much as a fn's.
        let (line, col) = (self.p.exprs[value].line, self.p.exprs[value].col);
        self.escaping(value, line, col);
    }

    // ---- Escapes ---------------------------------------------------------
    //
    //     Every reference in a signature with no lifetime of its own gets one,
    //     and a reference in the return type gets the shortest-lived of the
    //     ones the parameters brought in.                (docs/prose.txt, §3)
    //
    // A signature's regions are all brought in from outside, so a reference
    // rooted at a local of this body stands in none of them -- it is good until
    // the end of the block that declared it and the signature promises longer.
    // That is the whole of the check, and it needs no second frame: the caller
    // side of `outlives` is a different pass.

    // Does this type hold a reference standing in a region of the signature?
    // Region 0 is what a reference in a body gets, where how long it is good
    // for was nobody's question -- so it does not count.
    fn holds_ref(&self, ty: TyId) -> bool {
        self.holds_ref_past(ty, true, &mut Vec::new())
    }

    // The same question asked of a closure's result rather than a signature's.
    // Every reference a body takes stands in region 0 -- how long one held in a
    // local is good for is not what a signature promises -- so `holds_ref` can
    // see none of them, and what a closure gives back is worked out in a body.
    fn holds_any_ref(&self, ty: TyId) -> bool {
        self.holds_ref_past(ty, false, &mut Vec::new())
    }

    // `seen` is the declarations already being looked through. A struct cannot
    // hold itself by value, so a cycle is not reachable today -- but this walks
    // declarations rather than types, and a walk over declarations that cannot
    // be stopped is a hang waiting for a language change.
    fn holds_ref_past(&self, ty: TyId, signature: bool, seen: &mut Vec<TTIRItemId>) -> bool {
        match &self.p.types[ty] {
            Ty::Ref { life, inner, .. } => {
                (!signature || *life != 0) || self.holds_ref_past(*inner, signature, seen)
            }
            // A named type holds a reference where what it was declared to hold
            // does. The regions are the declaration's and not the use's -- a
            // `Held` written bare carries the same reference a `Held<'a>` does,
            // and it is the declaration that says so.
            Ty::Named { item, args, .. } => {
                if args.iter().any(|&a| self.holds_ref_past(a, signature, seen)) {
                    return true;
                }
                if seen.contains(item) {
                    return false;
                }
                seen.push(*item);
                let held = match &self.p.items[*item].kind {
                    TTIRItemKind::Struct { fields, .. } => {
                        fields.iter().any(|f| self.holds_ref_past(f.ty, signature, seen))
                    }
                    TTIRItemKind::Enum { variants, .. } => {
                        variants.iter().any(|v| match &v.payload {
                            TTIRPayload::None => false,
                            TTIRPayload::Tuple(tys) => {
                                tys.iter().any(|&t| self.holds_ref_past(t, signature, seen))
                            }
                            TTIRPayload::Named(fields) => {
                                fields.iter().any(|f| self.holds_ref_past(f.ty, signature, seen))
                            }
                        })
                    }
                    _ => false,
                };
                seen.pop();
                held
            }
            // A fn type says nothing about what a closure behind it captured,
            // so the question cannot be answered here and is left to the value:
            // `roots` returns nothing for a `move` closure or a plain fn, and
            // what it returns for one that captured by reference is what this
            // would have wanted to know.
            Ty::Fn { .. } => true,
            Ty::Tuple(members) => members.iter().any(|&m| self.holds_ref_past(m, signature, seen)),
            Ty::Array { elem, .. } | Ty::Run(elem) => self.holds_ref_past(*elem, signature, seen),
            Ty::GC(inner) => self.holds_ref_past(*inner, signature, seen),
            _ => false,
        }
    }

    // Every region standing anywhere in a type.
    fn regions_in(&self, ty: TyId, out: &mut Vec<RegionId>) {
        match &self.p.types[ty] {
            Ty::Ref { life, inner, .. } => {
                if *life != 0 && !out.contains(life) {
                    out.push(*life);
                }
                self.regions_in(*inner, out);
            }
            Ty::Tuple(members) => {
                for &m in members {
                    self.regions_in(m, out);
                }
            }
            Ty::Array { elem, .. } | Ty::Run(elem) => self.regions_in(*elem, out),
            Ty::Ptr(inner) | Ty::GC(inner) => self.regions_in(*inner, out),
            Ty::Named { args, regions, .. } => {
                for &r in regions {
                    if r != 0 && !out.contains(&r) {
                        out.push(r);
                    }
                }
                for &a in args {
                    self.regions_in(a, out);
                }
            }
            _ => {}
        }
    }

    // Which of a fn's parameters its result is tied to, or `None` where its
    // result is tied to nothing because it gives back no reference.
    //
    // This is the other half of the bargain §3 strikes. The declaration was
    // never refused for want of a lifetime -- every reference in it got a
    // region and the return was held to all of them -- and here is where that
    // is paid for: a caller is held to every parameter the return's region can
    // be reached from. Writing `'a` is what buys the precision back, and it
    // buys it exactly here, by leaving a parameter out of this list.
    fn tied(&self, item: TTIRItemId) -> Option<Vec<usize>> {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return None };
        let mut reach = Vec::new();
        self.regions_in(f.ret, &mut reach);
        if reach.is_empty() {
            // A named type carries references without carrying their regions:
            // `Ty::Named` holds types, and a `Held<'a>` loses the `'a` on the
            // way in. So the regions cannot be compared and the answer is the
            // one the elision rule would have given before anybody wrote a
            // lifetime -- tied to everything, which is never wrong and is what
            // §3 means by spending precision at the call.
            if self.holds_ref(f.ret) {
                let Ty::Fn { params, .. } = &self.p.types[f.ty] else { return None };
                return Some((0..params.len()).collect());
            }
            return None;
        }
        // Everything that outlives something already reached, until nothing
        // more is. A `(longer, shorter)` pair says the caller has to make
        // `longer` last at least as long, so `longer` is one more region the
        // result stands or falls with.
        loop {
            let grown: Vec<RegionId> = f
                .outlives
                .iter()
                .filter(|(longer, shorter)| reach.contains(shorter) && !reach.contains(longer))
                .map(|&(longer, _)| longer)
                .collect();
            if grown.is_empty() {
                break;
            }
            reach.extend(grown);
        }
        let Ty::Fn { params, .. } = &self.p.types[f.ty] else { return None };
        Some(
            params
                .iter()
                .enumerate()
                .filter(|(_, p)| {
                    let mut held = Vec::new();
                    self.regions_in(**p, &mut held);
                    held.iter().any(|r| reach.contains(r))
                })
                .map(|(i, _)| i)
                .collect(),
        )
    }

    // ---- Bounds at the call ----------------------------------------------
    //
    //     Too conservative a signature is turned down at the call and not at
    //     the declaration.                                (docs/prose.txt, §3)
    //
    // A `'a: 'b` and a `T: 'a` say nothing a declaration can be refused for --
    // they are what a *caller* is held to. So they are checked here, and what
    // they are checked against is a region substitution: what each of the
    // callee's regions stands for on this side, worked out from what was handed
    // to the parameters it appears in.
    //
    // A caller-side lifetime is a depth, the same ordering everything else in
    // this pass uses, and 0 means "came from outside and outlives the body".

    // What one callee region or type parameter was handed: how long the value
    // is good for, and the slot that made it so, for the message.
    fn supplied(
        &self,
        declared: TyId,
        held: (usize, Option<TTIRLocalId>),
        regions: &mut HashMap<RegionId, (usize, Option<TTIRLocalId>)>,
        params: &mut HashMap<usize, (usize, Option<TTIRLocalId>)>,
    ) {
        // The shortest life wins: a region standing in two places is good for
        // no longer than the shorter of them.
        let keep = |at: &mut HashMap<_, (usize, Option<TTIRLocalId>)>, key| {
            let entry = at.entry(key).or_insert(held);
            if held.0 > entry.0 {
                *entry = held;
            }
        };
        match &self.p.types[declared] {
            Ty::Ref { life, inner, .. } => {
                if *life != 0 {
                    keep(regions, *life);
                }
                self.supplied(*inner, held, regions, params);
            }
            Ty::Named { args, regions: rs, .. } => {
                for &r in rs {
                    if r != 0 {
                        keep(regions, r);
                    }
                }
                for &a in args {
                    self.supplied(a, held, regions, params);
                }
            }
            Ty::Param { index, .. } => keep(params, *index),
            Ty::Tuple(members) => {
                for &m in members {
                    self.supplied(m, held, regions, params);
                }
            }
            Ty::Array { elem, .. } | Ty::Run(elem) => {
                self.supplied(*elem, held, regions, params)
            }
            Ty::Ptr(inner) | Ty::GC(inner) => self.supplied(*inner, held, regions, params),
            Ty::Fn { params: ps, ret, .. } => {
                let (ps, ret) = (ps.clone(), *ret);
                for p in ps {
                    self.supplied(p, held, regions, params);
                }
                self.supplied(ret, held, regions, params);
            }
            _ => {}
        }
    }

    // Which borrows taken working a value out get as far as the value. The
    // same walk `roots` is, asking the other half of the question: `roots` says
    // what a value points into, and this says which `&` put it there.
    //
    // What it turns on at a call is the callee's own signature -- `len(&x)`
    // gives back an `i32` and can hold nothing, so the `&x` is a temporary and
    // goes with the statement; `pick(&x, &y)` gives back a reference tied to
    // both, so both get as far as whatever the result is bound to.
    fn reaching(&self, id: TTIRExprId) -> Vec<TTIRExprId> {
        let mut out = Vec::new();
        self.walk_reaching(id, &mut out);
        out
    }

    fn walk_reaching(&self, id: TTIRExprId, out: &mut Vec<TTIRExprId>) {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), .. } => out.push(id),
            // A closure holds what it captured by reference for as long as it
            // is in hand, so the closure is what took those borrows.
            TTIRExprKind::Closure { captures, .. } => {
                if captures.iter().any(|c| matches!(c.mode, TTIRCaptureMode::Ref(_))) {
                    out.push(id);
                }
            }
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.walk_reaching(*base, out),
            TTIRExprKind::Cast(inner) => self.walk_reaching(*inner, out),
            TTIRExprKind::Call { callee, args } => match self.callee(*callee).map(|i| self.tied(i)) {
                Some(None) => {}
                Some(Some(ties)) => {
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&i) {
                            self.walk_reaching(arg, out);
                        }
                    }
                }
                None => {
                    for &arg in args {
                        self.walk_reaching(arg, out);
                    }
                }
            },
            TTIRExprKind::Method { recv, item, args } => {
                if let Some(ties) = self.tied(*item) {
                    if ties.contains(&0) {
                        self.walk_reaching(*recv, out);
                    }
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&(i + 1)) {
                            self.walk_reaching(arg, out);
                        }
                    }
                }
            }
            TTIRExprKind::ArrayLit(parts)
            | TTIRExprKind::TupleLit(parts)
            | TTIRExprKind::StructLit { fields: parts, .. }
            | TTIRExprKind::VariantLit { fields: parts, .. }
            | TTIRExprKind::Set { elems: parts, .. } => {
                for &part in parts {
                    self.walk_reaching(part, out);
                }
            }
            TTIRExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.walk_reaching(key, out);
                    self.walk_reaching(value, out);
                }
            }
            TTIRExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.walk_reaching(*held, out);
                }
            }
            TTIRExprKind::Block { tail, .. } => {
                if let Some(tail) = tail {
                    self.walk_reaching(*tail, out);
                }
            }
            TTIRExprKind::If { then, els, .. } => {
                self.walk_reaching(*then, out);
                if let Some(els) = els {
                    self.walk_reaching(*els, out);
                }
            }
            TTIRExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.walk_reaching(arm.body, out);
                }
            }
            _ => {}
        }
    }

    // What a parameter's regions were handed, worked out against the argument
    // as it was written. A `(&'a i32, &'b i32)` given a tuple written on the
    // spot answers for each half on its own; anything this cannot take apart
    // answers for the argument whole, which is the blunt end of the same rule.
    fn supplied_from(
        &self,
        declared: TyId,
        arg: TTIRExprId,
        regions: &mut HashMap<RegionId, (usize, Option<TTIRLocalId>)>,
        params: &mut HashMap<usize, (usize, Option<TTIRLocalId>)>,
    ) {
        // A block stands for its tail and a cast for what it casts.
        let arg = match &self.p.exprs[arg].kind {
            TTIRExprKind::Cast(inner) => *inner,
            TTIRExprKind::Block { tail: Some(tail), .. } => *tail,
            _ => arg,
        };
        match (&self.p.types[declared], &self.p.exprs[arg].kind) {
            (Ty::Tuple(members), TTIRExprKind::TupleLit(parts))
                if members.len() == parts.len() =>
            {
                let (members, parts) = (members.clone(), parts.clone());
                for (want, part) in members.iter().zip(parts.iter()) {
                    self.supplied_from(*want, *part, regions, params);
                }
            }
            (Ty::Array { elem, .. }, TTIRExprKind::ArrayLit(parts)) => {
                let (elem, parts) = (*elem, parts.clone());
                for part in parts {
                    self.supplied_from(elem, part, regions, params);
                }
            }
            _ => self.supplied(declared, self.handed(arg), regions, params),
        }
    }

    // How long an argument's value is good for, and the slot that says so.
    fn handed(&self, arg: TTIRExprId) -> (usize, Option<TTIRLocalId>) {
        let mut worst = (0, None);
        for (root, _) in self.roots(arg) {
            let lives = self.lives(root);
            if lives >= worst.0 {
                worst = (lives, Some(root));
            }
        }
        worst
    }

    // The same, for a receiver a method borrows rather than takes. `&'a self`
    // is the one borrow nobody writes, so the region stands for how long the
    // receiver itself is good for and not for what it points into.
    fn handed_borrowed(&self, recv: TTIRExprId) -> (usize, Option<TTIRLocalId>) {
        match self.place(recv) {
            Some(place) => (self.lives(place.root), Some(place.root)),
            // A receiver with no place of its own is a value the compiler gave
            // one, and one it gave lasts as long as the call.
            None => self.handed(recv),
        }
    }

    // Every bound a signature was written with, held against what this call
    // handed it. `given` is the arguments in declaration order, the receiver
    // standing where parameter 0 does.
    fn bounds_at_call(
        &mut self,
        item: TTIRItemId,
        given: &[Handed],
        at: Span,
    ) {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return };
        let (generics, wheres) = (f.generics.clone(), f.wheres.clone());
        if generics.iter().all(|g| bounds_none(g)) && wheres.is_empty() {
            return;
        }
        let Ty::Fn { params: declared, .. } = &self.p.types[f.ty] else { return };
        let declared = declared.clone();

        let mut regions = HashMap::new();
        let mut params = HashMap::new();
        for (i, held) in given.iter().enumerate() {
            let Some(&want) = declared.get(i) else { continue };
            match held {
                // Taken apart where it was written as one thing built out of
                // several, so each region answers for its own half.
                Handed::Written(arg) => {
                    self.supplied_from(want, *arg, &mut regions, &mut params)
                }
                Handed::Whole(held) => self.supplied(want, *held, &mut regions, &mut params),
            }
        }

        // A region nothing was handed is one the caller may pick freely, and
        // the freest pick is the longest life. So: outlives everything.
        let of_region = |r: RegionId| regions.get(&r).copied().unwrap_or((0, None));

        let mut asked: Vec<(String, (usize, Option<TTIRLocalId>), RegionId)> = Vec::new();
        // A `Ty::Param` counts in the type parameters alone, so the position
        // among them is what a `T: 'a` is looked up by and not the position in
        // the list as written.
        let mut i = 0;
        for g in generics.iter() {
            match g {
                // `'a: 'b`, written among the parameters.
                TTIRGeneric::Life { name, region, bounds } => {
                    for &shorter in bounds {
                        asked.push((format!("`'{}`", name), of_region(*region), shorter));
                    }
                }
                // `T: 'a`. What T was handed is what has to outlive the region.
                TTIRGeneric::Type { name, bounds } => {
                    for bound in bounds {
                        if let TTIRBound::Life(shorter) = bound {
                            let held = params.get(&i).copied().unwrap_or((0, None));
                            asked.push((format!("`{}`", name), held, *shorter));
                        }
                    }
                    i += 1;
                }
            }
        }
        for pred in &wheres {
            // A predicate about a parameter was folded into that parameter's
            // bounds; what is left is a region or a type that was built.
            let held = match &pred.subject {
                TTIRSubject::Region(r) => {
                    (format!("`'{}`", self.life_name(&generics, *r)), of_region(*r))
                }
                TTIRSubject::Type(ty) => {
                    let mut regions_in = HashMap::new();
                    let mut params_in = HashMap::new();
                    self.supplied(*ty, (0, None), &mut regions_in, &mut params_in);
                    let worst = regions_in
                        .keys()
                        .map(|r| of_region(*r))
                        .chain(params_in.keys().map(|i| params.get(i).copied().unwrap_or((0, None))))
                        .max_by_key(|(lives, _)| *lives)
                        .unwrap_or((0, None));
                    (self.spell_subject(*ty), worst)
                }
            };
            for bound in &pred.bounds {
                if let TTIRBound::Life(shorter) = bound {
                    asked.push((held.0.clone(), held.1, *shorter));
                }
            }
        }

        for (what, (lives, blame), shorter) in asked {
            let (wanted, against) = of_region(shorter);
            // Longer-lived is a smaller depth. A bound that holds is one where
            // what was handed to the left outlives what was handed to the right.
            if lives <= wanted {
                continue;
            }
            let named = format!("`'{}`", self.life_name(&generics, shorter));
            let mut said = Diagnostic::error(
                format!("{} does not outlive {}", what, named),
                at,
            )
            .with_label("this call is where it has to");
            if let Some(blame) = blame {
                let local = &self.p.bodies[self.body].locals[blame];
                said = said.with_secondary(
                    Span::at(local.line, local.col),
                    format!("{} was handed this", what),
                );
            }
            if let Some(against) = against {
                let local = &self.p.bodies[self.body].locals[against];
                said = said.with_secondary(
                    Span::at(local.line, local.col),
                    format!("{} was handed this, which lasts longer", named),
                );
            }
            self.say(
                said.with_note(format!(
                    "the signature says {} outlives {}",
                    what, named
                ))
                .with_help("a bound is a promise the caller keeps, so what is handed in has to keep it"),
            );
        }
    }

    // What a region is called in the declaration that declared it.
    fn life_name(&self, generics: &[TTIRGeneric], region: RegionId) -> String {
        for g in generics {
            if let TTIRGeneric::Life { name, region: held, .. } = g {
                if *held == region {
                    return name.clone();
                }
            }
        }
        // A region with no name is one the rule made, and the rule makes one
        // per reference -- so this is a reference the reader did not name.
        "_".to_string()
    }

    fn spell_subject(&self, ty: TyId) -> String {
        match &self.p.types[ty] {
            Ty::Named { item, .. } => format!("`{}`", name_of(*item, self.p)),
            Ty::Param { name, .. } => format!("`{}`", name),
            _ => "what this `where` is about".to_string(),
        }
    }

    // The item a callee expression names, where it names one. A call through a
    // closure or a fn held in a variable names none, and then nothing is known
    // about what its result is tied to.
    fn callee(&self, id: TTIRExprId) -> Option<TTIRItemId> {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Item(item) => Some(*item),
            _ => None,
        }
    }

    // The locals of *this* body that a value points into. Empty is the answer
    // for anything that came from outside, which is why a parameter has no
    // entry in `from` and a literal contributes nothing.
    // Each root paired with the expression that reached it, so a refusal points
    // at the `&x` the reader wrote and not at whatever holds it.
    fn roots(&self, id: TTIRExprId) -> Vec<(TTIRLocalId, TTIRExprId)> {
        let mut out = Vec::new();
        self.walk_roots(id, &mut out);
        out
    }

    fn walk_roots(&self, id: TTIRExprId, out: &mut Vec<(TTIRLocalId, TTIRExprId)>) {
        let add = |root: TTIRLocalId, out: &mut Vec<(TTIRLocalId, TTIRExprId)>| {
            if !out.iter().any(|&(held, _)| held == root) {
                out.push((root, id));
            }
        };
        match &self.p.exprs[id].kind {
            // `&x` and `*x` both point at the place x names.
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(_), operand } => {
                if let Some(place) = self.place(*operand) {
                    add(place.root, out);
                }
            }
            // A name points where whatever was put in it pointed. A parameter
            // has no entry, which is the answer: it points outside.
            TTIRExprKind::Local(local) => {
                for &(root, took) in self.from.get(local).into_iter().flatten() {
                    if !out.iter().any(|&(held, _)| held == root) {
                        // The `&` that took it, however many names it has been
                        // handed through since -- which is the line to show.
                        out.push((root, took));
                    }
                }
            }
            // Reaching into a place does not change which place it is rooted
            // at, and a reference is reached through as the place it refers to.
            TTIRExprKind::Field { base, .. }
            | TTIRExprKind::TupleIndex { base, .. }
            | TTIRExprKind::Index { base, .. } => self.walk_roots(*base, out),
            TTIRExprKind::Cast(inner) => self.walk_roots(*inner, out),
            // "a reference in the return type gets the shortest-lived of the
            // ones the parameters brought in" -- the callee's rule read from
            // this side. What its result may point into is what was handed to
            // the parameters its result is tied to, and no more: a `'a` written
            // in the signature is what shortens that list, and this is where
            // the caller gets the precision it paid for.
            TTIRExprKind::Call { callee, args } => {
                let ties = self.callee(*callee).map(|item| self.tied(item));
                match ties {
                    // A fn whose result gives back no reference. Nothing that
                    // was handed in can be reached through what comes out.
                    Some(None) => {}
                    Some(Some(ties)) => {
                        for (i, &arg) in args.iter().enumerate() {
                            if ties.contains(&i) {
                                self.walk_roots(arg, out);
                            }
                        }
                    }
                    // A callee this cannot read -- a closure, or a fn in a
                    // slot. Every argument, which is the answer that is never
                    // wrong.
                    None => {
                        for &arg in args {
                            self.walk_roots(arg, out);
                        }
                    }
                }
            }
            // The same, with the receiver standing where parameter 0 does.
            TTIRExprKind::Method { recv, item, args } => match self.tied(*item) {
                None => {}
                Some(ties) => {
                    if ties.contains(&0) {
                        self.walk_roots(*recv, out);
                    }
                    for (i, &arg) in args.iter().enumerate() {
                        if ties.contains(&(i + 1)) {
                            self.walk_roots(arg, out);
                        }
                    }
                }
            },
            // "a closure that captures by reference cannot outlive what it
            // captured, and `move` is the only thing that lets one be
            // returned" (§8). A closure is the one value here whose type says
            // nothing about what is inside it, so the captures are asked
            // instead: what it took by reference it points at, and what it took
            // by value it points at only as far as that value did.
            TTIRExprKind::Closure { captures, .. } => {
                for held in captures {
                    match held.mode {
                        TTIRCaptureMode::Ref(_) => {
                            // The slot itself, since the closure holds a
                            // reference to it -- and wherever that slot points,
                            // since reading through the one reaches the other.
                            add(held.outer, out);
                            for &(root, _) in self.from.get(&held.outer).into_iter().flatten() {
                                add(root, out);
                            }
                        }
                        // "By value is a copy where the name's type copies and
                        // a move where it does not": the slot is not pointed at
                        // either way, and what the value points at goes with it.
                        TTIRCaptureMode::Value => {
                            for &(root, _) in self.from.get(&held.outer).into_iter().flatten() {
                                add(root, out);
                            }
                        }
                    }
                }
            }
            // What is built out of references points where they did, whatever
            // was built: a struct and a variant carry them in named places and
            // an array, a tuple, a map, a set and a range in unnamed ones, and
            // none of that changes where the references came from.
            TTIRExprKind::ArrayLit(parts)
            | TTIRExprKind::TupleLit(parts)
            | TTIRExprKind::StructLit { fields: parts, .. }
            | TTIRExprKind::VariantLit { fields: parts, .. }
            | TTIRExprKind::Set { elems: parts, .. } => {
                for &part in parts {
                    self.walk_roots(part, out);
                }
            }
            TTIRExprKind::Map { entries, .. } => {
                for &(key, value) in entries {
                    self.walk_roots(key, out);
                    self.walk_roots(value, out);
                }
            }
            TTIRExprKind::Range { start, end, .. } => {
                for held in [start, end].into_iter().flatten() {
                    self.walk_roots(*held, out);
                }
            }
            // Every way out of a block or a branch is a way the value can come.
            TTIRExprKind::Block { tail, .. } => {
                if let Some(tail) = tail {
                    self.walk_roots(*tail, out);
                }
            }
            TTIRExprKind::If { then, els, .. } => {
                self.walk_roots(*then, out);
                if let Some(els) = els {
                    self.walk_roots(*els, out);
                }
            }
            TTIRExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.walk_roots(arm.body, out);
                }
            }
            _ => {}
        }
    }

    // What a body gives back, held to what its signature promised.
    // How long a slot is good for. An unrecorded one is treated as coming from
    // outside: a binding this pass never walked past is not a thing to refuse a
    // program over.
    fn lives(&self, root: TTIRLocalId) -> usize {
        self.depth.get(&root).copied().unwrap_or(0)
    }

    // A block is where a value stands, not what it is: what comes out of one is
    // its tail, and the tail is the line a refusal points at.
    fn leaving(&self, id: TTIRExprId) -> TTIRExprId {
        let mut held = id;
        while let TTIRExprKind::Block { tail: Some(tail), .. } = &self.p.exprs[held].kind {
            held = *tail;
        }
        held
    }

    // A value put somewhere that outlives it. `held` is how long the place that
    // takes it is good for -- 0 for what a signature gives back, since every
    // region of a signature was brought in from outside and outlives the body.
    fn outstays(&mut self, value: TTIRExprId, held: usize, what: &str, at: Span) {
        let leaves = self.leaving(value);
        let at = if leaves == value {
            at
        } else {
            Span::at(self.p.exprs[leaves].line, self.p.exprs[leaves].col)
        };
        for (root, took) in self.roots(value) {
            if self.lives(root) <= held || self.said_of.contains(&root) {
                continue;
            }
            if !self.quiet {
                self.said_of.push(root);
            }
            let local = &self.p.bodies[self.body].locals[root];
            let name = self.name(&Place::of(root));
            let mut said =
                Diagnostic::error(format!("`{}` does not live long enough", name), at)
                    .with_label(what);
            // Where the `&` was written, when that is not the line already
            // shown: a reference handed through a name leaves in one place and
            // was taken in another.
            let took = Span::at(self.p.exprs[took].line, self.p.exprs[took].col);
            if (took.line, took.col) != (at.line, at.col) {
                said = said.with_secondary(took, "the reference was taken");
            }
            said = said.with_secondary(Span::at(local.line, local.col), "it was bound");
            self.say(if held == 0 {
                said.with_note("what a signature gives back is good for as long as what its parameters brought in, and this was not one of them")
                    .with_help("give back the value itself, or a reference to something the caller handed in")
            } else {
                said.with_note("a reference is good until the end of the block that holds what it refers to")
                    .with_help("move what it refers to out to where it has to last, or keep the reference where it was taken")
            });
        }
    }

    fn escaping(&mut self, value: TTIRExprId, line: usize, col: usize) {
        if !self.leaves {
            return;
        }
        self.outstays(value, 0, "this gives back a reference to it", Span::at(line, col));
    }

    // ---- Places ----------------------------------------------------------

    // The place an expression names, where it names one. A call names none, and
    // neither does a literal: "`&x` asks... any place at all, and a value with
    // no home of its own, which the compiler gives one" (§5).
    fn place(&self, id: TTIRExprId) -> Option<Place> {
        match &self.p.exprs[id].kind {
            TTIRExprKind::Local(local) => Some(Place::of(*local)),
            TTIRExprKind::Field { base, index } => {
                Some(self.reach(*base)?.then(Step::Field(*index)))
            }
            TTIRExprKind::TupleIndex { base, index } => {
                Some(self.reach(*base)?.then(Step::Tuple(*index)))
            }
            TTIRExprKind::Index { base, .. } => Some(self.reach(*base)?.then(Step::Index)),
            _ => None,
        }
    }

    // The base of a projection, with a `Deref` put in where it crosses a
    // reference. Nothing writes that step -- a reference is read and reached
    // into exactly as the place it refers to is (§3) -- so the type is the only
    // thing that says one happened.
    fn reach(&self, base: TTIRExprId) -> Option<Place> {
        let place = self.place(base)?;
        match &self.p.types[self.p.exprs[base].ty] {
            Ty::Ref { .. } => Some(place.then(Step::Deref)),
            _ => Some(place),
        }
    }

    // What to call a place in a message. The root's name and the way in, which
    // is what the reader wrote.
    fn name(&self, place: &Place) -> String {
        let local = &self.p.bodies[self.body].locals[place.root];
        let mut out = match &local.name {
            TIRBinding::Name(name) => name.clone(),
            TIRBinding::Discard => "_".to_string(),
            TIRBinding::SelfRecv(..) => "self".to_string(),
        };
        for step in &place.path {
            match step {
                Step::Field(i) => out.push_str(&format!(".{}", i)),
                Step::Tuple(i) => out.push_str(&format!(".{}", i)),
                Step::Index => out.push_str("[..]"),
                // A reference is transparent, so nothing is written for one and
                // nothing is shown for one either.
                Step::Deref => {}
            }
        }
        out
    }

    fn say(&mut self, d: Diagnostic) {
        if !self.quiet {
            self.errors.push(d);
        }
    }
}

// ---- The walk -------------------------------------------------------------

impl<'a> Checker<'a> {
    // One expression, and what using it does. `how` is what the *place* this
    // expression names is being used for, where it names one.
    fn expr(&mut self, id: TTIRExprId, how: Use) -> Flow {
        let (line, col) = (self.p.exprs[id].line, self.p.exprs[id].col);
        self.now = self.when.get(&id).copied().unwrap_or(self.now);
        match self.p.exprs[id].kind.clone() {
            TTIRExprKind::Literal(_) | TTIRExprKind::Item(_) | TTIRExprKind::SelfExpr => {
                Flow::Normal
            }

            // A name, and every way of reaching into one. Reading it is what
            // asks whether it is still there.
            TTIRExprKind::Local(_)
            | TTIRExprKind::Field { .. }
            | TTIRExprKind::TupleIndex { .. } => {
                if let Some(place) = self.place(id) {
                    self.reading(&place, how, line, col);
                }
                Flow::Normal
            }
            TTIRExprKind::Index { base, index } => {
                if self.expr(index, Use::Read).left() {
                    return Flow::Left;
                }
                let _ = base;
                if let Some(place) = self.place(id) {
                    self.reading(&place, how, line, col);
                }
                Flow::Normal
            }

            // Taking a reference, and the one that is not one: "`addr x` is the
            // third of them and the odd one: what it gives back is a `ptr` and
            // not a reference, so none of the above is asked of it and none of
            // it is promised" (§5).
            TTIRExprKind::Unary { op: TIRUnaryOp::Ref(op), operand } => {
                self.borrowing(id, operand, op, line, col)
            }
            TTIRExprKind::Unary { op: TIRUnaryOp::Addr, operand } => {
                self.expr(operand, Use::Read)
            }
            TTIRExprKind::Unary { operand, .. } | TTIRExprKind::Cast(operand) => {
                self.expr(operand, Use::Read)
            }

            TTIRExprKind::Binary { lhs, rhs, .. } => {
                if self.expr(lhs, Use::Read).left() {
                    return Flow::Left;
                }
                self.expr(rhs, Use::Read)
            }

            // "the right of an assignment" is one of the four places a value is
            // handed over (§2), and the left is a place being filled.
            TTIRExprKind::Assign { op, place, value } => {
                if self.expr(value, Use::Pass).left() {
                    return Flow::Left;
                }
                self.moving(value);
                // A compound assignment reads the place before it writes it.
                if op != crate::tir::tir_nodes::TIRAssignOp::Set {
                    if let Some(held) = self.place(place) {
                        self.reading(&held, Use::Assign, line, col);
                    }
                }
                if let Some(held) = self.place(place) {
                    // What the place is good for is what its root is good for,
                    // and it may not be given something shorter-lived. This is
                    // the refusal §3 promises lands "at the call rather than at
                    // the declaration", in the shape it takes when nothing is
                    // being returned: `r = pick(&outer, &inner)` where `r`
                    // outlives the block `inner` was declared in.
                    let lives = self.lives(held.root);
                    let (at_line, at_col) =
                        (self.p.exprs[value].line, self.p.exprs[value].col);
                    self.outstays(
                        value,
                        lives,
                        "this puts a reference to it somewhere longer-lived",
                        Span::at(at_line, at_col),
                    );
                    self.gone.filled(&held);
                }
                Flow::Normal
            }

            // Every argument is a place a value is handed over.
            TTIRExprKind::Call { callee, args } => {
                if self.expr(callee, Use::Read).left() {
                    return Flow::Left;
                }
                // "one call and no more": calling a `once fn` hands away what
                // it captured, so the call takes the closure. A second one is
                // then a use of something that has gone, and the message for
                // that is the one every other move already has.
                self.moving(callee);
                let flow = self.handing(&args);
                // After the arguments, so that what each was handed is known.
                if let Some(item) = self.callee(callee) {
                    let given: Vec<_> = args.iter().map(|&a| Handed::Written(a)).collect();
                    self.bounds_at_call(item, &given, Span::at(line, col));
                }
                flow
            }

            // A method holds a borrow of its receiver for the length of the
            // call, or moves it: "A `*self` receiver holds a mutable reference
            // to the whole value for the length of the call, so nothing reads
            // that value while the method runs" (§3).
            TTIRExprKind::Method { recv, item, args } => {
                let mode = self.receiver(item);
                // The receiver stands where parameter 0 does, so the two go
                // into one list before anything is asked of them -- and it is
                // borrowed rather than handed over, which is a different
                // question about how long it is good for.
                let first = match mode {
                    Some(TIRSelf::Ref) | Some(TIRSelf::Mut) => {
                        Handed::Whole(self.handed_borrowed(recv))
                    }
                    _ => Handed::Written(recv),
                };
                let given: Vec<_> = std::iter::once(first)
                    .chain(args.iter().map(|&a| Handed::Written(a)))
                    .collect();
                let flow = match mode {
                    Some(TIRSelf::Value) => {
                        if self.expr(recv, Use::Pass).left() {
                            return Flow::Left;
                        }
                        self.moving(recv);
                        self.handing(&args)
                    }
                    Some(TIRSelf::Ref) | Some(TIRSelf::Mut) => {
                        let op = if matches!(mode, Some(TIRSelf::Mut)) {
                            TIRRefOp::Mut
                        } else {
                            TIRRefOp::Imm
                        };
                        let mark = self.held.len();
                        if self.borrowing(id, recv, op, line, col).left() {
                            return Flow::Left;
                        }
                        let out = self.handing(&args);
                        // The call is over, and so is what it held.
                        self.held.truncate(mark);
                        out
                    }
                    None => {
                        if self.expr(recv, Use::Read).left() {
                            return Flow::Left;
                        }
                        self.handing(&args)
                    }
                };
                self.bounds_at_call(item, &given, Span::at(line, col));
                flow
            }

            // "a field of a literal being built" (§2).
            TTIRExprKind::StructLit { fields, .. }
            | TTIRExprKind::VariantLit { fields, .. }
            | TTIRExprKind::ArrayLit(fields)
            | TTIRExprKind::TupleLit(fields)
            | TTIRExprKind::Set { elems: fields, .. } => self.handing(&fields),
            TTIRExprKind::Map { entries, .. } => {
                let flat: Vec<TTIRExprId> =
                    entries.iter().flat_map(|&(k, v)| [k, v]).collect();
                self.handing(&flat)
            }

            TTIRExprKind::Range { start, end, .. } => {
                for held in start.iter().chain(end.iter()) {
                    if self.expr(*held, Use::Read).left() {
                        return Flow::Left;
                    }
                }
                Flow::Normal
            }

            // What it captured, and then its body. The captures are taken in
            // the frame the closure was written in -- they are names of *that*
            // body -- and the body is walked on its own afterwards.
            TTIRExprKind::Closure { captures, body } => {
                for held in &captures {
                    let place = Place::of(held.outer);
                    match held.mode {
                        // "Reading one takes a `&` of it and assigning to one
                        // takes a `*`" (§5), and the reference is held for as
                        // long as the closure is.
                        TTIRCaptureMode::Ref(op) => {
                            self.captured(id, &place, op, held.line, held.col);
                        }
                        // "By value is a copy where the name's type copies and
                        // a move where it does not" -- the same rule every
                        // other handing-over follows.
                        TTIRCaptureMode::Value => {
                            let ty = self.p.bodies[self.body].locals[held.outer].ty;
                            if !self.copies.is_copy(ty, self.p, &self.generic) {
                                self.gone.moved(place, held.line, held.col);
                            }
                        }
                    }
                }
                self.closure(&captures, body)
            }

            TTIRExprKind::Block { stmts, tail } => self.block(&stmts, tail),
            TTIRExprKind::If { cond, then, els } => self.conditional(cond, then, els),
            TTIRExprKind::While { cond, body } => self.loop_over(Some(cond), None, body),
            TTIRExprKind::For { local, iter, body } => {
                self.loop_over(None, Some((local, iter)), body)
            }
            TTIRExprKind::Match { scrutinee, arms } => self.matching(scrutinee, &arms),

            // The three that do not come back.
            TTIRExprKind::Return(value) => {
                if let Some(value) = value {
                    if self.expr(value, Use::Return).left() {
                        return Flow::Left;
                    }
                    self.moving(value);
                    self.escaping(value, line, col);
                }
                Flow::Left
            }
            TTIRExprKind::Break(value) => {
                if let Some(value) = value {
                    if self.expr(value, Use::Pass).left() {
                        return Flow::Left;
                    }
                    self.moving(value);
                }
                // What is gone here is gone after the loop as well.
                if let Some(out) = self.breaks.last_mut() {
                    out.push(self.gone.clone());
                }
                Flow::Left
            }
            TTIRExprKind::Continue => Flow::Left,
        }
    }

    // A closure's body, walked with nothing of the frame around it: its slots
    // are its own, the ones it captured among them, and a capture arrives whole
    // however the name outside it stood.
    fn closure(&mut self, captures: &[TTIRCapture], body: TTIRBodyId) -> Flow {
        // Everything keyed by a slot or an expression has to be put aside and
        // put back: "a `TTIRLocalId` is a slot of the body that holds it, not
        // of the program", so a closure's slot 0 and the enclosing frame's are
        // two different things with one number, and the same for an expression.
        let outer = self.body;
        let gone = std::mem::take(&mut self.gone);
        let held = std::mem::take(&mut self.held);
        let marks = std::mem::take(&mut self.marks);
        let breaks = std::mem::take(&mut self.breaks);
        let depth = std::mem::take(&mut self.depth);
        let from = std::mem::take(&mut self.from);
        let said_of = std::mem::take(&mut self.said_of);
        let when = std::mem::take(&mut self.when);
        let last = std::mem::take(&mut self.last);
        let now = self.now;
        // What the body gives back is the closure's result, and a reference in
        // it may point at what the closure captured -- which outlives the
        // closure -- but not at anything the body declared, which does not.
        let value = self.p.bodies[body].value;
        let gives = self.holds_any_ref(self.p.exprs[value].ty);
        let leaves = std::mem::replace(&mut self.leaves, gives);
        // "the one place a reference is taken without being written" (§5): a
        // slot holding one is a slot whose value is somebody else's.
        let borrowed = captures
            .iter()
            .filter_map(|c| match c.mode {
                TTIRCaptureMode::Ref(op) => Some((c.slot, op)),
                TTIRCaptureMode::Value => None,
            })
            .collect();
        let caught = std::mem::replace(&mut self.caught, borrowed);

        // A closure declares no parameters of its own, so the generics it is
        // checked under are the ones it was written inside.
        let generic = self.generic.clone();
        let slots: Vec<TTIRLocalId> = captures.iter().map(|c| c.slot).collect();
        self.walk_body_of(body, generic, &[], &slots);

        self.body = outer;
        self.gone = gone;
        self.held = held;
        self.marks = marks;
        self.breaks = breaks;
        self.depth = depth;
        self.from = from;
        self.said_of = said_of;
        self.when = when;
        self.last = last;
        self.now = now;
        self.leaves = leaves;
        self.caught = caught;
        Flow::Normal
    }

    // A reference nobody wrote. Held like any other, and reported like any
    // other -- what changes is only what the secondary says, a reader who did
    // not write a `&` needing to be told one is there.
    fn captured(
        &mut self,
        id: TTIRExprId,
        place: &Place,
        op: TIRRefOp,
        line: usize,
        col: usize,
    ) {
        let now = self.now;
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.until >= now
                    && held.place.conflicts(place)
                    && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
            })
            .cloned()
        {
            let name = self.name(place);
            self.say(
                Diagnostic::error(format!("`{}` is borrowed already", name), Span::at(line, col))
                    .with_label(format!("the closure captures it by `{}`", sigil(op)))
                    .with_secondary(
                        Span::at(other.line, other.col),
                        format!("a `{}` of it is held from", sigil(other.op)),
                    )
                    .with_help(
                        "a place is reached through one `*`, or through any number of `&`, and never both",
                    ),
            );
        }
        self.held.push(Held { place: place.clone(), op, line, col, until: usize::MAX, at: id });
    }

    // A run of things each of which is handed over: an argument list, the
    // fields of a literal. "all of them are one thing said in four places" (§2).
    fn handing(&mut self, args: &[TTIRExprId]) -> Flow {
        for &arg in args {
            if self.expr(arg, Use::Pass).left() {
                return Flow::Left;
            }
            self.moving(arg);
        }
        Flow::Normal
    }
}

// What a call handed one parameter: the expression, where there is one to take
// apart, and how long it lasts where there is not -- a method's receiver being
// borrowed rather than handed over, and the borrow lasting as long as the
// receiver itself.
enum Handed {
    Written(TTIRExprId),
    Whole((usize, Option<TTIRLocalId>)),
}

// A parameter holding no region bound: `T: Show` is a trait's business and
// `<T>` on its own is nobody's, and neither is a promise a caller keeps.
fn bounds_none(g: &TTIRGeneric) -> bool {
    match g {
        TTIRGeneric::Life { bounds, .. } => bounds.is_empty(),
        TTIRGeneric::Type { bounds, .. } => {
            !bounds.iter().any(|b| matches!(b, TTIRBound::Life(_)))
        }
    }
}

// ---- The rules ------------------------------------------------------------

impl<'a> Checker<'a> {
    // A place being used, which is where a move is found out about.
    fn reading(&mut self, place: &Place, how: Use, line: usize, col: usize) {
        let Some(state) = self.gone.of(place) else { return };
        let name = self.name(place);
        let (message, note) = if state.certain() {
            (format!("`{}` has been moved", name), "it was moved".to_string())
        } else {
            (
                format!("`{}` may have been moved", name),
                "it is moved on one way here".to_string(),
            )
        };
        self.say(
            Diagnostic::error(message, Span::at(line, col))
                .with_label(how.word())
                .with_secondary(state.at(), note)
                .with_help("a value moves unless its type says `impl Copy`"),
        );
    }

    // A value handed over: an argument, a return, the right of an assignment, a
    // field of a literal being built. It goes unless its type copies, and the
    // place it came from is done with.
    fn moving(&mut self, id: TTIRExprId) {
        let ty = self.p.exprs[id].ty;
        if self.copies.is_copy(ty, self.p, &self.generic) {
            return;
        }
        let Some(place) = self.place(id) else { return };
        let (line, col) = (self.p.exprs[id].line, self.p.exprs[id].col);

        // A value that moves has one owner at a time (§2), and neither of these
        // is this frame's to give away: what a reference refers to is owned
        // where it was borrowed from, and an element that went would leave the
        // array it was in with a hole in it.
        //
        // Neither is written down in the prose. Both follow from one owner at a
        // time, and a reader meets them early enough that saying nothing would
        // be worse than saying this.
        // A name the closure captured by reference is the enclosing frame's,
        // and handing it away from here would hand away what somebody else
        // still owns. §5 works the mode out from what the body asks -- reading
        // takes a `&` and assigning takes a `*` -- and taking the value is
        // more than either, with no mode for it short of `move`.
        if let Some(op) = self.caught.get(&place.root).copied() {
            if place.path.is_empty() || !place.path.contains(&Step::Deref) {
                let name = self.name(&place);
                self.say(
                    Diagnostic::error(
                        format!("`{}` cannot be moved out of a closure", name),
                        Span::at(line, col),
                    )
                    .with_label("this takes it")
                    .with_note(format!(
                        "the closure captured it by `{}`, which borrows it",
                        sigil(op)
                    ))
                    .with_help("a `move` closure takes what it captures, and may give it away"),
                );
                return;
            }
        }

        let out_of = if place.path.contains(&Step::Deref) {
            Some(("a reference", "`&` it instead, which borrows rather than takes"))
        } else if place.path.contains(&Step::Index) {
            Some(("an array", "an element that went would leave a hole where it was"))
        } else {
            None
        };
        if let Some((what, help)) = out_of {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(
                    format!("`{}` cannot be moved out of {}", name, what),
                    Span::at(line, col),
                )
                .with_label("this takes it")
                .with_help(help),
            );
            return;
        }

        self.gone.moved(place, line, col);
    }

    // Taking a reference. Two rules meet here: what `*` asks of its operand,
    // and how many of each may stand at once.
    fn borrowing(
        &mut self,
        id: TTIRExprId,
        operand: TTIRExprId,
        op: TIRRefOp,
        line: usize,
        col: usize,
    ) -> Flow {
        if self.expr(operand, Use::Read).left() {
            return Flow::Left;
        }
        // A value with no home of its own: "`&x` asks less: any place at all,
        // and a value with no home of its own, which the compiler gives one".
        let Some(place) = self.place(operand) else { return Flow::Normal };

        // "`*x` asks that x be a place the writer may write to -- a `var`, or a
        // field or element reached from one" (§5). Mutability is the root
        // binding's and reaches through whatever is reached from it (§2), so
        // the root is what is asked.
        if op == TIRRefOp::Mut && !self.writable(&place) {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(
                    format!("`{}` may not be written to", name),
                    Span::at(line, col),
                )
                .with_label("this takes a `*`")
                .with_help("a `*` wants a `var`, or a field or an element of one"),
            );
        }

        // "A place is reached either through one `*` and nothing else, or
        // through any number of `&` and no `*` -- one mutable reference or many
        // immutable ones, and never both" (§3).
        let now = self.now;
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.until >= now
                    && held.place.conflicts(&place)
                    && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
            })
            .cloned()
        {
            let name = self.name(&place);
            self.say(
                Diagnostic::error(format!("`{}` is borrowed already", name), Span::at(line, col))
                    .with_label(format!("this takes a `{}`", sigil(op)))
                    .with_secondary(
                        Span::at(other.line, other.col),
                        format!("a `{}` of it is held from", sigil(other.op)),
                    )
                    .with_help(
                        "a place is reached through one `*`, or through any number of `&`, and never both",
                    ),
            );
        }

        self.held.push(Held { place, op, line, col, until: usize::MAX, at: id });
        Flow::Normal
    }

    // Whether the writer may write to a place. The root binding's answer, since
    // "there is no marking a single field of a `let` writable, and none
    // weakening one of a `var` either" (§2) -- and a `*` reached through is
    // written through whatever the binding says.
    fn writable(&self, place: &Place) -> bool {
        let local = &self.p.bodies[self.body].locals[place.root];
        if matches!(local.intro, crate::tir::tir_nodes::TIRIntro::Var) {
            return true;
        }
        // A `let` of reference type never re-aims and still writes into what it
        // refers to, where the reference is a `*`: "what a `let` fixes is the
        // binding and not the referent" (§2).
        place.path.contains(&Step::Deref)
            && matches!(&self.p.types[local.ty], Ty::Ref { op: TIRRefOp::Mut, .. })
    }

    // How a method takes its receiver, where the item is one that has a body.
    fn receiver(&self, item: TTIRItemId) -> Option<TIRSelf> {
        let TTIRItemKind::Fn(f) = &self.p.items[item].kind else { return None };
        match f.params.first().map(|param| &param.name) {
            Some(TIRBinding::SelfRecv(mode, _)) => Some(*mode),
            _ => None,
        }
    }

    // ---- Control flow ----------------------------------------------------

    // A block, which is what a borrow's extent is measured in: everything taken
    // inside one is let go at the end of it.
    fn block(&mut self, stmts: &[TTIRStmt], tail: Option<TTIRExprId>) -> Flow {
        self.marks.push(self.held.len());
        let mut flow = Flow::Normal;
        for stmt in stmts {
            match stmt {
                // A `let` is the exception: what its initialiser borrowed may
                // have reached the slot, so the borrow keeps the block's
                // extent rather than the statement's. Bluntly -- every borrow
                // taken while working the value out, whether it reached the
                // slot or not -- which is the conservative half and costs a
                // reachability walk to sharpen.
                TTIRStmt::Let { local, init, .. } => {
                    // How long the slot is good for: the block it stands in,
                    // which is however many blocks deep the walk is now.
                    let held = self.marks.len();
                    self.depth.insert(*local, held);
                    let taken = self.held.len();
                    if let Some(init) = init {
                        if self.expr(*init, Use::Pass).left() {
                            flow = Flow::Left;
                            break;
                        }
                        self.moving(*init);
                        // A slot that outlives what it is given is the same
                        // refusal as a return that does, one block in rather
                        // than all the way out.
                        let (line, col) =
                            (self.p.exprs[*init].line, self.p.exprs[*init].col);
                        self.outstays(
                            *init,
                            held,
                            "this puts a reference to it somewhere longer-lived",
                            Span::at(line, col),
                        );
                        // And where it points, so a reference handed through a
                        // name is followed to what it was taken from.
                        let roots = self.roots(*init);
                        if roots.is_empty() {
                            self.from.remove(local);
                        } else {
                            self.from.insert(*local, roots);
                        }
                    }
                    // A borrow that got as far as the slot keeps the slot's
                    // extent, which ends where the slot is last read. One that
                    // did not is a temporary and goes with the statement:
                    // "a local at the end of its block, a temporary at the end
                    // of its statement" (§2), and a `&` handed to something
                    // that gives back no reference is a temporary however it
                    // was written.
                    let until = self.last.get(local).copied().unwrap_or(usize::MAX);
                    let reaching = match init {
                        Some(init) => self.reaching(*init),
                        None => Vec::new(),
                    };
                    let now = self.now;
                    for held in &mut self.held[taken..] {
                        held.until = if reaching.contains(&held.at) { until } else { now };
                    }
                    // The slot is filled, whatever was in it before.
                    self.gone.filled(&Place::of(*local));
                }
                TTIRStmt::Expr { expr, .. } => {
                    // "a local at the end of its block, a temporary at the end
                    // of its statement" (§2). A reference taken in a statement
                    // and bound to nothing is a temporary, so it goes with the
                    // statement -- which is what lets `f(&p)` and `g(*p)` stand
                    // one after the other.
                    let mark = self.held.len();
                    let left = self.expr(*expr, Use::Read).left();
                    self.held.truncate(mark);
                    if left {
                        flow = Flow::Left;
                        break;
                    }
                }
                // A declaration written in a block is walked where it is
                // declared, by `check` over every item.
                TTIRStmt::Item(_) => {}
            }
        }
        if flow == Flow::Normal {
            if let Some(tail) = tail {
                flow = self.expr(tail, Use::Read);
            }
        }
        let mark = self.marks.pop().unwrap_or(0);
        self.held.truncate(mark);
        flow
    }

    // Two ways, and what is true after them is what is true of both.
    fn conditional(
        &mut self,
        cond: TTIRExprId,
        then: TTIRExprId,
        els: Option<TTIRExprId>,
    ) -> Flow {
        if self.expr(cond, Use::Read).left() {
            return Flow::Left;
        }
        let before = self.gone.clone();
        let took = self.expr(then, Use::Read);
        let after_then = std::mem::replace(&mut self.gone, before);
        let other = match els {
            Some(els) => self.expr(els, Use::Read),
            None => Flow::Normal,
        };

        match (took.left(), other.left()) {
            // Neither came back, so nothing after this is reached.
            (true, true) => Flow::Left,
            // One left: what it did to the state left with it.
            (true, false) => Flow::Normal,
            (false, true) => {
                self.gone = after_then;
                Flow::Normal
            }
            (false, false) => {
                self.gone.join(&after_then);
                Flow::Normal
            }
        }
    }

    // Every arm, joined. A pattern binds slots of its own, and what it binds is
    // filled rather than moved from.
    fn matching(&mut self, scrutinee: TTIRExprId, arms: &[crate::tir::ttir_nodes::TTIRArm]) -> Flow {
        if self.expr(scrutinee, Use::Read).left() {
            return Flow::Left;
        }
        let before = self.gone.clone();
        let mut joined: Option<Gone> = None;
        let mut all_left = !arms.is_empty();

        let from_of = self.roots(scrutinee);
        for arm in arms {
            self.gone = before.clone();
            self.from_of = from_of.clone();
            for &pat in &arm.pats {
                self.binds(pat);
            }
            self.from_of.clear();
            if !self.expr(arm.body, Use::Read).left() {
                all_left = false;
                let reached = self.gone.clone();
                joined = Some(match joined {
                    None => reached,
                    Some(mut held) => {
                        held.join(&reached);
                        held
                    }
                });
            }
        }

        if all_left {
            return Flow::Left;
        }
        self.gone = joined.unwrap_or(before);
        Flow::Normal
    }

    // The slots a pattern binds. Each is filled by the match, so anything that
    // had gone from one is whole again.
    fn binds(&mut self, pat: TTIRPatId) {
        match &self.p.pats[pat].kind {
            TTIRPatKind::Bind(local) => {
                let place = Place::of(*local);
                // A name a pattern binds stands in the arm and nowhere else, so
                // it is one block shorter-lived than where the `match` is.
                self.depth.insert(*local, self.marks.len() + 1);
                // And it came out of what was matched on, so it points wherever
                // that did. Not *at* it: a name bound out of a value is the
                // value's own, and `match opt { Some(v) => v }` gives back what
                // `opt` held rather than a reference into `opt`.
                let (local, from) = (*local, self.from_of.clone());
                if from.is_empty() {
                    self.from.remove(&local);
                } else {
                    self.from.insert(local, from);
                }
                self.gone.filled(&place);
            }
            TTIRPatKind::Variant { elems, .. } => {
                for &elem in elems.clone().iter() {
                    self.binds(elem);
                }
            }
            TTIRPatKind::Tuple(elems) => {
                for &elem in elems.clone().iter() {
                    self.binds(elem);
                }
            }
            TTIRPatKind::Struct { fields, .. } => {
                for field in fields.clone().iter().flatten() {
                    self.binds(*field);
                }
            }
            TTIRPatKind::Range { lo, hi, .. } => {
                let (lo, hi) = (*lo, *hi);
                self.binds(lo);
                self.binds(hi);
            }
            TTIRPatKind::Wildcard | TTIRPatKind::Const(_) | TTIRPatKind::Lit { .. } => {}
        }
    }

    // A loop, walked twice: what a body does to the state is what the next turn
    // round it starts from, so a move in the body is a move at the top of the
    // second turn. The first walk says nothing -- it is how the state is
    // settled, and reporting from it would report a body that never ran.
    fn loop_over(
        &mut self,
        cond: Option<TTIRExprId>,
        each: Option<(TTIRLocalId, TTIRExprId)>,
        body: TTIRExprId,
    ) -> Flow {
        if let Some(cond) = cond {
            if self.expr(cond, Use::Read).left() {
                return Flow::Left;
            }
        }
        if let Some((local, iter)) = each {
            if self.expr(iter, Use::Pass).left() {
                return Flow::Left;
            }
            self.moving(iter);
            // The loop variable stands in the body and nowhere else, so it is
            // one block shorter-lived than where the `for` is.
            self.depth.insert(local, self.marks.len() + 1);
            // And it comes out of what is being gone through, so it points
            // wherever that did: `for v in &things` hands out references into
            // `things`, and `for v in things` hands out what `things` held.
            let from = self.roots(iter);
            if from.is_empty() {
                self.from.remove(&local);
            } else {
                self.from.insert(local, from);
            }
            self.gone.filled(&Place::of(local));
        }

        // Round once with nothing said, to find what the body leaves behind.
        let before = self.gone.clone();
        let was_quiet = std::mem::replace(&mut self.quiet, true);
        self.breaks.push(Vec::new());
        self.expr(body, Use::Read);
        self.breaks.pop();
        self.quiet = was_quiet;

        // And round again from the state the first turn reached, which is what
        // the second turn would really see.
        self.gone.join(&before);
        self.breaks.push(Vec::new());
        let flow = self.expr(body, Use::Read);
        let ways_out = self.breaks.pop().unwrap_or_default();

        // What is true after the loop is true of every way out of it, the body
        // running to the end among them -- unless nothing came back that way.
        if !flow.left() {
            self.gone.join(&before);
        } else {
            self.gone = before.clone();
        }
        for out in &ways_out {
            self.gone.join(out);
        }
        Flow::Normal
    }
}

fn sigil(op: TIRRefOp) -> &'static str {
    match op {
        TIRRefOp::Imm => "&",
        TIRRefOp::Mut => "*",
    }
}

#[cfg(test)]
mod tests;
