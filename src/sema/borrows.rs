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
// It walks the TTIR and not the CFG. The language is structured -- every branch
// and every loop is an expression and there is no goto -- so a walk that joins
// at an `if` and settles a loop by going round it twice reaches what a dataflow
// over a graph would reach. What the graph does not keep is what this needs:
// `cfg::lower` flattens the blocks a borrow's extent is measured in, drops which
// locals were parameters, and binds a pattern's names on an edge rather than in
// a statement.
//
// What it does not do:
//
//   - Regions, and this one is a hole and not a conservatism. A borrow here
//     lasts to the end of the block that holds it, which is the rule before
//     Rust's NLL: it turns down some programs that are fine, and the prose
//     allows for that, its own lifetime rule being "only ever answered too
//     conservatively". What it does *not* do is catch a reference that outlives
//     what it refers to. `fn f(): &i32 { let x = 1; &x }` passes this pass.
//     Whoever compares `Ty::Ref.life` is who closes that, and until then the
//     name of this file promises more than it does.
//   - Nothing about a closure's *body* reaching what it captured. The capture
//     itself is checked -- §5 makes it the one place a reference is taken
//     without being written, and `TTIRCapture` is what says so -- but the
//     borrow it takes lasts as long as the name the closure was bound to, and
//     what the body does with its own slot for it is the body's own business.
//   - Where a `Drop` runs. Settled in §2 and codegen's, not the checker's.

// The pass that would hand this a TTIR is `sema` itself, which is not written.
// Until it is, this is built by tests and by nothing else.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::tir::tir_nodes::{TIRBinding, TIRRefOp, TIRSelf, TIRUnaryOp};
use crate::tir::ttir_nodes::{
    TTIRBodyId, TTIRCaptureMode, TTIRExprId, TTIRExprKind, TTIRGeneric, TTIRItemId,
    TTIRItemKind, TTIRLocalId, TTIRPatId, TTIRPatKind, TTIRProgram, TTIRStmt, Ty, TyId,
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
            Ty::Ref { .. } | Ty::Ptr(_) | Ty::Fn { .. } => true,

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
            let (Some(body), generic) = (f.body, f.generics.clone()) else { continue };
            self.walk_body(body, generic);
        }
        &self.errors
    }

    fn walk_body(&mut self, body: TTIRBodyId, generic: Vec<TTIRGeneric>) {
        self.body = body;
        self.generic = generic;
        self.gone = Gone::default();
        self.held.clear();
        self.marks.clear();
        self.breaks.clear();
        let value = self.p.bodies[body].value;
        self.expr(value, Use::Read);
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
            TIRBinding::SelfRecv(_) => "self".to_string(),
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
                self.borrowing(operand, op, line, col)
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
                    self.gone.filled(&held);
                }
                Flow::Normal
            }

            // Every argument is a place a value is handed over.
            TTIRExprKind::Call { callee, args } => {
                if self.expr(callee, Use::Read).left() {
                    return Flow::Left;
                }
                self.handing(&args)
            }

            // A method holds a borrow of its receiver for the length of the
            // call, or moves it: "A `*self` receiver holds a mutable reference
            // to the whole value for the length of the call, so nothing reads
            // that value while the method runs" (§3).
            TTIRExprKind::Method { recv, item, args } => {
                let mode = self.receiver(item);
                match mode {
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
                        if self.borrowing(recv, op, line, col).left() {
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
                }
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
                            self.captured(&place, op, held.line, held.col);
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
                self.closure(body)
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
    fn closure(&mut self, body: TTIRBodyId) -> Flow {
        let (outer, gone, held, marks, breaks) = (
            self.body,
            std::mem::take(&mut self.gone),
            std::mem::take(&mut self.held),
            std::mem::take(&mut self.marks),
            std::mem::take(&mut self.breaks),
        );
        // A closure declares no parameters of its own, so the generics it is
        // checked under are the ones it was written inside.
        let generic = self.generic.clone();
        self.walk_body(body, generic);
        self.body = outer;
        self.gone = gone;
        self.held = held;
        self.marks = marks;
        self.breaks = breaks;
        Flow::Normal
    }

    // A reference nobody wrote. Held like any other, and reported like any
    // other -- what changes is only what the secondary says, a reader who did
    // not write a `&` needing to be told one is there.
    fn captured(&mut self, place: &Place, op: TIRRefOp, line: usize, col: usize) {
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.place.conflicts(place) && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
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
        self.held.push(Held { place: place.clone(), op, line, col });
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
        if let Some(other) = self
            .held
            .iter()
            .find(|held| {
                held.place.conflicts(&place) && (held.op == TIRRefOp::Mut || op == TIRRefOp::Mut)
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

        self.held.push(Held { place, op, line, col });
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
            Some(TIRBinding::SelfRecv(mode)) => Some(*mode),
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
                    if let Some(init) = init {
                        if self.expr(*init, Use::Pass).left() {
                            flow = Flow::Left;
                            break;
                        }
                        self.moving(*init);
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

        for arm in arms {
            self.gone = before.clone();
            for &pat in &arm.pats {
                self.binds(pat);
            }
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
