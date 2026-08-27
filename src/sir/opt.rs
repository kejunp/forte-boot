// Making the SIR smaller: the same program, with what it does not have to do
// taken out of it.
//
//     TTIR -> lower -> GIR -> opt -> lower -> SIR -> promote -> opt
//
// `gir::opt` runs before the checker and is held to what a declaration can
// answer on its own: no copy propagation, no inlining, and no folding that
// would change which programs compile. This pass is on the other side of all
// three. The types are settled, so `1 + 2` has a type and folding it cannot
// give the answer a different one. Every value is made once, so what a name
// holds is a lookup rather than a walk. And nothing after this refuses a
// program -- there is no diagnostic left to get wrong -- so a rewrite here is
// only ever wrong about what the program *does*.
//
// Eleven rewrites, run round and round until none of them has anything left:
//
//   `unroll`    a loop whose turns are counted before it starts, written out
//               as the turns it runs.
//   `hoist`     what a loop works out the same on every turn, moved to before
//               the loop.
//   `fold`      an operator over values that are already literals, the handful
//               of identities that need only one side to be one, and a field
//               read out of something built a few instructions above.
//   `phis`      a phi whose edges all name one value, which is a join that
//               joined nothing.
//   `share`     two instructions that make the same value from the same
//               operands, where the first stands before the second.
//   `forward`   a load answered by the store above it, where nothing between
//               them may have written where it reads.
//   `overwritten` a store written over before anything reads it.
//   `vectorize` a run of the same thing done to neighbouring places, done at
//               once.
//   `branches`  a branch whose condition is already known, and one whose two
//               edges go to one block.
//   `merge`     a block whose only way in is a `Goto`, folded into the block
//               that goes there.
//   `sweep`     everything nothing reads and nothing else needs run.
//
// And one that is the program's rather than a body's:
//
//   `inline`    a call to a declaration written out where it was called, with
//               the arguments standing in for the parameters.
//
// Inlining is what makes the rest of them worth running: a call carries its
// arguments into a body that cannot see where they came from, and writing the
// body out is what puts a literal argument next to the operator that would
// fold it.
//
// It is also the one rewrite that can make a program bigger, so it is bounded
// twice over: by how big a callee may be, and by how many calls one body may
// take in a round. And it is refused outright wherever the callee can reach
// itself, which stops a recursive fn being written into itself forever and
// equally into anybody else, where it would be a loop unrolled by accident
// rather than a call written out.
//
// The source has the last word both ways. `%noinline` "is a promise about what
// a stack trace will show" (§1), so it is obeyed and nothing here weighs it
// against anything; `%inline` is "a hint, and the one thing here a backend may
// ignore", so it waives the size bound and none of the rules that make the
// rewrite sound.
//
// The order they are written in is the order they are run in, and it is not
// arbitrary: unrolling turns a loop variable into a literal, which folding
// makes conditions out of, which makes branches into gotos, which leaves
// blocks with one way in for `merge`, which puts an instruction next to the
// one it repeats for `share` -- and leaves the turns of a loop side by side in
// one block, which is what `vectorize` needs to see them as one. Nothing
// depends on that order being right, though: the loop runs until nothing
// changes, so a rewrite that only becomes possible after another one just
// happens a round later.
//
// Four of them are about memory -- `hoist` for the loads it moves, `forward`,
// `overwritten` and `vectorize` -- and none of the four could be written
// before `alias.rs` was. "Does this write land where that reads" is the whole
// of what each of them has to know, and a pass with no answer to it has to
// assume the worst everywhere, which is the same as not being written.
//
// The two over loops are the two that need to know what a loop *is*, which is
// a question about the graph and not about the source: see `loops.rs`, where a
// `while`, a `for` and anything else that goes back where it has been are one
// shape. Both are written against the same two facts that fall out of it --
// the blocks a loop holds, and the one block above its head.
//
// What is *not* here is vectorization. It is asked for in the same breath as
// the rest and it does not belong in the same pass, or yet in this compiler:
// it needs a target to say how wide a vector is, a type for one to be held in
// -- the SIR has neither -- and, before either, an answer to whether two turns
// of a loop touch the same memory, which is the alias analysis nothing here
// has. Writing something that reshaped loops without those would be a rewrite
// that is right by luck. See the note at the foot of this file for what would
// have to come first.

use std::collections::HashMap;

use crate::tir::tir_nodes::{TIRBinOp, TIRFnUses, TIRInline, TIRLit, TIRPrim, TIRRangeOp,
                            TIRUnaryOp};
use crate::tir::ttir_nodes::{TTIRItemId, TTIRItemKind, TTIRProgram, Ty, TyId};

use super::alias::{Alias, Base};
use super::dom::Dominators;
use super::loops::{preheader, Loop};
use super::promote::promote;
use super::target::{self, Target};
use super::sir_nodes::*;

// Rounds before the loop gives up. A body settles in two or three; the cap is
// for a rewrite that undoes another, which would be a bug here rather than
// anything a program can do.
const MAX_ROUNDS: usize = 8;

// ---- How hard to try ------------------------------------------------------

// The rewrites here fall into three kinds, and a level is a line drawn between
// them rather than a list of passes turned on.
//
//   Some only ever remove. Folding an operator over two literals, taking out
//   what nothing reads, joining two blocks that were one -- none of these can
//   leave a program bigger or slower than it was, and there is no reason to
//   want them off except to see what the lowering made.
//
//   Some move code, or copy it. Writing a call out, lifting something out of a
//   loop, writing a loop out as its turns: each makes the program bigger in
//   the hope of making it quicker, and each is bounded by a number that is a
//   guess.
//
//   And one widens it: running the turns of a loop several at a time, which
//   needs the other two kinds to have gone first and needs something the rest
//   of this compiler has no opinion about -- a machine. See `sir::target`.
//
// So: nothing, the first kind, the first two, and all three with the guesses
// turned up. Which is what `-O0` through `-O3` mean everywhere else, and there
// is no reason for them to mean something else here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Level {
    // Nothing at all. What comes out is what `sir::lower` and `sir::promote`
    // made, which is the shape to read when the question is what the front of
    // the compiler did rather than what this pass made of it.
    None,
    // Everything that only ever takes something away.
    Less,
    // And everything that moves or copies code. The level a program is built
    // at unless something says otherwise.
    #[default]
    Default,
    // And the widening, with the bounds on the copying raised. What is widened
    // and how far is the target's to say; this only says to ask it.
    More,
}

impl Level {
    // `-O<n>`, and anything past the end is the most there is: a number nobody
    // has written a level for is a level nobody meant to name.
    pub fn of(n: u8) -> Level {
        match n {
            0 => Level::None,
            1 => Level::Less,
            2 => Level::Default,
            _ => Level::More,
        }
    }

    // The rewrites that only remove.
    fn shrinks(self) -> bool {
        self > Level::None
    }

    // The ones that move code, or write a second copy of it.
    fn moves(self) -> bool {
        self >= Level::Default
    }

    // And running the turns of a loop several at a time.
    fn widens(self) -> bool {
        self >= Level::More
    }

    fn rounds(self) -> usize {
        match self {
            Level::None => 0,
            Level::Less => 2,
            Level::Default => MAX_ROUNDS,
            Level::More => MAX_ROUNDS * 2,
        }
    }

    // How many instructions a callee may hold and still be written out. A call
    // is a handful of instructions itself, so the middle of these is roughly
    // "a body worth less than the call to it, or not much more".
    fn inline_max(self) -> usize {
        match self {
            Level::More => 96,
            _ => 32,
        }
    }

    // And how many calls one body may take in one round. The rounds compose --
    // what was written into a callee last round is written into its caller
    // this round -- so this bounds the growth per round and not the depth.
    fn inline_each(self) -> usize {
        match self {
            Level::More => 24,
            _ => 8,
        }
    }

    fn unroll_turns(self) -> usize {
        match self {
            Level::More => 16,
            _ => 8,
        }
    }

    fn unroll_insts(self) -> usize {
        match self {
            Level::More => 256,
            _ => 96,
        }
    }
}

// What the pass did, for the driver to print. Nothing reads it but the message.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    pub rounds:    usize,
    pub inlined:   usize,
    pub folded:    usize,
    // Values that turned out to be a value there already: a phi that joined
    // one answer, or an instruction that repeated one.
    pub shared:    usize,
    // Loads answered by what a store above them wrote, which is the same idea
    // over memory and is counted apart because it is the one that needed an
    // analysis rather than a comparison.
    pub forwarded: usize,
    pub dead:      usize,
    // Blocks emptied, merged away, or left with one edge where they had two.
    pub blocks:    usize,
    // Instructions lifted out of a loop, and loops written out as the turns
    // they run for.
    pub hoisted:   usize,
    pub unrolled:  usize,
    // Runs of writes to neighbouring places, turned into one write of several.
    pub widened:   usize,
    // Slots the re-run of `promote` took out, which are the callee's locals
    // now that they are the caller's.
    pub promoted:  usize,
}

pub fn optimize(
    program: &mut SIRProgram,
    ttir: &TTIRProgram,
    level: Level,
    target: Target,
) -> Stats {
    let mut stats = Stats::default();
    if !level.shrinks() {
        return stats;
    }
    let graph = Calls::of(program, ttir);
    for round in 1..=level.rounds() {
        let mut changed = false;
        // The program first: writing a call out is what gives the body
        // rewrites something new to work on, and the slots it brings with it
        // are the caller's now, so the promotion is asked again.
        if level.moves() && inline(program, &graph, level, &mut stats) {
            stats.promoted += promote(program);
            changed = true;
        }
        for body in &mut program.bodies {
            changed |= clean(body, ttir, level, target, &mut stats);
        }
        stats.rounds = round;
        if !changed {
            break;
        }
    }
    stats
}

// One body, until the six have nothing left. The inner loop is here rather
// than only in `optimize` so that a body settles without waiting on the whole
// program to go round again.
fn clean(
    body: &mut SIRBody,
    ttir: &TTIRProgram,
    level: Level,
    target: Target,
    stats: &mut Stats,
) -> bool {
    let mut ever = false;
    for _ in 0..level.rounds() {
        let mut changed = false;
        if level.moves() {
            changed |= unroll(body, ttir, level, stats);
            changed |= hoist(body, ttir, stats);
        }
        changed |= fold(body, ttir, stats);
        changed |= phis(body, stats);
        changed |= share(body, ttir, stats);
        changed |= forward(body, ttir, stats);
        changed |= overwritten(body, stats);
        if level.widens() {
            changed |= vectorize(body, ttir, target, stats);
        }
        changed |= branches(body, stats);
        changed |= merge(body, stats);
        changed |= sweep(body, ttir, stats);
        ever |= changed;
        if !changed {
            break;
        }
    }
    ever
}

// ---- Reading the body -----------------------------------------------------

// What made each value, by the value's id. SSA is what makes this a table
// rather than a walk, and every rewrite below is written against it: "what
// does this operand hold" is `made[operand]`, and there is no second answer.
//
// A phi is not in it. What a phi made depends on the edge, which is the one
// question this table cannot be asked -- `operands` below is what covers both.
fn made(body: &SIRBody) -> Vec<Option<SIRInstKind>> {
    let mut out = vec![None; body.values.len()];
    for block in &body.blocks {
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = Some(inst.kind.clone());
                }
            }
        }
    }
    out
}

// What whatever made each value reads, phis included. `sweep` walks this
// backwards from the values that have to be worked out to the ones that
// therefore do.
fn operands(body: &SIRBody) -> Vec<Vec<SIRValueId>> {
    let mut out = vec![Vec::new(); body.values.len()];
    for block in &body.blocks {
        for phi in &block.phis {
            if phi.def < out.len() {
                out[phi.def] = phi.edges.iter().map(|(_, value)| *value).collect();
            }
        }
        for inst in &block.insts {
            if let Some(def) = inst.def {
                if def < out.len() {
                    out[def] = SIRBody::uses(&inst.kind);
                }
            }
        }
    }
    out
}

fn lit_of(made: &[Option<SIRInstKind>], value: SIRValueId) -> Option<&TIRLit> {
    match made.get(value)? {
        Some(SIRInstKind::Literal(held)) => Some(held),
        _ => None,
    }
}

fn prim(ttir: &TTIRProgram, ty: TyId) -> Option<TIRPrim> {
    match ttir.types.get(ty)? {
        Ty::Prim(p) => Some(*p),
        _ => None,
    }
}

// Whether two types say the same thing, which is not the same as being the
// same entry.
//
// A `TyId` is not a name for a type: `sema` interns as it infers, so a program
// with three `i32`s written in it can leave three entries that all read
// `Prim(I32)`. Everything here that compares two types wants them one where
// they say the same thing -- an instruction repeated is repeated whichever
// `i32` the checker happened to be holding -- so the comparison is over what
// the entry says. The id is tried first because it usually settles it.
fn alike(ttir: &TTIRProgram, a: TyId, b: TyId) -> bool {
    a == b || (ttir.types.get(a).is_some() && ttir.types.get(a) == ttir.types.get(b))
}

fn integer(p: TIRPrim) -> bool {
    use TIRPrim::*;
    matches!(p, I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128)
}

// Whether the value has to stay even where nothing reads it.
//
// Three kinds of reason. A call or a store or a release is what the program is
// *for*, and dropping one drops what it did. An index may be past the end, and
// whether that is a trap is not settled anywhere yet (docs/prose.txt says
// nothing about it), so taking one out would be this pass answering a question
// that is not its own. And a division whose divisor is not a literal that is
// plainly not zero is the same: the trap, if there is one, is the thing being
// removed.
fn effects(
    values: &[SIRValue],
    ttir: &TTIRProgram,
    made: &[Option<SIRInstKind>],
    kind: &SIRInstKind,
) -> bool {
    match kind {
        SIRInstKind::Call { .. }
        | SIRInstKind::Method { .. }
        | SIRInstKind::Store { .. }
        | SIRInstKind::Drop(_)
        | SIRInstKind::DropSlot(_)
        | SIRInstKind::VecStore { .. } => true,
        SIRInstKind::Index { base, index } | SIRInstKind::IndexAddr { base, index } => {
            !within(values, ttir, made, *base, *index)
        }
        SIRInstKind::Binary { op: TIRBinOp::Div | TIRBinOp::Rem, rhs, .. } => {
            match lit_of(made, *rhs) {
                Some(TIRLit::Int(n)) => *n == 0,
                // A float division by zero is an infinity and not a trap, so
                // there is nothing being kept for.
                Some(TIRLit::Float(_)) => false,
                _ => true,
            }
        }
        _ => false,
    }
}

// Whether the element being asked for is one the thing being indexed certainly
// has. A number for an index and a length in the type is the whole of what can
// be answered here, and it is enough for the shape that matters: a name of this
// frame, declared `T[n]`, reached at a place the unrolling worked out.
//
// Everything else is left as something that might be past the end -- which is
// not the same as saying it traps, only that nothing here knows it does not,
// and moving or dropping it would be answering a question §5 has not.
fn within(
    values: &[SIRValue],
    ttir: &TTIRProgram,
    made: &[Option<SIRInstKind>],
    base: SIRValueId,
    index: SIRValueId,
) -> bool {
    let Some(TIRLit::Int(n)) = lit_of(made, index) else { return false };
    let Some(held) = values.get(base) else { return false };
    let Some(Ty::Array { len, .. }) = ttir.types.get(held.ty) else { return false };
    *n >= 0 && (*n as u128) < *len as u128
}

// Whether two of them with the same operands make the same value.
//
// Not the same question as `effects`. A load has no effects and may still find
// something different the second time, because a store between them is exactly
// the effect the load has not got. A division may trap and is still the same
// answer twice: if the first one trapped there is no second one.
fn known(kind: &SIRInstKind) -> bool {
    matches!(
        kind,
        SIRInstKind::Literal(_)
            | SIRInstKind::Item(_)
            | SIRInstKind::SelfValue
            | SIRInstKind::Unary { .. }
            | SIRInstKind::Binary { .. }
            | SIRInstKind::Cast(_)
            | SIRInstKind::Discriminant(_)
            | SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::FieldAddr { .. }
            | SIRInstKind::TupleAddr { .. }
            // Two of these make the one value whether or not either traps: if
            // the first one did, there is no second one to have shared with.
            // Whether a dead one may *go* is `effects`, which is a different
            // question and answered differently.
            | SIRInstKind::Index { .. }
            | SIRInstKind::IndexAddr { .. }
    )
}

// And whether naming one value twice is naming one *thing* twice. It is not,
// wherever the value is something to release: two instructions that each made
// one become one instruction and two releases of it. So sharing is held to the
// types nobody releases, which is the part of `sema::borrows`' answer a `TyId`
// can give on its own -- see `Copies::drops`, which this agrees with and does
// not call, having neither the table nor the body's generics to hand.
fn shareable(ttir: &TTIRProgram, ty: TyId) -> bool {
    match ttir.types.get(ty) {
        Some(Ty::Prim(_) | Ty::Ref { .. } | Ty::Ptr(_) | Ty::Run(_)) => true,
        Some(Ty::Fn { uses, .. }) => *uses != TIRFnUses::Takes,
        _ => false,
    }
}

// ---- Putting one value where another was ----------------------------------

// What a value came to, following the chain as far as it goes: a value
// replaced by one that is itself replaced later in the same round. Bounded by
// the length of the map, which is what makes a cycle stop rather than spin.
fn settle(subst: &HashMap<SIRValueId, SIRValueId>, mut value: SIRValueId) -> SIRValueId {
    for _ in 0..=subst.len() {
        match subst.get(&value) {
            Some(&next) if next != value => value = next,
            _ => return value,
        }
    }
    value
}

// Every operand of the body, rewritten at once. Every rewrite that takes an
// instruction out ends here: what it made is read somewhere, and what it made
// is now something else's.
fn replace(body: &mut SIRBody, subst: &HashMap<SIRValueId, SIRValueId>) {
    if subst.is_empty() {
        return;
    }
    for block in &mut body.blocks {
        for phi in &mut block.phis {
            for (_, value) in &mut phi.edges {
                *value = settle(subst, *value);
            }
        }
        for inst in &mut block.insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(subst, *value);
            }
        }
        match &mut block.term {
            SIRTerm::Branch { cond, .. } => *cond = settle(subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(subst, *value),
            _ => {}
        }
    }
}

// ---- Constant folding -----------------------------------------------------

// What an operator came to. Either a literal, which the instruction becomes,
// or a value that was already there, which the instruction is replaced by.
enum Folded {
    Lit(TIRLit),
    Same(SIRValueId),
}

// Every operator whose operands are already worked out.
//
// The type is the difference between this and the same rewrite in `gir::opt`.
// There, `let x = 5` written into its uses would have given each use its own
// type where the binding gave them one between them, so folding stopped at
// what needed no types. Here `body.values[def].ty` is the answer the checker
// settled, and the fold is checked against it: a sum that does not fit the
// type it was going to be held in is not folded, because the literal that came
// out would be a different program.
fn fold(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut held = made(body);
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut changed = false;

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let mut gone = vec![false; body.blocks[at].insts.len()];
        for index in 0..body.blocks[at].insts.len() {
            let Some(def) = body.blocks[at].insts[index].def else { continue };
            let want = prim(ttir, body.values[def].ty);
            // Operands first: an operand this pass has already replaced is
            // read under the name it had, and what it holds is under the name
            // it came to.
            let folded = {
                let mut kind = body.blocks[at].insts[index].kind.clone();
                for value in SIRBody::uses_mut(&mut kind) {
                    *value = settle(&subst, *value);
                }
                match kind {
                    SIRInstKind::Unary { op, operand } => unary(&held, op, operand, want),
                    SIRInstKind::Binary { op, lhs, rhs } => binary(&held, op, lhs, rhs, want),
                    SIRInstKind::Cast(of) => cast(&held, of, want),
                    other => built(&held, ttir, &other, body.values[def].ty),
                }
            };
            match folded {
                None => {}
                Some(Folded::Lit(value)) => {
                    held[def] = Some(SIRInstKind::Literal(value.clone()));
                    body.blocks[at].insts[index].kind = SIRInstKind::Literal(value);
                    stats.folded += 1;
                    changed = true;
                }
                Some(Folded::Same(value)) => {
                    let value = settle(&subst, value);
                    // Whatever the operand was made by is what this is made by
                    // now, so a chain of identities settles in one walk.
                    held[def] = held.get(value).cloned().flatten();
                    subst.insert(def, value);
                    gone[index] = true;
                    stats.folded += 1;
                    changed = true;
                }
            }
        }
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[index - 1]
        });
    }
    replace(body, &subst);
    changed
}

fn unary(
    made: &[Option<SIRInstKind>],
    op: TIRUnaryOp,
    operand: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    let value = lit_of(made, operand)?;
    let folded = match (op, value) {
        (TIRUnaryOp::Not, TIRLit::Bool(b)) => TIRLit::Bool(!b),
        (TIRUnaryOp::Not, TIRLit::Int(n)) => TIRLit::Int(fits(want?, !(*n as i128))?),
        (TIRUnaryOp::Neg, TIRLit::Int(n)) => TIRLit::Int(fits(want?, -(*n as i128))?),
        (TIRUnaryOp::Neg, TIRLit::Float(x)) => real(want?, -*x)?,
        // Taking a reference to a literal is not the literal.
        _ => return None,
    };
    Some(Folded::Lit(folded))
}

fn binary(
    made: &[Option<SIRInstKind>],
    op: TIRBinOp,
    lhs: SIRValueId,
    rhs: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    match (lit_of(made, lhs), lit_of(made, rhs)) {
        (Some(a), Some(b)) => both(op, a, b, want).map(Folded::Lit),
        _ => idem(made, op, lhs, rhs, want),
    }
}

fn both(op: TIRBinOp, a: &TIRLit, b: &TIRLit, want: Option<TIRPrim>) -> Option<TIRLit> {
    match (a, b) {
        (TIRLit::Int(x), TIRLit::Int(y)) => int(op, *x, *y, want),
        (TIRLit::Float(x), TIRLit::Float(y)) => real_op(op, *x, *y, want),
        (TIRLit::Bool(x), TIRLit::Bool(y)) => match op {
            TIRBinOp::And | TIRBinOp::BitAnd => Some(TIRLit::Bool(*x && *y)),
            TIRBinOp::Or | TIRBinOp::BitOr => Some(TIRLit::Bool(*x || *y)),
            TIRBinOp::Xor | TIRBinOp::BitXor => Some(TIRLit::Bool(x != y)),
            _ => compare(op, x, y),
        },
        (TIRLit::Char(x), TIRLit::Char(y)) => compare(op, x, y),
        (TIRLit::Str(x), TIRLit::Str(y)) => compare(op, x, y),
        (TIRLit::Null, TIRLit::Null) => compare(op, &(), &()),
        _ => None,
    }
}

// Integers fold in i128 and are then held to the type the checker gave the
// result. i128 is wide enough that nothing an i64 pair can do to it overflows,
// so the only question left is the one `fits` asks.
fn int(op: TIRBinOp, x: i64, y: i64, want: Option<TIRPrim>) -> Option<TIRLit> {
    let (x, y) = (x as i128, y as i128);
    let worked = match op {
        TIRBinOp::Add => x + y,
        TIRBinOp::Sub => x - y,
        TIRBinOp::Mul => x * y,
        // Dividing by zero is the program's mistake to make, not this pass's
        // to commit on its behalf.
        TIRBinOp::Div => x.checked_div(y)?,
        TIRBinOp::Rem => x.checked_rem(y)?,
        // A shift as wide as the value is a shift this pass has no answer for:
        // what an i64 does at 64 is not what the narrower type would do, and
        // the type is not always one of them.
        TIRBinOp::Shl => x.checked_shl(width(y)?)?,
        TIRBinOp::Shr => x.checked_shr(width(y)?)?,
        TIRBinOp::BitAnd => x & y,
        TIRBinOp::BitOr => x | y,
        TIRBinOp::BitXor => x ^ y,
        _ => return compare(op, &x, &y),
    };
    Some(TIRLit::Int(fits(want?, worked)?))
}

fn width(y: i128) -> Option<u32> {
    let shift = u32::try_from(y).ok()?;
    (shift < 64).then_some(shift)
}

// Whether the answer can be held in the type it is going to be held in, and
// the answer itself if it can. A `TIRLit::Int` is an i64 whatever the type is,
// so that is a second ceiling and not only the type's.
fn fits(p: TIRPrim, n: i128) -> Option<i64> {
    use TIRPrim::*;
    let ok = match p {
        I8 => (i8::MIN as i128..=i8::MAX as i128).contains(&n),
        I16 => (i16::MIN as i128..=i16::MAX as i128).contains(&n),
        I32 => (i32::MIN as i128..=i32::MAX as i128).contains(&n),
        I64 | I128 => (i64::MIN as i128..=i64::MAX as i128).contains(&n),
        U8 => (0..=u8::MAX as i128).contains(&n),
        U16 => (0..=u16::MAX as i128).contains(&n),
        U32 => (0..=u32::MAX as i128).contains(&n),
        // A literal is an i64, so what a u64 can hold past that is not
        // something a folded one could be written as anyway.
        U64 | U128 => (0..=i64::MAX as i128).contains(&n),
        _ => false,
    };
    ok.then(|| n as i64)
}

// Floats fold now that which one they are is settled -- `gir::opt` would not,
// and said why: f32 and f64 round differently and the choice had not been
// made. It is made here, so an f32 folds in f32.
//
// Only where the answer stays finite. An overflow to an infinity or a zero
// divided by a zero is a fold that has left the range the operands were in,
// and a literal infinity is not what the source wrote.
fn real_op(op: TIRBinOp, x: f64, y: f64, want: Option<TIRPrim>) -> Option<TIRLit> {
    if let Some(held) = compare(op, &x, &y) {
        return Some(held);
    }
    let p = want?;
    if p == TIRPrim::F32 {
        let (x, y) = (x as f32, y as f32);
        let worked = match op {
            TIRBinOp::Add => x + y,
            TIRBinOp::Sub => x - y,
            TIRBinOp::Mul => x * y,
            TIRBinOp::Div => x / y,
            TIRBinOp::Rem => x % y,
            _ => return None,
        };
        return worked.is_finite().then(|| TIRLit::Float(worked as f64));
    }
    let worked = match op {
        TIRBinOp::Add => x + y,
        TIRBinOp::Sub => x - y,
        TIRBinOp::Mul => x * y,
        TIRBinOp::Div => x / y,
        TIRBinOp::Rem => x % y,
        _ => return None,
    };
    (p == TIRPrim::F64 && worked.is_finite()).then(|| TIRLit::Float(worked))
}

fn real(p: TIRPrim, x: f64) -> Option<TIRLit> {
    match p {
        TIRPrim::F32 => (x as f32).is_finite().then(|| TIRLit::Float(x as f32 as f64)),
        TIRPrim::F64 => x.is_finite().then_some(TIRLit::Float(x)),
        _ => None,
    }
}

fn compare<T: PartialOrd + PartialEq>(op: TIRBinOp, x: &T, y: &T) -> Option<TIRLit> {
    Some(TIRLit::Bool(match op {
        TIRBinOp::Eq => x == y,
        TIRBinOp::Ne => x != y,
        TIRBinOp::Lt => x < y,
        TIRBinOp::Gt => x > y,
        TIRBinOp::Le => x <= y,
        TIRBinOp::Ge => x >= y,
        _ => return None,
    }))
}

// A cast of a literal to a type that can hold it is that literal. Only between
// integers: what `as` does to a float that will not fit, or to a char, is not
// written down anywhere yet, and a fold is not the place to decide it.
fn cast(made: &[Option<SIRInstKind>], of: SIRValueId, want: Option<TIRPrim>) -> Option<Folded> {
    let p = want?;
    if !integer(p) {
        return None;
    }
    let TIRLit::Int(n) = lit_of(made, of)? else { return None };
    Some(Folded::Lit(TIRLit::Int(fits(p, *n as i128)?)))
}

// Reading out of something this body has just built. `Point { x: 1, y: 2 }.x`
// is `1` twice over -- once because the field is there in the literal, and
// once because reading it made a copy of what was put there -- and after a
// call has been written out that is most of what an argument passed as a
// struct turns into.
//
// The type is what says whether the copy may go. A field that is something to
// release is a field whose copy is a second thing to release, and naming the
// one that was put in would leave two releases of it; `shareable` is the same
// rule `share` is held to, and for the same reason.
//
// The discriminant is the one of these that answers with a literal rather than
// with a value that was already there: what a variant's tag *is* is written in
// the declaration, which is where `sir::lower` reads it from as well.
fn built(
    made: &[Option<SIRInstKind>],
    ttir: &TTIRProgram,
    kind: &SIRInstKind,
    ty: TyId,
) -> Option<Folded> {
    match kind {
        SIRInstKind::Discriminant(of) => {
            let Some(SIRInstKind::VariantLit { item, variant, .. }) = made.get(*of)? else {
                return None;
            };
            let TTIRItemKind::Enum { variants, .. } = &ttir.items.get(*item)?.kind else {
                return None;
            };
            let tag = variants.get(*variant).map(|v| v.value).unwrap_or(*variant as i64);
            Some(Folded::Lit(TIRLit::Int(tag)))
        }
        _ if !shareable(ttir, ty) => None,
        SIRInstKind::Field { base, index } => {
            let Some(SIRInstKind::StructLit { fields, .. }) = made.get(*base)? else {
                return None;
            };
            fields.get(*index).map(|held| Folded::Same(*held))
        }
        SIRInstKind::TupleIndex { base, index } => {
            let Some(SIRInstKind::TupleLit(fields)) = made.get(*base)? else { return None };
            fields.get(*index as usize).map(|held| Folded::Same(*held))
        }
        SIRInstKind::Payload { of, variant, index } => {
            let Some(SIRInstKind::VariantLit { variant: made_as, fields, .. }) = made.get(*of)?
            else {
                return None;
            };
            // Reading the payload of a variant the value is not is reading
            // what is not there. `sir::lower` only ever puts one under a test
            // that has already settled which variant it is, so this is a
            // shape that should not arise -- and answering it wrongly would be
            // worse than leaving it alone.
            (made_as == variant).then(|| fields.get(*index).map(|held| Folded::Same(*held)))?
        }
        _ => None,
    }
}

// The identities that need one side to be a literal and say nothing about the
// other. Integers only: `x + 0.0` is `x` for every float but one, and the one
// is a negative zero.
//
// `x * 0` is the odd one out -- it answers without the other side at all --
// and it is still sound, because the instruction that worked the other side
// out is left standing. If nothing else reads it, `sweep` is what decides
// whether it may go, and `sweep` knows about traps.
fn idem(
    made: &[Option<SIRInstKind>],
    op: TIRBinOp,
    lhs: SIRValueId,
    rhs: SIRValueId,
    want: Option<TIRPrim>,
) -> Option<Folded> {
    let p = want?;
    if !integer(p) {
        return None;
    }
    let whole = |value| match lit_of(made, value) {
        Some(TIRLit::Int(n)) => Some(*n),
        _ => None,
    };
    let (a, b) = (whole(lhs), whole(rhs));
    let folded = match (op, a, b) {
        (TIRBinOp::Add, Some(0), _) | (TIRBinOp::Mul, Some(1), _) => Folded::Same(rhs),
        (TIRBinOp::BitOr, Some(0), _) | (TIRBinOp::BitXor, Some(0), _) => Folded::Same(rhs),
        (TIRBinOp::Add, _, Some(0))
        | (TIRBinOp::Sub, _, Some(0))
        | (TIRBinOp::Mul, _, Some(1))
        | (TIRBinOp::Div, _, Some(1))
        | (TIRBinOp::Shl, _, Some(0))
        | (TIRBinOp::Shr, _, Some(0))
        | (TIRBinOp::BitOr, _, Some(0))
        | (TIRBinOp::BitXor, _, Some(0)) => Folded::Same(lhs),
        (TIRBinOp::Mul, Some(0), _) | (TIRBinOp::Mul, _, Some(0)) => {
            Folded::Lit(TIRLit::Int(0))
        }
        (TIRBinOp::BitAnd, Some(0), _) | (TIRBinOp::BitAnd, _, Some(0)) => {
            Folded::Lit(TIRLit::Int(0))
        }
        _ => return None,
    };
    Some(folded)
}

// ---- Phis that joined one answer ------------------------------------------

// A phi whose edges all name one value is a join where nothing was decided:
// every way in brought the same thing, so the phi *is* that thing. Its own
// name among the edges does not count -- a loop's phi naming itself along the
// back edge still has one answer, which is what came in the first time round.
fn phis(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        body.blocks[at].phis.retain(|phi| {
            let mut one: Option<SIRValueId> = None;
            for (_, value) in &phi.edges {
                if *value == phi.def {
                    continue;
                }
                match one {
                    None => one = Some(*value),
                    Some(held) if held == *value => {}
                    // Two answers, so the phi is what says which.
                    Some(_) => return true,
                }
            }
            match one {
                Some(value) => {
                    subst.insert(phi.def, value);
                    false
                }
                // Every edge named the phi itself, which is a value with no
                // first answer at all. Nothing here can invent one.
                None => true,
            }
        });
    }
    stats.shared += subst.len();
    let changed = !subst.is_empty();
    replace(body, &subst);
    changed
}

// ---- One value for two instructions ---------------------------------------

// Two instructions that read the same values and do the same thing to them
// make the same value, so the second can be the first -- but only where the
// first stands before it on every path, which is dominance and nothing weaker.
// So the walk is down the dominator tree: what a block adds is visible to
// everything below it and taken back off on the way out, which is exactly the
// set of instructions that stand before the block being walked.
fn share(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let doms = Dominators::of(body);
    let children = doms.children();
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    // What is in hand, deepest last, and how much of it each block added. A
    // list and not a map: `SIRInstKind` holds an f64 and so cannot be hashed,
    // and the lists a block's worth of instructions makes are short.
    let mut seen: Vec<(SIRInstKind, TyId, SIRValueId)> = Vec::new();
    let mut added = vec![0usize; body.blocks.len()];

    let mut work = vec![(body.entry, false)];
    while let Some((at, leaving)) = work.pop() {
        if leaving {
            seen.truncate(added[at]);
            continue;
        }
        added[at] = seen.len();
        work.push((at, true));

        for index in 0..body.blocks[at].insts.len() {
            let Some(def) = body.blocks[at].insts[index].def else { continue };
            let mut kind = body.blocks[at].insts[index].kind.clone();
            for value in SIRBody::uses_mut(&mut kind) {
                *value = settle(&subst, *value);
            }
            if !known(&kind) {
                continue;
            }
            let ty = body.values[def].ty;
            // An address is a place and not a thing: two names for one place
            // are one name whatever is kept there, which is why the addresses
            // do not go through `shareable` and everything else does.
            let place = matches!(
                kind,
                SIRInstKind::Addr(_)
                    | SIRInstKind::ItemAddr(_)
                    | SIRInstKind::SelfAddr
                    | SIRInstKind::FieldAddr { .. }
                    | SIRInstKind::TupleAddr { .. }
            );
            if !place && !shareable(ttir, ty) {
                continue;
            }
            match seen.iter().find(|(held, of, _)| alike(ttir, *of, ty) && *held == kind) {
                Some((_, _, held)) => {
                    subst.insert(def, *held);
                    gone[at][index] = true;
                    stats.shared += 1;
                }
                None => seen.push((kind, ty, def)),
            }
        }

        for &child in &children[at] {
            if live[child] {
                work.push((child, false));
            }
        }
    }

    if subst.is_empty() {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    replace(body, &subst);
    true
}

// ---- Branches with one edge -----------------------------------------------

// A branch on a literal goes one way, and a branch whose two edges go to one
// block was never a branch. Either way the block that stops being reached has
// to be told: a phi has one entry per way in, and a way in that has gone is an
// entry that has to go with it.
fn branches(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let live = body.live();
    let held = made(body);
    let mut changed = false;
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let SIRTerm::Branch { cond, then, els } = body.blocks[at].term else { continue };
        let to = match lit_of(&held, cond) {
            Some(TIRLit::Bool(true)) => then,
            Some(TIRLit::Bool(false)) => els,
            _ if then == els => then,
            _ => continue,
        };
        body.blocks[at].term = SIRTerm::Goto(to);
        stats.blocks += 1;
        changed = true;
    }
    if changed {
        repair(body);
    }
    changed
}

// Phis held to the ways in the block actually has. Only ever fewer: nothing in
// this pass gives a block a way in it had not got, and `merge` renames the one
// edge it moves rather than adding one.
fn repair(body: &mut SIRBody) {
    let live = body.live();
    let preds = body.preds();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let ways: Vec<SIRBlockId> =
            preds[at].iter().copied().filter(|&p| live[p]).collect();
        for phi in &mut body.blocks[at].phis {
            let mut kept: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
            for &(from, value) in phi.edges.iter() {
                if ways.contains(&from) && !kept.iter().any(|(held, _)| *held == from) {
                    kept.push((from, value));
                }
            }
            phi.edges = kept;
        }
    }
}

// ---- Blocks folded into the block above them ------------------------------

// A block with one way in, and that way a `Goto`, is the tail of the block
// that goes there. Joining the two is what leaves an instruction next to the
// one it repeats, which is most of what `share` and `fold` need to see.
//
// Only where the block has no phis. A phi with one way in is a phi with one
// answer, which `phis` takes out a round earlier -- so this waits rather than
// working out what a phi means in a block that no longer begins anywhere.
fn merge(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let mut changed = false;
    loop {
        let live = body.live();
        let preds = body.preds();
        let mut joined = None;
        for at in 0..body.blocks.len() {
            if !live[at] {
                continue;
            }
            let SIRTerm::Goto(to) = body.blocks[at].term else { continue };
            if to == at || to == body.entry || !body.blocks[to].phis.is_empty() {
                continue;
            }
            if preds[to].iter().filter(|&&p| live[p]).count() != 1 {
                continue;
            }
            joined = Some((at, to));
            break;
        }
        let Some((at, to)) = joined else { return changed };

        let mut moved = std::mem::take(&mut body.blocks[to].insts);
        let term = std::mem::replace(&mut body.blocks[to].term, SIRTerm::Unreachable);
        body.blocks[at].insts.append(&mut moved);
        // Whoever heard from the block that has gone hears from this one now.
        for next in term.targets() {
            for phi in &mut body.blocks[next].phis {
                for (from, _) in &mut phi.edges {
                    if *from == to {
                        *from = at;
                    }
                }
            }
        }
        body.blocks[at].term = term;
        stats.blocks += 1;
        changed = true;
    }
}

// ---- What nothing reads ---------------------------------------------------

// A value nothing reads and nothing needs run is a value that was never worth
// working out. Marked and then swept: an instruction is wanted if what it
// makes is wanted, and what it reads is wanted if it is -- so the walk starts
// at the instructions that have to run whatever else happens, and everything
// it does not reach goes.
//
// Blocks nothing reaches go the same way, and first: an instruction standing
// in one is not run either, and leaving it there would keep alive whatever it
// reads.
fn sweep(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let live = body.live();
    let mut changed = false;
    for at in 0..body.blocks.len() {
        let emptied = body.blocks[at].term == SIRTerm::Unreachable
            && body.blocks[at].insts.is_empty()
            && body.blocks[at].phis.is_empty();
        if live[at] || emptied {
            continue;
        }
        stats.dead += body.blocks[at].insts.len();
        stats.blocks += 1;
        body.blocks[at].phis.clear();
        body.blocks[at].insts.clear();
        body.blocks[at].term = SIRTerm::Unreachable;
        changed = true;
    }

    let held = made(body);
    let reads = operands(body);
    let mut wanted = vec![false; body.values.len()];
    let mut work: Vec<SIRValueId> = Vec::new();
    let want = |value: SIRValueId, wanted: &mut Vec<bool>, work: &mut Vec<SIRValueId>| {
        if value < wanted.len() && !wanted[value] {
            wanted[value] = true;
            work.push(value);
        }
    };

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for inst in &body.blocks[at].insts {
            if effects(&body.values, ttir, &held, &inst.kind) {
                for value in SIRBody::uses(&inst.kind) {
                    want(value, &mut wanted, &mut work);
                }
            }
        }
        match &body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => want(*cond, &mut wanted, &mut work),
            SIRTerm::Return(Some(value)) => want(*value, &mut wanted, &mut work),
            _ => {}
        }
    }
    while let Some(value) = work.pop() {
        for &read in &reads[value] {
            want(read, &mut wanted, &mut work);
        }
    }

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let before = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        body.blocks[at].phis.retain(|phi| wanted[phi.def]);
        // Worked out before the list is touched: what an instruction is for
        // is a question about the whole body, and the answer cannot be asked
        // for while the list it is about is being written to.
        let keep: Vec<bool> = body.blocks[at]
            .insts
            .iter()
            .map(|inst| match inst.def {
                Some(def) => wanted[def] || effects(&body.values, ttir, &held, &inst.kind),
                // An instruction that makes nothing is there for what it does,
                // and one that does nothing either is one nothing put there.
                None => effects(&body.values, ttir, &held, &inst.kind),
            })
            .collect();
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            keep[index - 1]
        });
        let after = body.blocks[at].insts.len() + body.blocks[at].phis.len();
        if after != before {
            stats.dead += before - after;
            changed = true;
        }
    }
    changed
}

// ---- What a store put there ------------------------------------------------

// A load below a store to the same address finds what the store wrote, so it
// need not go and look: the value is already in hand. And a second load of an
// address nothing has written since finds what the first one found.
//
// This is the rewrite `share` cannot make. Two instructions with the same
// operands make the same value, which is why `share` may put one where two
// were -- but a load's operands are an address, and what is *at* an address is
// not among them. What is at it is whatever the last write left, so the
// question is which writes stand between the two, and that is what `alias`
// answers.
//
// Within a block and no further. Following the answer across a join means
// carrying what is known at every edge and joining it where they meet, which
// is a memory SSA and is a larger thing than this; a block at a time catches
// the shape that matters -- a name written and read on the next line -- and
// `hoist` is what carries a load out of a loop.
//
// Three things end what is known. A store to an address that may be the same
// one replaces it. A call, a method or a release may write anywhere it can
// reach, so everything goes but what is rooted in a name of this frame whose
// address nothing kept. And a value with something to release is never
// forwarded at all: the load would be the value the store wrote rather than a
// copy of it, and both would be released.
fn forward(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    let alias = Alias::of(body);
    let live = body.live();
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        // What is at an address, in the order it was learnt.
        let mut known: Vec<(SIRValueId, SIRValueId)> = Vec::new();
        for index in 0..body.blocks[at].insts.len() {
            match body.blocks[at].insts[index].kind {
                SIRInstKind::Store { to, value } => {
                    known.retain(|(addr, _)| !alias.may(*addr, to));
                    known.push((to, settle(&subst, value)));
                }
                SIRInstKind::Load { from } => {
                    let Some(def) = body.blocks[at].insts[index].def else { continue };
                    if !shareable(ttir, body.values[def].ty) {
                        continue;
                    }
                    let found = known
                        .iter()
                        .rev()
                        .find(|(addr, _)| alias.must(*addr, from))
                        .map(|(_, held)| *held);
                    match found {
                        // The types have to agree as well as the addresses. A
                        // union read back as the other arm is one address and
                        // two values, and this pass is not the place to decide
                        // what that means.
                        Some(held) if alike(ttir, body.values[held].ty, body.values[def].ty) => {
                            subst.insert(def, held);
                            gone[at][index] = true;
                            stats.forwarded += 1;
                        }
                        _ => known.push((from, def)),
                    }
                }
                SIRInstKind::Call { .. }
                | SIRInstKind::Method { .. }
                | SIRInstKind::Drop(_)
                | SIRInstKind::DropSlot(_) => {
                    known.retain(|(addr, _)| alias.own(*addr));
                }
                // A run of places written at once, and only the first of them
                // named. See `overwritten`, where the same answer is given for
                // the same reason.
                SIRInstKind::VecStore { .. } => known.clear(),
                _ => {}
            }
        }
    }

    if subst.is_empty() {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    replace(body, &subst);
    true
}

// ---- Stores nothing will read ---------------------------------------------

// A store whose value is written over before anything reads it is a store that
// need not have happened. The mirror of `forward`, and it reads the block the
// other way round: from the bottom, holding the addresses that are certainly
// written again below, and dropping one as soon as something between might
// read it.
//
// It has to be `must` below and `may` between, and the two are not the same
// question turned round. A store is dead only if what overwrites it certainly
// lands on the same place; it is alive again if anything that might read it
// stands in the way. Getting either the wrong way about is a store dropped
// that somebody wanted.
//
// A block at a time, again, and for the same reason as `forward`: what a store
// is worth past the end of its block is a question about every path out of it.
// Stopping at the end of the block is what makes "nothing reads it" a fact
// about a straight line rather than a claim about the graph.
fn overwritten(body: &mut SIRBody, stats: &mut Stats) -> bool {
    let alias = Alias::of(body);
    let live = body.live();
    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    let mut changed = false;

    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        // Addresses written again below without being read in between.
        let mut over: Vec<SIRValueId> = Vec::new();
        for index in (0..body.blocks[at].insts.len()).rev() {
            match body.blocks[at].insts[index].kind {
                SIRInstKind::Store { to, .. } => {
                    if over.iter().any(|&held| alias.must(held, to)) {
                        gone[at][index] = true;
                        stats.dead += 1;
                        changed = true;
                    } else {
                        over.push(to);
                    }
                }
                SIRInstKind::Load { from } => over.retain(|&held| !alias.may(held, from)),
                // Releasing what is in a name reads what is in it.
                SIRInstKind::DropSlot(slot) => over.retain(|&held| {
                    alias.place(held).map(|p| p.base) != Some(Base::Slot(slot))
                }),
                SIRInstKind::Drop(value) => {
                    over.retain(|&held| alias.own(held) && !alias.may(held, value))
                }
                // A call reads wherever it can reach, which is everywhere but
                // a name of this frame whose address nothing kept.
                SIRInstKind::Call { .. } | SIRInstKind::Method { .. } => {
                    over.retain(|&held| alias.own(held))
                }
                // A vector store writes a run of places and this knows the
                // address of the first of them only. Rather than reason about
                // how far it reaches, nothing is held across one -- which
                // costs nothing worth having: it is written by the last
                // rewrite in the round, after this one has already run.
                SIRInstKind::VecStore { .. } => over.clear(),
                _ => {}
            }
        }
    }

    if !changed {
        return false;
    }
    for at in 0..body.blocks.len() {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    true
}

// ---- Out of the loop ------------------------------------------------------

// An instruction inside a loop whose operands all come from outside it works
// out the same value every turn, so it belongs before the loop rather than in
// it. That is the whole of loop-invariant code motion, and the two words that
// carry it are "all" and "outside" -- which is why it is a fixpoint: the first
// instruction lifted makes its own value one that comes from outside, and the
// instruction that read it becomes liftable in the same walk.
//
// Three things hold it back, and each is a rule about soundness rather than
// about whether the move is worth making.
//
// It runs on a path the loop may not. A loop that turns nought times still
// reaches its preheader, so what is lifted there runs where it would not have
// -- which is why only instructions with nothing to do and nothing to trap on
// may go. `effects` is the same answer `sweep` is held to, and a division that
// might be by zero fails both for the same reason.
//
// It runs once where it ran every turn. A value with something to release is a
// value released every turn by the release the loop already holds, and lifting
// what made it would leave one thing released many times. So the type is held
// to `shareable`, exactly as `share` is, and for exactly that reason.
//
// And it may not be the same value twice. A `Load` finds what is there, and
// what is there is what the last store put there -- so a load may be lifted
// only out of a loop that stores nothing, calls nothing, and releases nothing.
// Anything narrower would need to know which addresses the loop writes, which
// is an alias analysis, and there is not one.
fn hoist(body: &mut SIRBody, ttir: &TTIRProgram, stats: &mut Stats) -> bool {
    // The preheaders first, all of them, and then the loops found again: a
    // block made here belongs to whatever loop stands outside the one it was
    // made for, and a bitmap worked out before it existed does not say so.
    let mut changed = false;
    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        let before = body.blocks.len();
        preheader(body, &held);
        changed |= body.blocks.len() != before;
    }

    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        changed |= lift(body, ttir, &held, stats);
    }
    changed
}

fn lift(body: &mut SIRBody, ttir: &TTIRProgram, held: &Loop, stats: &mut Stats) -> bool {
    let Some(pre) = preheader(body, held) else { return false };
    if held.has(pre) {
        return false;
    }

    // What the loop writes, so that a load can be asked whether any of it
    // lands where it reads. Three kinds: the addresses stored to, the slots
    // released, and whether it calls out at all -- a call writes wherever it
    // can reach, which is everywhere but a name of this frame whose address
    // nothing kept.
    let alias = Alias::of(body);
    let held_made = made(body);
    let mut wrote: Vec<SIRValueId> = Vec::new();
    let mut released: Vec<SIRSlotId> = Vec::new();
    let mut calls = false;
    for &at in &held.blocks {
        for inst in &body.blocks[at].insts {
            match &inst.kind {
                SIRInstKind::Store { to, .. } => wrote.push(*to),
                SIRInstKind::DropSlot(slot) => released.push(*slot),
                SIRInstKind::Call { .. } | SIRInstKind::Method { .. } | SIRInstKind::Drop(_) => {
                    calls = true
                }
                // A vector store reaches further than the address it names, so
                // it is treated as reaching everywhere rather than reasoned
                // about.
                SIRInstKind::VecStore { .. } => calls = true,
                _ => {}
            }
        }
    }
    let quiet = |from: SIRValueId| {
        if wrote.iter().any(|&to| alias.may(to, from)) {
            return false;
        }
        if released.iter().any(|&slot| alias.place(from).map(|p| p.base) == Some(Base::Slot(slot)))
        {
            return false;
        }
        !calls || alias.own(from)
    };

    // What the loop makes, which is what "comes from outside" is the negation
    // of. Cleared as an instruction is lifted, so that what read it is lifted
    // too on the same walk down.
    let mut within = vec![false; body.values.len()];
    for &at in &held.blocks {
        for phi in &body.blocks[at].phis {
            within[phi.def] = true;
        }
        for inst in &body.blocks[at].insts {
            if let Some(def) = inst.def {
                within[def] = true;
            }
        }
    }

    let mut gone: Vec<Vec<bool>> =
        body.blocks.iter().map(|b| vec![false; b.insts.len()]).collect();
    let mut moved: Vec<SIRInst> = Vec::new();
    for &at in &held.blocks {
        for index in 0..body.blocks[at].insts.len() {
            let inst = &body.blocks[at].insts[index];
            let Some(def) = inst.def else { continue };
            if !liftable(ttir, &body.values, &held_made, &inst.kind, body.values[def].ty) {
                continue;
            }
            if let SIRInstKind::Load { from } = inst.kind {
                if !quiet(from) {
                    continue;
                }
            }
            if SIRBody::uses(&inst.kind).iter().any(|&value| within[value]) {
                continue;
            }
            within[def] = false;
            moved.push(inst.clone());
            gone[at][index] = true;
        }
    }
    if moved.is_empty() {
        return false;
    }

    for &at in &held.blocks {
        let mut index = 0;
        body.blocks[at].insts.retain(|_| {
            index += 1;
            !gone[at][index - 1]
        });
    }
    // In the order they were met, which is the order they were written in: a
    // lifted instruction whose operand was lifted with it stands below it,
    // because the walk down the loop meets a value before it is read.
    stats.hoisted += moved.len();
    body.blocks[pre].insts.append(&mut moved);
    true
}

fn liftable(
    ttir: &TTIRProgram,
    values: &[SIRValue],
    made: &[Option<SIRInstKind>],
    kind: &SIRInstKind,
    ty: TyId,
) -> bool {
    let place = matches!(
        kind,
        SIRInstKind::Addr(_)
            | SIRInstKind::ItemAddr(_)
            | SIRInstKind::SelfAddr
            | SIRInstKind::FieldAddr { .. }
            | SIRInstKind::TupleAddr { .. }
            | SIRInstKind::IndexAddr { .. }
    );
    if !place && !shareable(ttir, ty) {
        return false;
    }
    // Nothing that may trap, which is the same list `sweep` is held to and for
    // the mirror of the same reason: a loop that turns nought times still
    // reaches the block this is going into, so a division by something that
    // might be zero, or an index that might be past the end, would be a trap
    // moved onto a path it was not on. `known` is not that question -- `share`
    // puts nothing anywhere new -- which is why both are asked here.
    if effects(values, ttir, made, kind) {
        return false;
    }
    // A load is liftable as far as this is concerned; whether what it reads
    // stays put for the length of the loop is `quiet`'s to say, and it is the
    // only one of these that has to ask.
    known(kind) || matches!(kind, SIRInstKind::Load { .. })
}

// ---- The loop written out as the turns it runs ----------------------------

// A loop whose number of turns is known before it starts is a straight line
// with the body written down that many times, and no test between the copies
// because there is nothing left for a test to decide.
//
// It is worth more here than the instructions it saves. `for i in 0..4` walks
// a cursor nothing can see into, and the value `i` takes is a question only
// the loop can answer -- until the turns are written out, and then `i` is 0 in
// the first copy and 1 in the second, and every operator over it folds. What
// unrolling really does in this pass is hand the four rewrites above something
// to work on.
//
// Which loops those are is the closed set `sir::lower` walks (§5: "the
// language has no iterator protocol, so what may be run through is a closed
// set"), asked one question: how many. A range between two literals runs the
// difference between them; an array of `T[n]` runs n. A run, a set and a map
// have a length nobody has worked out yet and are left alone.
//
// Three things are required of the shape, and the third is the one that
// refuses the most:
//
//   - the head ends in the walk's own test, and the arm it fails to is
//     outside the loop -- which is what makes the test the thing being taken
//     out;
//   - the copies fit: the turns are few and the body is small, because this
//     is the one rewrite here that makes a program bigger on purpose, and how
//     few and how small is what a `Level` says;
//   - and nothing the loop worked out is read past it except through a phi.
//     A phi is answered by giving it one entry per copy, which the rewrite
//     does anyway; anything else wanted one block standing before it, and
//     after this there are as many blocks as there were turns. With the head's
//     failing test as the only way out that never bites -- what the head made
//     is taken from the last head, which is the one that ran -- so it is only
//     a `break` that this ever turns down, and only a `break` that carries a
//     value out without a phi to carry it.
// How many turns, and what the loop variable is on each of them.
struct Turns {
    count: usize,
    // The first value and the type it is held in, where the walk is over a
    // range between two literals: then the element of turn `i` is `first + i`
    // and no cursor need survive. `None` for an array, whose elements are
    // whatever is in it and are still read one at a time.
    first: Option<(i64, TIRPrim)>,
}

fn unroll(body: &mut SIRBody, ttir: &TTIRProgram, level: Level, stats: &mut Stats) -> bool {
    let doms = Dominators::of(body);
    for held in Loop::all(body, &doms) {
        let Some((elem, exit)) = walked(body, &held) else { continue };
        let Some(turns) = counted(body, ttir, &held, elem, level) else { continue };
        let size: usize = held.blocks.iter().map(|&at| body.blocks[at].insts.len()).sum();
        if turns.count > level.unroll_turns() || size * (turns.count + 1) > level.unroll_insts() {
            continue;
        }
        // A second way out is a `break`, and it is allowed as long as nothing
        // the loop worked out is read past it other than through a phi. With
        // one way out that is not a limit at all -- what the head made can be
        // taken from the last head, which is the one that ran -- but a break
        // reaches the code after the loop without passing through the head, so
        // there is no one copy to take it from.
        if held.ways_out(body) != vec![(held.head, exit)] && reaches_out(body, &held) {
            continue;
        }
        written_round(body, &held, &turns, exit);
        stats.unrolled += 1;
        return true;
    }
    false
}

// Whether anything the loop makes is read outside it by something other than a
// phi. A phi is answered by giving it one edge per copy; anything else needs
// one block standing before it, and after this rewrite there are as many
// blocks as there were turns.
fn reaches_out(body: &SIRBody, held: &Loop) -> bool {
    let live = body.live();
    let mut within = vec![false; body.values.len()];
    for &at in &held.blocks {
        for phi in &body.blocks[at].phis {
            within[phi.def] = true;
        }
        for inst in &body.blocks[at].insts {
            if let Some(def) = inst.def {
                within[def] = true;
            }
        }
    }
    for at in 0..body.blocks.len() {
        if !live[at] || held.has(at) {
            continue;
        }
        for inst in &body.blocks[at].insts {
            if SIRBody::uses(&inst.kind).iter().any(|&value| within[value]) {
                return true;
            }
        }
        match &body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => {
                if within[*cond] {
                    return true;
                }
            }
            SIRTerm::Return(Some(value)) => {
                if within[*value] {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

// Whether the head is the top of a walk, and where it goes when the walk is
// done. The test is what `sir::lower` put there and nothing else looks like
// it: a branch on an `IterValid`, one arm inside the loop and one outside.
fn walked(body: &SIRBody, held: &Loop) -> Option<(SIRValueId, SIRBlockId)> {
    let SIRTerm::Branch { cond, then, els } = body.blocks[held.head].term else { return None };
    if !held.has(then) || held.has(els) {
        return None;
    }
    let made = made(body);
    let Some(SIRInstKind::IterValid { iter, .. }) = made.get(cond)? else { return None };
    Some((*iter, els))
}

// How many turns the walk takes, worked out from the thing being walked.
fn counted(
    body: &SIRBody,
    ttir: &TTIRProgram,
    held: &Loop,
    iter: SIRValueId,
    level: Level,
) -> Option<Turns> {
    let made = made(body);
    // The element type, which is what a range's values have to fit in.
    let elem = held.blocks.iter().find_map(|&at| {
        body.blocks[at].insts.iter().find_map(|inst| match inst.kind {
            SIRInstKind::IterElem { .. } => inst.def.map(|def| body.values[def].ty),
            _ => None,
        })
    });

    if let Some(SIRInstKind::Range { op, start: Some(from), end: Some(to) }) = made.get(iter)? {
        let (Some(TIRLit::Int(from)), Some(TIRLit::Int(to))) =
            (lit_of(&made, *from), lit_of(&made, *to))
        else {
            return None;
        };
        // In i128, where a range between the two ends of an i64 is still a
        // number: how many turns it takes is asked before anything decides
        // whether that is few enough to write out.
        let last = match op {
            TIRRangeOp::Inclusive => *to as i128,
            TIRRangeOp::Exclusive => *to as i128 - 1,
        };
        let count = usize::try_from((last - *from as i128 + 1).max(0)).ok()?;
        if count > level.unroll_turns() {
            return None;
        }
        // The values the loop variable takes are written as literals, so every
        // one of them has to be one the type can hold. The two ends answer for
        // all of them: what lies between them lies between them.
        let p = elem.and_then(|ty| prim(ttir, ty)).filter(|p| integer(*p))?;
        if count > 0 {
            fits(p, *from as i128)?;
            fits(p, *from as i128 + count as i128 - 1)?;
        }
        return Some(Turns { count, first: Some((*from, p)) });
    }
    // An array's length is in its type. What is in it is not, so the cursor
    // stays and only the tests go.
    if let Some(Ty::Array { len, .. }) = ttir.types.get(body.values[iter].ty) {
        return Some(Turns { count: usize::try_from(*len).ok()?, first: None });
    }
    None
}

// The loop, written out.
//
// One copy per turn, and one more of the head alone: the last head is where
// the test would have failed, and it is the block the code after the loop
// hears from -- so it has to be there, even though everything it works out is
// about a turn that does not happen.
//
// Every copy is a copy of the whole loop, values and all. What a copy reads
// that the loop made is that copy's; what it reads from before the loop is
// still the one value there always was. The edges are the only thing that
// differs: a copy's way round goes to the next copy's head rather than back to
// its own, which is what leaves a chain where there was a circle.
fn written_round(body: &mut SIRBody, held: &Loop, turns: &Turns, exit: SIRBlockId) {
    let n = turns.count;
    // By turn, then by block, what each block and each value became. The last
    // turn holds the head alone.
    let mut blocks: Vec<HashMap<SIRBlockId, SIRBlockId>> = Vec::new();
    let mut values: Vec<HashMap<SIRValueId, SIRValueId>> = Vec::new();

    for turn in 0..=n {
        let mut mine = HashMap::new();
        let mut made = HashMap::new();
        for &at in &held.blocks {
            if turn == n && at != held.head {
                continue;
            }
            let copy = body.blocks.len();
            body.blocks.push(body.blocks[at].clone());
            mine.insert(at, copy);
            for index in 0..body.blocks[copy].phis.len() {
                let def = body.blocks[copy].phis[index].def;
                body.values.push(body.values[def].clone());
                let fresh = body.values.len() - 1;
                body.blocks[copy].phis[index].def = fresh;
                made.insert(def, fresh);
            }
            for index in 0..body.blocks[copy].insts.len() {
                let Some(def) = body.blocks[copy].insts[index].def else { continue };
                body.values.push(body.values[def].clone());
                let fresh = body.values.len() - 1;
                body.blocks[copy].insts[index].def = Some(fresh);
                made.insert(def, fresh);
            }
        }
        blocks.push(mine);
        values.push(made);
    }

    let mine = |turn: usize, value: SIRValueId| {
        values[turn].get(&value).copied().unwrap_or(value)
    };

    for turn in 0..=n {
        // Down the loop's own list rather than the map's: what a map hands
        // back is in no order in particular, and two runs over one program
        // should not differ in what they write.
        for at in held.blocks.clone() {
            let Some(&copy) = blocks[turn].get(&at) else { continue };
            // The phis first. What arrives at a head arrives from the turn
            // before it, so its operands are that turn's and not this one's;
            // everywhere else the ways in are all inside the one turn.
            for index in 0..body.blocks[copy].phis.len() {
                let edges = body.blocks[copy].phis[index].edges.clone();
                let mut kept = Vec::new();
                for (from, value) in edges {
                    if at != held.head {
                        let Some(&edge) = blocks[turn].get(&from) else { continue };
                        kept.push((edge, mine(turn, value)));
                        continue;
                    }
                    match (held.has(from), turn) {
                        // The way in from before the loop, which only the
                        // first turn is reached by.
                        (false, 0) => kept.push((from, value)),
                        (false, _) => {}
                        (true, 0) => {}
                        (true, _) => {
                            if let Some(&edge) = blocks[turn - 1].get(&from) {
                                kept.push((edge, mine(turn - 1, value)));
                            }
                        }
                    }
                }
                body.blocks[copy].phis[index].edges = kept;
            }

            for index in 0..body.blocks[copy].insts.len() {
                for value in SIRBody::uses_mut(&mut body.blocks[copy].insts[index].kind) {
                    *value = mine(turn, *value);
                }
                // The element of this turn, where the walk is over a range
                // between two literals: it is `first + turn`, and saying so is
                // what leaves the loop variable a literal for `fold` to work
                // with.
                if let (SIRInstKind::IterElem { .. }, Some((first, p))) =
                    (&body.blocks[copy].insts[index].kind, turns.first)
                {
                    if turn < n {
                        let held = fits(p, first as i128 + turn as i128)
                            .expect("the turns were checked before the copies were made");
                        body.blocks[copy].insts[index].kind =
                            SIRInstKind::Literal(TIRLit::Int(held));
                    }
                }
            }

            // And where it goes. The head's test is settled -- every copy but
            // the last takes the arm that carries on, and the last takes the
            // one that leaves -- and a way round becomes the way into the turn
            // after it.
            let mut term = body.blocks[copy].term.clone();
            if at == held.head {
                let SIRTerm::Branch { then, .. } = term else { unreachable!() };
                term = if turn == n { SIRTerm::Goto(exit) } else { SIRTerm::Goto(then) };
            }
            if let SIRTerm::Branch { cond, .. } = &mut term {
                *cond = mine(turn, *cond);
            }
            for to in term.targets_mut() {
                if !held.has(*to) {
                    continue;
                }
                let next = if *to == held.head { turn + 1 } else { turn };
                if let Some(&edge) = blocks.get(next).and_then(|held| held.get(to)) {
                    *to = edge;
                }
            }
            body.blocks[copy].term = term;
        }
    }

    // What the blocks after the loop hear, and who from. Every edge that used
    // to leave the loop leaves a copy of it now, so the phis they land in take
    // one entry per copy that still goes there -- and the copies that no
    // longer do are answered by `repair`, which holds a phi to the ways in the
    // block actually has.
    let mut outside: Vec<(SIRBlockId, SIRBlockId, usize)> = Vec::new();
    for turn in 0..=n {
        for &at in &held.blocks {
            let Some(&copy) = blocks[turn].get(&at) else { continue };
            for to in body.blocks[copy].term.targets() {
                if !held.has(to) && to < body.blocks.len() {
                    outside.push((at, to, turn));
                }
            }
        }
    }
    for (at, to, turn) in outside {
        let copy = blocks[turn][&at];
        for phi in &mut body.blocks[to].phis {
            let Some(&(_, value)) = phi.edges.iter().find(|(from, _)| *from == at) else {
                continue;
            };
            let held = mine(turn, value);
            if !phi.edges.iter().any(|(from, _)| *from == copy) {
                phi.edges.push((copy, held));
            }
        }
    }
    for at in 0..body.blocks.len() {
        if held.has(at) {
            continue;
        }
        for phi in &mut body.blocks[at].phis {
            phi.edges.retain(|(from, _)| !held.has(*from));
        }
    }

    // The ways in, which go to the first turn now. The loop's own blocks are
    // left standing and unreachable, which is what `sweep` is for.
    for &from in &held.entries {
        for to in body.blocks[from].term.targets_mut() {
            if *to == held.head {
                *to = blocks[0][&held.head];
            }
        }
    }

    // And what the head worked out, read from after the loop: the last head is
    // the one that ran, so it is the one that answers. Nothing else inside can
    // be read out there -- the head's failing test is the only way out, so no
    // other block of the loop stands before anything after it.
    let mut subst: HashMap<SIRValueId, SIRValueId> = HashMap::new();
    for (value, held) in &values[n] {
        subst.insert(*value, *held);
    }
    for at in 0..body.blocks.len() {
        if held.has(at) || blocks.iter().any(|turn| turn.values().any(|&copy| copy == at)) {
            continue;
        }
        // The phis as well: an edge into a block after the loop may carry
        // what the head worked out, and the block it comes along is not one
        // of the copies -- the copies were given their own values above.
        for phi in &mut body.blocks[at].phis {
            for (_, value) in &mut phi.edges {
                *value = settle(&subst, *value);
            }
        }
        for inst in &mut body.blocks[at].insts {
            for value in SIRBody::uses_mut(&mut inst.kind) {
                *value = settle(&subst, *value);
            }
        }
        match &mut body.blocks[at].term {
            SIRTerm::Branch { cond, .. } => *cond = settle(&subst, *cond),
            SIRTerm::Return(Some(value)) => *value = settle(&subst, *value),
            _ => {}
        }
    }
    repair(body);
}

// ---- Several turns at once -------------------------------------------------

// The same thing done to four neighbouring places, done once.
//
// This is superword-level parallelism, and it is here rather than a loop
// vectorizer because of the order the rewrites above happen in. `unroll` has
// already written a counted loop out as its turns, so what would have been a
// loop to widen is a straight run of instructions in one block, each doing to
// element `k + j` what the one before did to `k + j - 1`. Finding that is a
// matter of looking at a list, which is a much smaller thing than reasoning
// about a loop -- and everything the loop version would have had to prove has
// already been proved by the passes that got here.
//
// It starts at the writes and works upwards. A run of stores to consecutive
// elements of one thing is the seed: whatever they store is a group of four
// values that want to be one, and what made those is a group of instructions
// that want to be one instruction. Upwards from there until it reaches
// something it cannot group, and then that is packed as it stands.
//
// Four things have to hold, and three of them are answered by work already
// done:
//
//   - the elements have to be neighbours, which needs the numbers indexing
//     them to be literals -- which is what `unroll` leaves behind when it
//     writes out a walk over a range;
//   - the writes have to be able to happen together, which means nothing
//     between them may read or write where they do: `sir::alias`;
//   - nothing being grouped may trap or have an effect, because a vector
//     instruction is one instruction and cannot trap for the third lane only:
//     `effects`, the same answer `sweep` and `hoist` are held to;
//   - and the machine has to be able to do it: as many at once as fit in one
//     of its registers, and an instruction that exists over that many. That is
//     `sir::target`, which is a description of a machine rather than a guess
//     about one -- there is no integer divide over a vector on anything, so
//     four divisions stay four however neatly they line up.
//
// And then, having found a group it *may* make, it asks whether it should.
// Four instructions become one, which is a saving; four values that have to be
// put into a register one at a time are four instructions, which is not. See
// `pays`, where the two are counted against each other, and where an
// instruction something else still reads counts as no saving at all.
//
// Nothing is taken out. The scalar instructions are left where they are and
// `sweep` removes the ones nothing reads any more, which is what makes this
// safe to do to a group whose values are also read by something that was not
// part of it: that use still reads the scalar, and the scalar is still there.
const WIDE_DEEP: usize = 4;

// What a lane of a group is made of.
struct Group {
    ty:   TyId,
    // The values it stands for, one per lane. What the cost of leaving them
    // alone is worked out from.
    vals: Vec<SIRValueId>,
    plan: Plan,
}

enum Plan {
    // The same value in every lane.
    Splat(SIRValueId),
    // Neighbouring elements of one aggregate, read at once.
    Run { of: SIRValueId, at: u64 },
    // The same instruction in every lane, over groups.
    Same { kind: SIRInstKind, args: Vec<Group> },
    // And anything else: the values as they are, side by side.
    Gather(Vec<SIRValueId>),
}

fn vectorize(
    body: &mut SIRBody,
    ttir: &TTIRProgram,
    target: Target,
    stats: &mut Stats,
) -> bool {
    if target.bytes == 0 {
        return false;
    }
    let live = body.live();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        let alias = Alias::of(body);
        let held = made(body);
        let counted = counts(body);
        for run in runs(body, ttir, &alias, &held, target, at) {
            let vals: Vec<SIRValueId> = run
                .at
                .iter()
                .map(|&index| match body.blocks[at].insts[index].kind {
                    SIRInstKind::Store { value, .. } => value,
                    _ => unreachable!("a run is a run of stores"),
                })
                .collect();
            let group = grouped(body, ttir, &alias, &held, &vals, 0);
            if !target_does(ttir, target, &group, run.lanes) {
                continue;
            }
            if !pays(target, &counted, &group, run.lanes) {
                continue;
            }
            // One at a time: widening a run rewrites the block's list, and the
            // next is looked for in what that left.
            widen(body, at, &run, &group, stats);
            return true;
        }
    }
    false
}

// Where each of a run's stores stands, in the order they were written.
struct Run {
    // The instruction each store is, by its place in the block.
    at:    Vec<usize>,
    // And the address each writes to, in the same order.
    addrs: Vec<SIRValueId>,
    // How many of them there are, which is what the target said fits.
    lanes: usize,
}

// Every run of stores in the block that writes neighbouring elements of one
// thing, as many of them at a time as the machine holds, with nothing between
// them that may read or write where they do.
fn runs(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    held: &[Option<SIRInstKind>],
    target: Target,
    at: SIRBlockId,
) -> Vec<Run> {
    // Every store in the block that writes an element whose number is known.
    let mut writes: Vec<(usize, SIRValueId, i64, SIRValueId, SIRValueId)> = Vec::new();
    for (index, inst) in body.blocks[at].insts.iter().enumerate() {
        let SIRInstKind::Store { to, value } = inst.kind else { continue };
        let Some(Some(SIRInstKind::IndexAddr { base, index: which })) = held.get(to) else {
            continue;
        };
        let Some(TIRLit::Int(n)) = lit_of(held, *which) else { continue };
        writes.push((index, *base, *n, to, value));
    }

    let mut out = Vec::new();
    for start in 0..writes.len() {
        // How many fit is a question about what is being written, so it is
        // asked of the first of them and the rest are held to that.
        let Some(width) = target::size(ttir, body.values[writes[start].4].ty) else { continue };
        // As many as the register holds, and then half as many, and so on
        // down to two. A register filled halfway is still a register: what a
        // machine holds is a ceiling and not a quota, and refusing to write
        // four of something out on a machine that could have held eight would
        // leave every short array alone on the widest machines.
        let mut lanes = target.lanes(width);
        while lanes >= 2 {
            if start + lanes <= writes.len() {
                let group = &writes[start..start + lanes];
                let neighbours = (1..lanes).all(|j| {
                    group[j].2 == group[0].2 + j as i64 && alias.must(group[j].1, group[0].1)
                });
                let addrs: Vec<SIRValueId> = group.iter().map(|w| w.3).collect();
                let places: Vec<usize> = group.iter().map(|w| w.0).collect();
                if neighbours && settled(body, ttir, alias, at, &places, &addrs) {
                    out.push(Run { at: places, addrs, lanes });
                    break;
                }
            }
            lanes /= 2;
        }
    }
    out
}

// Whether the machine has an instruction for every step of the plan.
//
// Without this a group of four field reads would be written out as a "wide
// field read", which is not a thing: `grouped` will happily find that four
// instructions are the same instruction, and being the same is not the same as
// being one the machine can do at once.
fn target_does(ttir: &TTIRProgram, target: Target, group: &Group, lanes: usize) -> bool {
    let Some(p) = target::prim(ttir, group.ty) else { return false };
    if target::size_of(p).is_none() {
        return false;
    }
    match &group.plan {
        // Moving values about, which every machine with vectors can do.
        Plan::Splat(_) | Plan::Gather(_) | Plan::Run { .. } => true,
        Plan::Same { kind, args } => {
            target.does(kind, p, lanes)
                && args.iter().all(|arg| target_does(ttir, target, arg, lanes))
        }
    }
}

// Whether the wide instructions cost less than the narrow ones they stand for.
//
// The narrow side counts only what would actually go. An instruction whose
// value something outside the group also reads is an instruction that stays
// where it is however the group is written, so counting it as saved would be
// counting a saving that does not happen -- which is the way a cost model
// talks itself into a rewrite that makes things worse.
//
// The wide side counts what has to be built. A group whose operands were
// already lined up -- neighbouring elements, or one value in every lane --
// costs one instruction to read; a group whose operands have to be fetched one
// at a time costs an insert each, and that is usually the whole difference
// between a group worth making and one that is not.
fn pays(target: Target, counted: &[usize], group: &Group, lanes: usize) -> bool {
    // The stores themselves: `lanes` of them become one.
    let (narrow, wide) = costs(target, counted, group, lanes);
    narrow + lanes > wide + 1
}

fn costs(target: Target, counted: &[usize], group: &Group, lanes: usize) -> (usize, usize) {
    // How many of the lanes are read by nothing but this group, and so go.
    let goes = || group.vals.iter().filter(|&&v| counted.get(v) == Some(&1)).count();
    match &group.plan {
        // Already worked out, and staying: nothing is saved, and putting them
        // side by side costs an insert each.
        Plan::Gather(_) => (0, lanes * target.insert),
        // One value in every lane is one broadcast.
        Plan::Splat(_) => (0, 1),
        Plan::Run { .. } => (goes(), 1),
        Plan::Same { kind, args } => {
            let mut narrow = goes();
            let mut wide = target.cost(kind);
            for arg in args {
                let (n, w) = costs(target, counted, arg, lanes);
                narrow += n;
                wide += w;
            }
            (narrow, wide)
        }
    }
}

// How many times each value is read, which is what says whether taking one
// instruction out would take it out.
fn counts(body: &SIRBody) -> Vec<usize> {
    let mut out = vec![0; body.values.len()];
    let count = |value: SIRValueId, out: &mut Vec<usize>| {
        if value < out.len() {
            out[value] += 1;
        }
    };
    for block in &body.blocks {
        for phi in &block.phis {
            for (_, value) in &phi.edges {
                count(*value, &mut out);
            }
        }
        for inst in &block.insts {
            for value in SIRBody::uses(&inst.kind) {
                count(value, &mut out);
            }
        }
        match &block.term {
            SIRTerm::Branch { cond, .. } => count(*cond, &mut out),
            SIRTerm::Return(Some(value)) => count(*value, &mut out),
            _ => {}
        }
    }
    out
}

// Whether the stores may be brought together at the last of them: nothing
// standing between may read or write where any of them writes.
fn settled(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    at: SIRBlockId,
    places: &[usize],
    addrs: &[SIRValueId],
) -> bool {
    let held = made(body);
    let first = places[0];
    let last = places[places.len() - 1];
    for index in first..=last {
        if places.contains(&index) {
            continue;
        }
        let kind = &body.blocks[at].insts[index].kind;
        let touches = match kind {
            SIRInstKind::Load { from } => addrs.iter().any(|&a| alias.may(a, *from)),
            SIRInstKind::Store { to, .. } | SIRInstKind::VecStore { to, .. } => {
                addrs.iter().any(|&a| alias.may(a, *to))
            }
            SIRInstKind::DropSlot(slot) => addrs
                .iter()
                .any(|&a| alias.place(a).map(|p| p.base) == Some(Base::Slot(*slot))),
            SIRInstKind::Call { .. } | SIRInstKind::Method { .. } | SIRInstKind::Drop(_) => {
                !addrs.iter().all(|&a| alias.own(a))
            }
            // Anything else works a value out, and a value is not somewhere
            // anything can have been written.
            other => effects(&body.values, ttir, &held, other),
        };
        if touches {
            return false;
        }
    }
    true
}

// What the lanes of a group are, worked out from the values that fill them.
fn grouped(
    body: &SIRBody,
    ttir: &TTIRProgram,
    alias: &Alias,
    held: &[Option<SIRInstKind>],
    vals: &[SIRValueId],
    depth: usize,
) -> Group {
    let ty = body.values[vals[0]].ty;
    let gather = || Group { ty, vals: vals.to_vec(), plan: Plan::Gather(vals.to_vec()) };

    // The same value in every lane, which is how a thing that does not vary
    // with the turn joins a group of things that do.
    if vals.iter().all(|&v| v == vals[0]) {
        return Group { ty, vals: vals.to_vec(), plan: Plan::Splat(vals[0]) };
    }
    if depth >= WIDE_DEEP {
        return gather();
    }

    // Neighbouring elements of one aggregate.
    let elems: Option<Vec<(SIRValueId, i64)>> = vals
        .iter()
        .map(|&v| match held.get(v) {
            Some(Some(kind @ SIRInstKind::Index { base, index })) => {
                match (lit_of(held, *index), effects(&body.values, ttir, held, kind)) {
                    (Some(TIRLit::Int(n)), false) => Some((*base, *n)),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect();
    if let Some(elems) = elems {
        let run = (1..elems.len()).all(|j| {
            elems[j].1 == elems[0].1 + j as i64 && alias.must(elems[j].0, elems[0].0)
        });
        if run {
            if let Ok(first) = u64::try_from(elems[0].1) {
                return Group {
                    ty,
                    vals: vals.to_vec(),
                    plan: Plan::Run { of: elems[0].0, at: first },
                };
            }
        }
    }

    // Or the same instruction in every lane. `shape` is what "the same" means:
    // the instruction with its operands blanked, so that two adds are one
    // shape and an add and a subtract are two.
    let kinds: Option<Vec<SIRInstKind>> = vals
        .iter()
        .map(|&v| match held.get(v) {
            Some(Some(kind)) if !effects(&body.values, ttir, held, kind) => Some(kind.clone()),
            _ => None,
        })
        .collect();
    let Some(kinds) = kinds else { return gather() };
    let first = shape(&kinds[0]);
    if !kinds.iter().all(|kind| shape(kind) == first) {
        return gather();
    }
    let width = SIRBody::uses(&kinds[0]).len();
    // Nothing to group under it, and nothing above it either: an instruction
    // with no operands is the same instruction in every lane only if it is
    // literally the same value, which the splat above has already answered.
    if width == 0 {
        return gather();
    }
    let mut args = Vec::new();
    for arg in 0..width {
        let lane: Vec<SIRValueId> = kinds.iter().map(|kind| SIRBody::uses(kind)[arg]).collect();
        args.push(grouped(body, ttir, alias, held, &lane, depth + 1));
    }
    Group { ty, vals: vals.to_vec(), plan: Plan::Same { kind: kinds[0].clone(), args } }
}

// An instruction with its operands blanked, which is what makes two of them
// the same instruction for this purpose.
fn shape(kind: &SIRInstKind) -> SIRInstKind {
    let mut out = kind.clone();
    for value in SIRBody::uses_mut(&mut out) {
        *value = 0;
    }
    out
}

// The group written out, and the run of stores replaced by the one that writes
// all of it.
fn widen(body: &mut SIRBody, at: SIRBlockId, run: &Run, group: &Group, stats: &mut Stats) {
    let last = run.at[run.at.len() - 1];
    let (line, col) = (body.blocks[at].insts[last].line, body.blocks[at].insts[last].col);
    let mut out = Vec::new();
    let value = write(body, group, run.lanes, line, col, &mut out);
    stats.widened += 1;

    // The scalar stores go and the vector one stands where the last of them
    // did -- which is below every value any of them wrote, so nothing it reads
    // is read above where it is made.
    let mut insts = Vec::with_capacity(body.blocks[at].insts.len() + out.len());
    for (index, inst) in body.blocks[at].insts.iter().enumerate() {
        if index == last {
            insts.append(&mut out);
            insts.push(SIRInst {
                def:       None,
                kind:      SIRInstKind::VecStore { to: run.addrs[0], value },
                is_unsafe: inst.is_unsafe,
                line,
                col,
            });
        } else if !run.at.contains(&index) {
            insts.push(inst.clone());
        }
    }
    body.blocks[at].insts = insts;
}

// One group written out, operands first, and the value it comes to.
fn write(
    body: &mut SIRBody,
    group: &Group,
    lanes: usize,
    line: usize,
    col: usize,
    out: &mut Vec<SIRInst>,
) -> SIRValueId {
    let kind = match &group.plan {
        Plan::Splat(value) => SIRInstKind::Pack(vec![*value; lanes]),
        Plan::Gather(values) => SIRInstKind::Pack(values.clone()),
        Plan::Run { of, at } => SIRInstKind::Lanes { of: *of, at: *at, lanes },
        Plan::Same { kind, args } => {
            let held: Vec<SIRValueId> =
                args.iter().map(|arg| write(body, arg, lanes, line, col, out)).collect();
            let mut kind = kind.clone();
            for (slot, value) in SIRBody::uses_mut(&mut kind).into_iter().zip(held) {
                *slot = value;
            }
            kind
        }
    };
    body.values.push(SIRValue { ty: group.ty, lanes, of: None, line, col });
    let def = body.values.len() - 1;
    out.push(SIRInst { def: Some(def), kind, is_unsafe: false, line, col });
    def
}

// ---- Writing a call out ---------------------------------------------------

// Which body each declaration is, and which bodies each body can reach. The
// first is what a call has to be looked up in -- a `Call` names a value, the
// value is an `Item`, and the item is where the body is written -- and the
// second is what says whether writing one out would ever stop.
struct Calls {
    // By item, the body it is the body of. Only the fns that have one and take
    // no generic parameters: a generic body is one body for every type it is
    // called at, and nothing has monomorphised it, so the body written out
    // would be the wrong one for all but one caller.
    of:    HashMap<TTIRItemId, (SIRBodyId, TIRInline)>,
    // By body, the bodies it can reach through a call or a closure. Reachable
    // and not just called: a body that makes a closure may call it, and
    // whether it does is not a question this has to answer to be safe.
    reach: Vec<Vec<SIRBodyId>>,
}

impl Calls {
    fn of(program: &SIRProgram, ttir: &TTIRProgram) -> Calls {
        let mut of = HashMap::new();
        for (id, item) in ttir.items.iter().enumerate() {
            let TTIRItemKind::Fn(f) = &item.kind else { continue };
            let Some(body) = f.body else { continue };
            if !f.generics.is_empty() || body >= program.bodies.len() {
                continue;
            }
            of.insert(id, (body, f.attrs.inline));
        }

        // One step first, then closed over: reaching is the transitive
        // closure, and a body that can reach the body it stands in is one
        // nothing may be written into.
        let mut reach: Vec<Vec<SIRBodyId>> = vec![Vec::new(); program.bodies.len()];
        for (id, body) in program.bodies.iter().enumerate() {
            for block in &body.blocks {
                for inst in &block.insts {
                    let to = match &inst.kind {
                        SIRInstKind::Item(item) => of.get(item).map(|(body, _)| *body),
                        SIRInstKind::Closure { body, .. } => Some(*body),
                        _ => None,
                    };
                    if let Some(to) = to {
                        if to < reach.len() && !reach[id].contains(&to) {
                            reach[id].push(to);
                        }
                    }
                }
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            for id in 0..reach.len() {
                let held = reach[id].clone();
                for to in held {
                    for &far in &reach[to].clone() {
                        if !reach[id].contains(&far) {
                            reach[id].push(far);
                            changed = true;
                        }
                    }
                }
            }
        }
        Calls { of, reach }
    }

    // Whether writing this callee into this caller is a rewrite there would
    // be no end to. Three ways, and the third is the one that is easy to miss:
    // a body written into itself, a body that can reach the one it would be
    // written into -- and a body that can reach *itself*, which is bounded
    // only by how many times this pass is willing to go round, and is a loop
    // unrolled by accident rather than a call written out.
    fn cycles(&self, callee: SIRBodyId, caller: SIRBodyId) -> bool {
        callee == caller
            || self.reach[callee].contains(&caller)
            || self.reach[callee].contains(&callee)
    }
}

// Where one call stands and what it was handed.
struct Site {
    at:     SIRBlockId,
    index:  usize,
    callee: SIRBodyId,
    args:   Vec<SIRValueId>,
    def:    Option<SIRValueId>,
}

fn inline(program: &mut SIRProgram, graph: &Calls, level: Level, stats: &mut Stats) -> bool {
    let mut changed = false;
    for caller in 0..program.bodies.len() {
        for _ in 0..level.inline_each() {
            let Some(site) = pick(program, graph, caller, level) else { break };
            let callee = program.bodies[site.callee].clone();
            written_out(&mut program.bodies[caller], &callee, &site);
            stats.inlined += 1;
            changed = true;
        }
    }
    changed
}

// The first call in the body worth writing out. First and not best: the ones
// refused are refused on a rule, and among the rest one call is much like
// another at this size.
fn pick(program: &SIRProgram, graph: &Calls, caller: SIRBodyId, level: Level) -> Option<Site> {
    let body = &program.bodies[caller];
    let held = made(body);
    let live = body.live();
    for at in 0..body.blocks.len() {
        if !live[at] {
            continue;
        }
        for (index, inst) in body.blocks[at].insts.iter().enumerate() {
            let SIRInstKind::Call { callee, args } = &inst.kind else { continue };
            let Some(Some(SIRInstKind::Item(item))) = held.get(*callee) else { continue };
            let Some(&(callee, asked)) = graph.of.get(item) else { continue };
            // `%noinline` is a promise and not a preference (§1): whatever
            // this pass would have made of the size, it has been answered.
            if asked == TIRInline::Never || graph.cycles(callee, caller) {
                continue;
            }
            if !worth(&program.bodies[callee], inst, args, asked, level) {
                continue;
            }
            return Some(Site {
                at,
                index,
                callee,
                args: args.clone(),
                def: inst.def,
            });
        }
    }
    None
}

// Whether this body may stand where this call did.
fn worth(
    callee: &SIRBody,
    call: &SIRInst,
    args: &[SIRValueId],
    asked: TIRInline,
    level: Level,
) -> bool {
    if callee.params.len() != args.len() {
        return false;
    }
    let live = callee.live();
    let mut size = 0;
    for (at, block) in callee.blocks.iter().enumerate() {
        if !live[at] {
            continue;
        }
        size += block.insts.len();
        for inst in &block.insts {
            // A receiver is a value the caller has not got. A method is
            // called through `Method` rather than `Call` and so is not
            // reached here at all, but a fn body that names `self` would
            // be one written out with nothing to put in its place.
            if matches!(inst.kind, SIRInstKind::SelfValue | SIRInstKind::SelfAddr) {
                return false;
            }
        }
        // What the call makes has to come from somewhere on every path that
        // gets back, so a body that returns without a value cannot stand where
        // a call that makes one did.
        if call.def.is_some() && matches!(block.term, SIRTerm::Return(None)) {
            return false;
        }
    }
    // The size is this pass's guess at what a call is worth, and `%inline` is
    // the source saying it has a better one. Everything above this line is a
    // rule about whether the rewrite is *sound*, and a hint waives none of it.
    asked == TIRInline::Always || size <= level.inline_max()
}

// The callee written into the caller at the call.
//
// Four things move, and the ids of all four are the caller's now: the values,
// the slots, the blocks, and the edges between them. The parameters are the
// exception -- they are made by no instruction, being what the caller handed
// over, so they are not copied at all and every read of one reads the argument
// instead.
//
// The call's own block is cut in two at the call. What stood above it stays;
// what stood below it, and the terminator, become a block the callee's returns
// go to. That block is where the call's value is made, by a phi over the
// blocks that returned one -- which is the one place the value can be made,
// there being as many answers as there are ways back.
fn written_out(caller: &mut SIRBody, callee: &SIRBody, site: &Site) {
    let vbase = caller.values.len();
    let sbase = caller.slots.len();
    let bbase = caller.blocks.len();
    let back = bbase + callee.blocks.len();

    caller.values.extend(callee.values.iter().cloned());
    caller.slots.extend(callee.slots.iter().cloned());

    // A parameter is the argument; everything else is itself, one arena
    // further along.
    let value = |v: SIRValueId| match callee.params.iter().position(|&p| p == v) {
        Some(index) => site.args[index],
        None => v + vbase,
    };

    let live = callee.live();
    let mut edges: Vec<(SIRBlockId, SIRValueId)> = Vec::new();
    for (at, block) in callee.blocks.iter().enumerate() {
        let mut moved = block.clone();
        for phi in &mut moved.phis {
            phi.def += vbase;
            for (from, held) in &mut phi.edges {
                *from += bbase;
                *held = value(*held);
            }
        }
        for inst in &mut moved.insts {
            if let Some(def) = &mut inst.def {
                *def += vbase;
            }
            for held in SIRBody::uses_mut(&mut inst.kind) {
                *held = value(*held);
            }
            match &mut inst.kind {
                SIRInstKind::Addr(slot) | SIRInstKind::DropSlot(slot) => *slot += sbase,
                _ => {}
            }
        }
        match &mut moved.term {
            SIRTerm::Return(held) => {
                if live[at] {
                    if let Some(held) = held {
                        edges.push((at + bbase, value(*held)));
                    }
                }
                moved.term = SIRTerm::Goto(back);
            }
            term => {
                for to in term.targets_mut() {
                    *to += bbase;
                }
                if let SIRTerm::Branch { cond, .. } = term {
                    *cond = value(*cond);
                }
            }
        }
        caller.blocks.push(moved);
    }

    // The call's block, cut. The call itself goes: what it made is made by the
    // phi below instead.
    let tail = caller.blocks[site.at].insts.split_off(site.index + 1);
    caller.blocks[site.at].insts.pop();
    let term = std::mem::replace(
        &mut caller.blocks[site.at].term,
        SIRTerm::Goto(bbase + callee.entry),
    );
    let (line, col) = (caller.blocks[site.at].line, caller.blocks[site.at].col);

    // And whoever heard from that block hears from the block below the call.
    for to in term.targets() {
        for phi in &mut caller.blocks[to].phis {
            for (from, _) in &mut phi.edges {
                if *from == site.at {
                    *from = back;
                }
            }
        }
    }

    let mut phis = Vec::new();
    if let Some(def) = site.def {
        if !edges.is_empty() {
            phis.push(SIRPhi { def, edges });
        }
    }
    caller.blocks.push(SIRBlock { phis, insts: tail, term, line, col });
}

// ---- What is left after the widening --------------------------------------
//
// `vectorize` above is the SLP pass. It finds the same instruction applied to
// neighbouring places, asks `sir::target` whether the machine can do that to
// several at once and how many, weighs the instructions it would save against
// the ones it would have to add, and writes it once over the lot if that comes
// out ahead. Which is the whole of the shape a vectorizer has; what is left is
// how much it knows.
//
// The target descriptions are coarse, and deliberately so: a register width, a
// flag for the multiply that arrived late, a flag for shifts that differ by
// lane, and what an insert costs. Every one of those is a claim about hardware
// that can be checked and changed. What is *not* there is anything about how
// long an instruction takes, how many may go at once, or what a load costs
// when it misses -- and none of that can be added honestly until something
// measures a machine, which needs a back end to measure.
//
// So the costs are counted in instructions, and one instruction is one unit.
// That is right about the thing that matters most here -- a vector add does
// four adds and costs one -- and silent about everything else. A group that
// this makes is a group that is nearly certainly worth making; a group it
// turns down on cost is one it is only fairly sure about.
//
// What would sharpen it, in the order the work would be done:
//
//   - a back end, which is what makes a cost a measurement rather than a
//     claim, and what would let `Target` carry a number per instruction
//     instead of one number for all of them;
//   - seeds other than stores. A run of writes is the clearest group there is
//     and it is not the only one: a reduction -- four adds into one running
//     total -- is the other shape loops are full of, and it needs the adds
//     reassociated before they can be grouped, which is a rewrite this file
//     does not have;
//   - `Lanes` over memory. A run read out of an aggregate *value* is what this
//     emits, because that is what the lowering leaves; a run read straight out
//     of memory would need the load and the extraction to be one instruction,
//     which is a change to what `sir::lower` builds rather than to what is
//     made of it;
//   - and a group that is wider than the register, written out as two. What
//     falls back to a narrower group now could as well go the other way.

#[cfg(test)]
mod tests;
