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
// One file each, and this one holds only what they have in common: what a
// level means, what the pass did, and the loop that runs them until nothing
// changes.
//
//   `facts`   the questions all of them ask -- what made a value, whether an
//             instruction has effects, whether two of it make one value, and
//             whether one value may be named twice. Written once because
//             three rewrites answering `effects` three ways would be three
//             answers, and the wrong one would be wrong quietly.
//   `fold`    operators over what is already worked out.
//   `share`   two values that turn out to be one: phis and repeated work.
//   `memory`  what a store put there, and stores nothing will read.
//   `graph`   edges, blocks, and everything nothing runs.
//   `hoist`   what does not vary with the turn, moved out of the loop.
//   `unroll`  a loop whose turns are counted, written out as the turns.
//   `wide`    the same thing done to neighbouring places, done at once.
//   `inline`  a call written out where it was called.
//
// The order above is the order they are declared in below and not the order
// they run in, which is `clean`'s: reading a pass and running a pass want
// different orders, and only one of them can be the file listing.
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


use crate::tir::ttir_nodes::TTIRProgram;

use super::promote::promote;
use super::sir_nodes::*;
use super::target::Target;

mod facts;
mod fold;
mod graph;
mod hoist;
mod inline;
mod memory;
mod share;
mod unroll;
mod wide;

use fold::fold;
use graph::{branches, merge, sweep};
use hoist::hoist;
use inline::{inline, Calls};
use memory::{forward, overwritten};
use share::{phis, share};
use unroll::unroll;
use wide::vectorize;

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
