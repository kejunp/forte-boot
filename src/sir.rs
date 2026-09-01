// The SIR -- the SSA IR: the graph with every value named once.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR
//                                                       |
//                                                    [ sema ]
//                                                       |
//                                                      TTIR
//                                                       |
//                                                     lower -> GIR -> opt
//                                                                      |
//                                                                    lower
//                                                                      |
//                                                                     SIR
//                                                                      |
//                                                                    lower
//                                                                      |
//                                                                     MIR
//
// The GIR drew the control flow as edges and stopped there. A name in it is
// still a name -- written as many times as the source writes it -- and an
// expression is still a tree. Both are shapes that make a later pass ask
// something it should not have to: "what does this name hold here" is a walk
// back through the graph, and it is a walk that has to be redone for every
// question anyone asks.
//
// Naming each value where it is made answers all of them at once. `x` written
// twice is two values, so what a read of `x` holds is the one instruction that
// made it, and the walk is a lookup. Where two paths meet and there is no one
// instruction, a phi says which value came along which edge -- which is the
// only thing SSA adds to the graph, and the reason it needs a graph to be
// added to.
//
// Four passes, in this order:
//
//   `lower`    the GIR's trees flattened, its `Match` turned into tests and
//              its `for` into a cursor and a loop, and every local put in a
//              slot of the frame.
//   `promote`  the slots taken back out again, wherever the address of one
//              never goes anywhere but a load or a store, with the phis that
//              takes.
//   `opt`      what the program does not have to do, taken out of it: calls
//              written where they were called, loops written out as the turns
//              they run, operators over values already worked out, everything
//              nothing reads -- and, at the top level, the turns of a loop run
//              several at a time. How much of that happens is a `Level`, and
//              `Level::None` is none of it.
//   `verify`   the two rules that make it SSA, checked rather than assumed.
//
// `opt` is the one that needs all three of the others. It can only be written
// against SSA -- "what does this operand hold" is a lookup and not a walk --
// and it is the pass most able to break it silently, which is what `verify` is
// run over every body it touches for.
//
// Three of these are analyses rather than passes, and are what the rewrites
// are written against. `dom` is what `promote` places phis by: dominance is
// what "this value is usable here" means, and every rewrite over the graph has
// to ask it. `loops` is the next thing it answers -- a back edge is an edge to
// a block that dominates it. And `alias` is the one about memory: whether two
// addresses may be the same address, which is the question a load, a store and
// a loop that holds either all turn on.
//
// `mir` is what consumes a SIR, and it is the first thing in this compiler
// that is about a machine rather than about the program. Parts of what is built
// here are still built for a pass that has not reached them, and the warning
// about that would be on every build rather than about anything.
#![allow(dead_code)]

#[cfg(test)]
pub mod fixture;

pub mod alias;
pub mod dom;
pub mod loops;
pub mod lower;
pub mod opt;
pub mod promote;
pub mod sir_nodes;
pub mod target;
pub mod verify;
