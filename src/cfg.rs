// The CFG -- the control flow graph: a function's body with its control flow
// drawn as edges rather than nesting.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR
//                                                       |
//                                                    [ sema ]
//                                                       |
//                                                      TTIR
//                                                       |
//                                                     lower -> CFG -> opt
//
// It is built from the TTIR and not from the TIR, so everything it holds is
// already typed and already resolved. That ordering is the usual one and it is
// the usual reason: name resolution and inference want a tree, and a graph is
// what you build once they are done -- which is why this sits after `sema` and
// not before it.
//
// What lowering adds is the one thing the TTIR still had: `if`, `while`, `for`,
// `match`, the jumps and the two short-circuiting operators stop being
// expressions and become edges. `a && b` is the two branches it always meant.
// An expression that had a value *and* branched gets a slot to put the answer
// in, written on both sides.
//
// And where every release goes, which is what `drops` places: "a local at the
// end of its block, a temporary at the end of its statement ... and nothing at
// all where the value was moved away first" (§2). The first two are where the
// lowering puts the statement; the third is a dataflow, which is what a graph
// is for.
//
// Parts of this are constructed and never called -- a graph has no consumer
// past `opt` yet -- and the warning about that would be on every build rather
// than about anything.
#![allow(dead_code)]

#[cfg(test)]
pub mod fixture;
pub mod drops;
pub mod lower;
pub mod opt;
pub mod source_map;
pub mod cfg_nodes;
