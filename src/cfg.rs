// The CFG -- the control flow graph: a function's body with its control flow
// drawn as edges rather than nesting.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR
//                                                       |
//                                                    [ sema ]        not written
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
// Nothing runs any of this yet. `sema` is what would hand `lower` a TTIR, and
// it is not written -- so the driver stops at the TIR, and what is here is
// reached only by tests that build a TTIR by hand (`fixture.rs`). Until one
// exists most of this is constructed and never called, and the warning about it
// would be on every build rather than about anything.
#![allow(dead_code)]

#[cfg(test)]
pub mod fixture;
pub mod lower;
pub mod opt;
pub mod source_map;
pub mod cfg_nodes;
