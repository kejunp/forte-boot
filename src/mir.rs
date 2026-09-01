// The MIR -- the machine IR: the program as things a machine does, in two
// shapes.
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
//                                                            SIR -> opt -> lower
//                                                                            |
//                                                                           MIR
//
// The SIR named every value once and stopped there. What it names them with is
// still the language's: a `Map`, a `Set`, a closure, the cursor a `for` walks,
// the release at the end of a scope. Not one of those is a thing a machine
// does, and the reason they survived that far is that no pass before this one
// had to say what they cost or where they sit. This one does, and saying so is
// most of what it is.
//
// Two shapes rather than one, and the split is where a question stops being
// about the program and starts being about the machine running it.
//
//   the graph   the same blocks and edges the SIR had, with the instructions
//               chosen and every address worked out. A field is a number of
//               bytes from a base here, not a name; a release is a call.
//               Values are still as many as the body wants.
//   the linear  the edges become an order, the phis become moves, and the
//               registers become the ones a machine actually has -- which is
//               the first point in this compiler where there are not enough of
//               something. Then it is written out as text.
//
// Neither shape is a real instruction set. What is emitted is a listing: the
// MIR made readable, in the order it would run, with the registers it would
// use. That is short of an assembler and well past a graph, and it is the
// thing the choice of a machine can be checked against by reading.
//
// The parts, as far as they go: what a machine is, and what a type takes on
// one. The graph itself and the passes over it come after.
//
//   `machine`    what the machine is: how wide a pointer is, which registers
//                there are, and which of them a call may keep.
//   `layout`     what a type takes and where each of its parts sits -- the
//                question `sir::target` says out loud that nothing had
//                answered.
//
// What consumes a MIR is the listing, and after that nothing does: there is no
// assembler and no object file. So parts of this are built for a reader rather
// than for a pass, and the warning about that would be on every build rather
// than about anything.
//
// The calls it emits do have somewhere to land. `runtime/` is the other member
// of this workspace and defines every `__rt_` symbol named here -- a heap, a
// collector, a map and a set. What is still missing between the two is the
// assembler: the contract is checked at both ends and nothing puts them
// together.
#![allow(dead_code)]

pub mod layout;
pub mod machine;
