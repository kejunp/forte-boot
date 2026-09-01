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
// The parts. The first four are what the graph is and what it needs to be
// built; the last three are the second shape.
//
//   `machine`    what the machine is: how wide a pointer is, which registers
//                there are, and which of them a call may keep.
//   `layout`     what a type takes and where each of its parts sits -- the
//                question `sir::target` says out loud that nothing had
//                answered.
//   `mono`       a generic made once for each set of types it is used with,
//                which is what leaves no `T` for `layout` to fail on.
//   `runtime`    the symbols the lowering calls for the things the language
//                has and a machine does not.
//   `shape`      what a type is, written down for the runtime to read: which
//                of its words are pointers, which is the one thing a collector
//                cannot work out for itself.
//   `mir_nodes`  what the graph is made of.
//   `lower`      the SIR turned into it: every type a number, every value in a
//                register or in the frame, every release a call -- and a body
//                for each of those releases, which is the one thing here that
//                emits code no source wrote.
//   `verify`     the rules that make it a graph worth reading, checked rather
//                than assumed.
//
//   `linear`     the edges made into an order and the phis into moves.
//   `regalloc`   the registers a body wanted met with the ones there are.
//   `text`       the listing, for a person to read.
//   `asm`        the same decisions for an assembler: x86-64, aarch64 and
//                riscv64, with the prologue, the epilogue and the calling
//                convention that everything above here left for it.
//
// Two things consume a MIR, and they are the same decisions written for two
// readers. `text` is the listing, which is for a person; `asm` is assembly for
// one of three machines, which is for an assembler. A program that comes out
// of the second can be assembled, linked against `runtime/`, and run.
//
// Parts of this are still built for a reader rather than for a pass, and the
// warning about that would be on every build rather than about anything.
//
// The calls it emits do have somewhere to land. `runtime/` is the other member
// of this workspace and defines every `__rt_` symbol named here -- a heap, a
// collector, a map and a set. What is still missing between the two is the
// assembler: the contract is checked at both ends and nothing puts them
// together.
#![allow(dead_code)]

#[cfg(test)]
pub mod fixture;

pub mod asm;
pub mod layout;
pub mod linear;
pub mod lower;
pub mod machine;
pub mod mir_nodes;
pub mod mono;
pub mod regalloc;
pub mod runtime;
pub mod shape;
pub mod text;
pub mod verify;
