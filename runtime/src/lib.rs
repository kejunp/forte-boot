// The runtime: the things a compiled program needs that a machine does not
// provide and the language cannot write for itself.
//
//     SIR -> mono -> lower -> MIR -> linear -> regalloc -> text
//                                                           |
//                                                        __rt_*
//                                                           |
//                                                       [ this ]
//
// `mir::runtime` names a set of symbols and says plainly that nothing defines
// them. This defines them. There are three groups and they are three different
// kinds of thing:
//
//   the heap       room that outlives the frame that asked for it, and a
//                  collector that works out when it stops being wanted.
//   the containers a map and a set, ordered and hashed. Section 8 says these
//                  are "syntax for a type a library declares", and no library
//                  exists to declare them -- so they are here, standing in for
//                  one, and the day a library can be written they should move.
//   the glue       the entry points themselves, in `abi`.
//
// Built from the bottom up. What is here so far is the heap: pages cut into
// size-classed spans, with the bits that say what is going on in each. The
// collector over it and the containers beside it come after.

pub mod heap;
pub mod mem;
pub mod shape;
