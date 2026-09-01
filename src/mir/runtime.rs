// The symbols the lowering calls, for the things the language has and a
// machine does not.
//
// A machine has no map. It has no set, no collector, no notion that a value
// goes out of scope and something has to happen. The SIR has all four, because
// every pass before this one could carry them without saying what they cost.
// This is where they stop being carried: each becomes a call, and a call is
// something a machine does.
//
// What is on the other end is `runtime/`, the second member of this workspace
// -- a heap of size-classed spans, a concurrent mark-and-sweep collector shaped
// after Go's, and a map and a set standing in for the library §8 says should
// one day declare them. So a listing that mentions `__rt_map_new` names
// something that exists, which was not true when this file was written.
//
// What is still not true is that the two can be put together: there is no
// assembler and no object file, so nothing links a compiled program to that
// library. What these calls are checked against is the contract, at both ends,
// and not a program that runs.
//
// The names are deliberately in one file. A name spelled in the lowering would
// be a name spelled in five files, and the first time one of them differed by a
// letter it would be a link error about a function nobody can find.
//
// **Three of these take a type descriptor**, which `mir::shape` emits into the
// constant pool and the runtime reads. That is the answer to the question this
// file used to leave open: `__rt_map_insert` is one symbol for every `K` in the
// program and the register it is handed says nothing about what is in it, so
// something has to. A descriptor is that something, and it does for the
// collector what it does for the map -- it says which words of a value are
// addresses, which is the one thing a collector cannot work out for itself.
//
// Two shapes of name are here. The fixed ones below are one routine each,
// whatever the types. A release is not one of those: what has to happen when a
// value goes out of scope is a question about *that type*, so it is one routine
// per type, named the way everything else is named -- which is what `glue` is.

use crate::sema::names::part;

// ---- Starting up -----------------------------------------------------------

// `__rt_init()` -- called once, from the outermost frame of the program.
//
// It records where the stack begins, which is the one thing the collector
// cannot work out for itself: the address of a local says where the stack is
// now, and what has to be scanned is everything above that. A program that
// never calls it never collects.
//
// **Nothing emits this yet**, because nothing emits an entry point: there is no
// `main` in the MIR and no object file for one to be in. It is named here
// because the day something does emit one, this is the first call it makes.
pub const INIT: &str = "__rt_init";

// ---- Getting room ----------------------------------------------------------

// `__rt_alloc(bytes): ptr` -- room that outlives the frame and that the
// collector does not own. Nothing frees it.
//
// The lowering emits none of these. It is here because the runtime's own map
// and set use it for the storage a program never sees, and because a caller
// that means "this is not the collector's" should have a way to say so rather
// than a shape with nothing in it -- an object with no pointers is still
// collected, and this is not.
pub const ALLOC: &str = "__rt_alloc";

// `__rt_gc_alloc(bytes, shape): ptr` -- room the collector does own.
//
// The shape says which words of the new object hold addresses, and an object
// whose shape names none goes in a span the marker never reads. Passing
// nothing is allowed and means the same as naming none.
pub const GC_ALLOC: &str = "__rt_gc_alloc";

// `__rt_collect()` -- a whole cycle, now, on the calling thread.
pub const COLLECT: &str = "__rt_collect";

// ---- Writing a pointer -----------------------------------------------------

// `__rt_write(slot, value)` -- a pointer going into a place that is not a frame
// slot.
//
// The marker walks the heap as it stood when the cycle began while the program
// carries on writing to it, and between them they can hide an object. This is
// what stops that: it shades what is being overwritten and what is being
// written, and then stores. Between cycles it is a load, a branch and the
// store.
//
// It is skipped for a store into this frame, and that is not an optimisation
// -- the deletion half of the barrier is what makes a stack scannable once, so
// the snapshot does not depend on seeing stack writes.
pub const WRITE: &str = "__rt_write";

// `__rt_copy(to, from, shape)` -- a whole value moved, where the value holds
// pointers somewhere in it.
//
// A structure assignment is a great many pointer stores at once and every one
// of them wants the same two shades. One call that walks the shape's map is
// what Go calls a bulk barrier, and it is here for the same reason: the other
// way round is one call per word.
pub const COPY: &str = "__rt_copy";

// ---- Maps and sets ---------------------------------------------------------

// §8 settles that these are library types and that "which one you named says
// how it behaves", so the ordered and the hashed kind are separate routines
// rather than one routine and a flag. A flag would be a branch on every
// insertion of every map in the program, deciding something that was known when
// the literal was written.
//
// `__rt_map_new(key, value): handle`, both of them descriptors.
pub const MAP_NEW: &str = "__rt_map_new";
pub const HASHMAP_NEW: &str = "__rt_hashmap_new";
// `__rt_map_insert(map, key, value)`.
pub const MAP_INSERT: &str = "__rt_map_insert";
pub const HASHMAP_INSERT: &str = "__rt_hashmap_insert";

// `__rt_set_new(elem): handle`.
pub const SET_NEW: &str = "__rt_set_new";
pub const HASHSET_NEW: &str = "__rt_hashset_new";
// `__rt_set_insert(set, elem)`.
pub const SET_INSERT: &str = "__rt_set_insert";
pub const HASHSET_INSERT: &str = "__rt_hashset_insert";

pub fn map_new(hashed: bool) -> &'static str {
    if hashed { HASHMAP_NEW } else { MAP_NEW }
}

pub fn map_insert(hashed: bool) -> &'static str {
    if hashed { HASHMAP_INSERT } else { MAP_INSERT }
}

pub fn set_new(hashed: bool) -> &'static str {
    if hashed { HASHSET_NEW } else { SET_NEW }
}

pub fn set_insert(hashed: bool) -> &'static str {
    if hashed { HASHSET_INSERT } else { SET_INSERT }
}

// ---- Walking one -----------------------------------------------------------

// The cursor protocol, for the things a cursor cannot just count through. An
// array, a run and a `Range` are walked by index arithmetic and reach none of
// these: paying a call to add one to a number would be paying a call to add one
// to a number.
//
// `valid(it, at): bool`, `elem(it, at): T`, `step(it, at): cursor` -- which is
// three of the SIR's four. There is no `start`: `IterStart` is a `Const(-1)`
// whatever is being walked, so the contract is that stepping from -1 lands on
// the first. It is already a protocol (§5: "the language has no iterator
// protocol, so what may be run through is a closed set"), and this is the half
// of that closed set which is the library's rather than the machine's.
//
// Named for the protocol rather than for the set, because a map takes it too --
// the difference is what a turn yields, and that is the runtime's to know from
// the handle.
pub const ITER_VALID: &str = "__rt_iter_valid";
pub const ITER_ELEM: &str = "__rt_iter_elem";
pub const ITER_STEP: &str = "__rt_iter_step";

// ---- Letting go ------------------------------------------------------------

// One release routine per type, not one for all of them.
//
// A single `__rt_drop(ptr)` cannot work: what has to happen depends entirely on
// what is at that address -- a structure releases its fields, a `gc` handle
// tells the collector, an integer does nothing -- and the address does not say
// which. Passing a description alongside would be passing a description that
// something has to build and something has to read, when the type is known
// where the call is written and known nowhere else afterwards.
//
// So the type is put in the *name*, exactly as it is for a fn: `__D` and then
// the type spelled the way `sema::names::Mangler` spells one. `__D3i32` is the
// release of an `i32`, and what defines it is a later piece of work -- these
// are the one group here the runtime does not define, because a release is a
// thing the *compiler* has to emit a body for.
pub fn glue(spelled: &str) -> String {
    let mut out = String::from("__D");
    part(spelled, &mut out);
    out
}

// ---- Strings ---------------------------------------------------------------

// What a string literal is kept under. A literal has no name in the source, so
// one is made from where it sits in the pool -- the numbering is the program's
// and nothing outside it ever names one.
pub fn text(at: usize) -> String {
    format!("__S{}", at)
}

#[cfg(test)]
mod tests;
