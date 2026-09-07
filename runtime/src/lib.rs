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
// **The collector is Go's, in shape and mostly in substance.** Non-moving
// mark-and-sweep; a heap of size-classed spans under a two-level allocator; a
// tri-colour marker with a hybrid Dijkstra-Yuasa write barrier; marking that
// runs concurrently with the program and two short stops rather than one long
// one; sweeping done lazily by whoever next wants the room; and a pace set by
// how much the heap grew since the last cycle. Each of those is written in the
// file that does it and argued for there.
//
// Where it is not Go's, it is because something the compiler would have to
// emit is not emitted, and each of those is said out loud rather than left to
// be discovered:
//
//   The roots are scanned **conservatively**. Go's collector is precise
//   everywhere because Go's compiler emits a map of where the pointers are on
//   every stack frame at every safepoint. Nothing here emits one. So the stack
//   and the callee-saved registers are read as if any word could be an
//   address, and a word that looks like one keeps its object alive. That is
//   sound -- nothing moves, so an address that was guessed at is never
//   followed anywhere -- and it retains garbage that a precise scan would not.
//   The heap itself *is* precise, through `shape`.
//
//   The safepoints are allocation and the write barrier, and nothing else. Go
//   preempts a goroutine at an asynchronous safepoint with a signal. A loop
//   here that neither allocates nor stores a pointer never reaches one, and
//   the two stops wait for it. That was Go's own problem until 1.14.
//
//   There is one mutator. The language has no threads, so there is one cache,
//   and the lock the central lists would need is not taken. The structure is
//   kept; the contention is not there to have.
//
//   No finalisers, no weak references, and nothing is given back to the
//   kernel once taken.
//
// One lock over the whole runtime, held in short slices. Go has a dozen and
// takes them at a fine grain; here the collector thread takes this one, does a
// bounded amount of marking, and lets go, which is what makes the marking
// concurrent with the program rather than merely on another thread. It is the
// coarsest thing that is still concurrent, and the place to look first if a
// program ever spends its time waiting here.

use std::sync::{Mutex, MutexGuard, OnceLock};

// ---- One at a time -----------------------------------------------------------

// The lock every test that touches the *process-wide* collector phase takes.
//
// `gc::phase` is one flag for the whole process -- the barrier reads it on
// every write and cannot afford a runtime to ask -- so a test that starts a
// cycle raises it for every other test running beside it. Three modules test
// through it and each had a lock of its own, which is three locks and no
// order: `gc`'s tests raised the flag while `abi`'s asserted it was down, and
// what that looked like was a test failing about one run in four.
//
// One lock, named here so that all three take the same one. It is not
// tidiness: the runtime is written for one mutator and a test binary has a
// dozen, which is a thing the tests arrange around rather than a thing the
// runtime is wrong about.
#[cfg(test)]
pub(crate) fn alone() -> std::sync::MutexGuard<'static, ()> {
    static ORDER: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    match ORDER.get_or_init(|| std::sync::Mutex::new(())).lock() {
        Ok(held) => held,
        Err(held) => held.into_inner(),
    }
}

pub mod abi;
pub mod alloc;
pub mod env;
pub mod fmt;
pub mod gc;
pub mod heap;
pub mod map;
pub mod mem;
pub mod set;
pub mod shape;
pub mod stop;
pub mod test;

use heap::cache::{Cache, Central};
use heap::large::Large;
use heap::span::SpanId;
use heap::Heap;

// Everything the runtime is, behind the one lock.
pub struct Runtime {
    pub heap:    Heap,
    pub central: Central,
    pub cache:   Cache,
    pub large:   Large,
    pub gc:      gc::State,
    // Objects nothing is allowed to collect, which is what `__rt_alloc` hands
    // out. A sweep clears every mark, so they are marked again at the end of
    // each cycle rather than once.
    pub pinned:  Vec<(SpanId, usize)>,
    // The maps and sets the program has made. They are roots in their own
    // right -- a key or a value in one is reachable however the container was
    // reached -- and they are the one part of the heap the collector walks
    // knowingly rather than through a shape.
    pub tables:  Vec<map::Table>,
    pub sets:    Vec<set::Held>,
    // Where the program's globals are, and what each holds. A global is not on
    // any stack and is not in the heap, so it is reachable from neither of the
    // two root sets that find things by looking -- and a global holding the
    // only reference to a collected value would have it swept underneath.
    //
    // Registered rather than discovered. A linker's `__data_start` and `_edata`
    // are neither portable across the three machines nor precise, and a shape
    // per global buys precision a range scan could never have: a global with no
    // pointers in it costs nothing, and one with a pointer at the third word is
    // walked at the third word.
    pub rooted:  Vec<(usize, shape::Shape)>,
}

impl Runtime {
    // Public because every test builds its own rather than sharing the one
    // below: a collector's tests are about what a heap does from empty, and a
    // heap that other tests have been allocating out of is not empty.
    pub fn new() -> Runtime {
        Runtime {
            heap: Heap::new(),
            central: Central::new(),
            cache: Cache::new(),
            large: Large::new(),
            gc: gc::State::new(),
            pinned: Vec::new(),
            rooted: Vec::new(),
            tables: Vec::new(),
            sets: Vec::new(),
        }
    }
}

static RUNTIME: OnceLock<Mutex<Runtime>> = OnceLock::new();

// The lock, taken. A poisoned lock means a thread died holding it, which here
// means the runtime is in an unknown state -- but refusing to carry on would
// turn a bug somewhere else into a second failure with less information in it,
// so what was there is taken and the program is left to fail on its own terms.
pub fn runtime() -> MutexGuard<'static, Runtime> {
    match RUNTIME.get_or_init(|| Mutex::new(Runtime::new())).lock() {
        Ok(held) => held,
        Err(held) => held.into_inner(),
    }
}

pub fn with<R>(f: impl FnOnce(&mut Runtime) -> R) -> R {
    f(&mut runtime())
}
