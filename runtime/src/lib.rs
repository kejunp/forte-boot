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

pub mod abi;
pub mod alloc;
pub mod fmt;
pub mod gc;
pub mod heap;
pub mod map;
pub mod mem;
pub mod set;
pub mod shape;

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
