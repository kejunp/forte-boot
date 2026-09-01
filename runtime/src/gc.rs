// The collection cycle: when it runs, what it does, and who does it.
//
//     off --- trigger --> setup --> mark --> termination --> sweep --> off
//                          STW      thread       STW          lazy
//
// Five states and two of them stop the program. That shape is Go's and the
// whole argument for it is in where the stops are: everything expensive --
// walking the heap, working out what died -- happens while the program runs,
// and what is left inside the stops is turning the barrier on and noticing
// that there is no work left. A collector that stopped the program for the
// walk would be simpler and its pauses would be the size of the live heap.
//
// **Setup** is done by the mutator itself and could not be done by anyone
// else. Its job is to scan the roots, and the roots are the mutator's own
// stack: another thread reading a running stack reads a stack that is being
// written. So a cycle begins inside an allocation, on the thread that
// allocated, which is also the moment the program is provably not in the
// middle of building an object.
//
// A stack is scanned **once**. That is what the hybrid barrier in `barrier`
// buys and it is the single most important property here: once a stack has
// been read it is black and stays black, so the termination stop does not have
// to read it again. Go got this in 1.8 and the pause went from milliseconds to
// microseconds.
//
// **Marking** is the thread. It takes the lock, drains a bounded number of
// grey objects, and lets go -- so the program can allocate between slices. It
// is a coarser grain than Go's, which locks per work buffer, and it is the
// place to look first if a program is found waiting on the runtime.
//
// **Assists** are what stop a program outrunning the marker. A mutator that
// allocates during a cycle does marking work in proportion to what it asked
// for, so the faster it allocates the faster the cycle it is racing finishes.
// Without them a program that allocates in a tight loop would reach the goal
// before the marker reached the end of the heap, and the heap would grow
// without bound while a collection ran forever.
//
// **Sweeping** is nobody's, until somebody wants the room -- see `sweep`.
//
// What is *not* here is a way to stop a program that is not allocating. Go
// preempts with a signal at a safepoint the compiler emitted; nothing emits
// one here, so a loop that neither allocates nor stores a pointer is a loop
// the two stops wait for. It is the same problem Go had until 1.14 and it has
// the same fix, which is a thing the compiler has to do.

use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::OnceLock;
use std::thread::{self, Thread};
use std::time::Duration;

pub mod barrier;
pub mod mark;
pub mod pace;
pub mod roots;
pub mod sweep;

use super::heap::span::SpanId;
use super::Runtime;

// ---- Where a cycle has got to ----------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    // Nothing is running. Allocation counts towards the trigger and the write
    // barrier is a plain store.
    Off,
    // The marker is walking. Everything allocated is black, and every pointer
    // written anywhere goes through the barrier.
    Mark,
}

// The phase again, outside the lock.
//
// The write barrier is on the path of every pointer store in the program, and
// taking a lock to find out that there is nothing to do would be the most
// expensive thing in the runtime by a wide margin. So the phase is kept here
// as well, and the barrier reads this first and only takes the lock when the
// answer is that a cycle is running. The two can disagree for as long as it
// takes one thread to store a byte, and that is harmless in the direction that
// matters: the flag is raised inside the setup stop, before anything the
// marker did could be undone by a store that skipped the barrier.
static PHASE: AtomicU8 = AtomicU8::new(0);

pub fn phase() -> Phase {
    if PHASE.load(Ordering::Acquire) == 0 { Phase::Off } else { Phase::Mark }
}

fn set_phase(held: Phase) {
    PHASE.store(u8::from(held == Phase::Mark), Ordering::Release);
}

// ---- What the collector remembers ------------------------------------------

pub struct State {
    pub phase:   Phase,
    // Which cycle the heap is in. A span whose own number is behind this has
    // not been swept since the last collection, and holds garbage that is
    // still counted as allocated.
    pub cycle:   u32,
    // Whether an object being made now should be marked as it is made.
    pub black:   bool,
    // The grey set: objects that have been reached and whose own contents have
    // not been looked at yet. A stack rather than a queue because the order
    // does not matter and the depth-first order is kinder to the cache.
    pub work:    Vec<(SpanId, usize)>,
    // What was live at the end of the last cycle, and what the heap is allowed
    // to grow to before the next one starts.
    pub live:    usize,
    pub goal:    usize,
    // How many cycles have finished and how many bytes they freed, which is
    // what a program asking whether the collector is working reads.
    pub cycles:  u32,
    pub freed:   usize,
    // Whether anything has said where the stack starts. Without that the roots
    // cannot be found, and a cycle that ran anyway would free everything.
    pub rooted:  bool,
}

impl State {
    pub fn new() -> State {
        State {
            phase: Phase::Off,
            cycle: 1,
            black: false,
            work: Vec::new(),
            live: 0,
            goal: pace::FIRST,
            cycles: 0,
            freed: 0,
            rooted: false,
        }
    }
}

impl Default for State {
    fn default() -> State {
        State::new()
    }
}

// ---- The cycle -------------------------------------------------------------

// How many objects the marker looks at before letting go of the lock. Big
// enough that taking the lock is not most of the work, small enough that a
// program waiting for it is not waiting long.
pub const SLICE: usize = 256;

// Turn the barrier on, colour the roots, and let the marker go.
//
// Everything in here is inside the stop, so everything in here has to be
// short. Scanning the roots is the one part that is not constant, and it is
// the mutator's stack rather than the heap -- thousands of words rather than
// however many objects there are.
pub fn start(rt: &mut Runtime, stack: usize) {
    // Nothing has said where this thread's stack begins, so the roots cannot
    // be found. Not collecting is the safe half of that: the heap grows, and
    // the alternative is freeing what the program is holding.
    if rt.gc.phase == Phase::Mark || roots::base() == 0 {
        return;
    }
    open(rt);
    roots::all(rt, stack);
    wake();
}

// The same, with the roots given rather than found.
//
// This is what makes a collector testable. Found roots are a conservative scan
// of a running stack, and a stack holds whatever the last few calls left on it
// -- so a test that allocated something and then wanted it collected would be
// testing whether a dead local happened to still be readable, which is not a
// question with an answer. Given roots make the reachable set exactly what the
// test says it is, and everything after this point is the same code either
// way.
pub fn start_from(rt: &mut Runtime, held: &[usize]) {
    if rt.gc.phase == Phase::Mark {
        return;
    }
    open(rt);
    for &at in held {
        mark::shade(rt, at);
    }
    roots::owned(rt);
}

// Turning the barrier on, which both of the above do first and neither may
// do second: a store that got in before the flag was raised is a store the
// marker did not see.
fn open(rt: &mut Runtime) {
    rt.gc.phase = Phase::Mark;
    rt.gc.black = true;
    set_phase(Phase::Mark);
    rt.gc.work.clear();
}

// A slice of marking. `true` while there is still something grey, which is
// what the thread loops on and what termination waits for.
pub fn step(rt: &mut Runtime, budget: usize) -> bool {
    if rt.gc.phase != Phase::Mark {
        return false;
    }
    mark::drain(rt, budget);
    !rt.gc.work.is_empty()
}

// The second stop. Everything grey has been looked at, so what is marked is
// what is reachable; the barrier comes off, the cycle number moves on, and
// every span in the heap is now one cycle behind and will be swept by whoever
// wants it.
//
// The barrier is turned off *after* the last drain and not before. A store
// between the two would be a store that skipped the barrier while the marker
// still believed it had finished, and the object it hid would be swept.
pub fn finish(rt: &mut Runtime) {
    if rt.gc.phase != Phase::Mark {
        return;
    }
    mark::drain(rt, usize::MAX);
    rt.gc.phase = Phase::Off;
    rt.gc.black = false;
    set_phase(Phase::Off);

    // What survived, worked out before anything is swept: the marks are what
    // the next goal is set against, and a sweep clears them.
    let live = mark::marked_bytes(rt);
    rt.gc.cycle += 1;
    rt.gc.cycles += 1;
    rt.gc.live = live;
    rt.gc.goal = pace::goal(live);
    rt.heap.live = live;

    // Whatever was handed out and never collected is reachable by definition,
    // and a sweep has just thrown away the marks that said so.
    for (id, index) in rt.pinned.clone() {
        rt.heap.span_mut(id).mark(index);
    }
}

// The whole cycle, start to end, on the caller's thread.
//
// This is what `__rt_collect` does and what nearly every test does. It is not
// a lesser version of the concurrent path -- it is the same three calls the
// thread makes, made one after another instead of with the lock let go in
// between. That is what makes the collector testable: the concurrency is in
// who calls these and when, and not in what they do.
pub fn cycle_now(rt: &mut Runtime, stack: usize) {
    start(rt, stack);
    finish_now(rt);
}

// And the same over roots that were given rather than found.
pub fn cycle_from(rt: &mut Runtime, held: &[usize]) {
    start_from(rt, held);
    finish_now(rt);
}

fn finish_now(rt: &mut Runtime) {
    while step(rt, SLICE) {}
    finish(rt);
    sweep::all(rt);
}

// ---- When to start ---------------------------------------------------------

// Called after every collected allocation. Two things: a mutator that is
// allocating during a cycle pays for it in marking, and a heap that has grown
// past its goal starts one.
pub fn after(rt: &mut Runtime, bytes: usize, stack: usize) {
    if rt.gc.phase == Phase::Mark {
        mark::drain(rt, pace::assist(bytes));
        return;
    }
    if rt.heap.live >= rt.gc.goal {
        start(rt, stack);
    }
}

// ---- The thread ------------------------------------------------------------

// The marker, and the sweeper behind it.
//
// It takes the lock, does a slice of whatever there is to do, and lets go --
// so the program can allocate in between, which is what makes this concurrent
// with the program rather than merely elsewhere. When there is nothing to do
// it parks, and `start` wakes it.
//
// Parking with a timeout and not for ever, because the thing that would wake
// it is the thing it is racing: a cycle can also be started and finished on
// the mutator's own thread through `__rt_collect`, and a sweeper asleep with
// spans to sweep is a heap that does not shrink.
static WORKER: OnceLock<Thread> = OnceLock::new();

pub fn begin() {
    if WORKER.get().is_some() {
        return;
    }
    let made = thread::Builder::new().name("fortec-gc".to_string()).spawn(work);
    if let Ok(held) = made {
        let _ = WORKER.set(held.thread().clone());
    }
}

fn wake() {
    if let Some(held) = WORKER.get() {
        held.unpark();
    }
}

fn work() -> ! {
    loop {
        let doing = {
            let mut rt = super::runtime();
            if rt.gc.phase == Phase::Mark {
                if !step(&mut rt, SLICE) {
                    finish(&mut rt);
                }
                true
            } else {
                sweep::some(&mut rt, SLICE) > 0
            }
        };
        if !doing {
            thread::park_timeout(Duration::from_micros(500));
        }
    }
}

#[cfg(test)]
mod tests;
