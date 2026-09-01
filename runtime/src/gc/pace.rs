// How often a collection runs, and how hard a program that is allocating has
// to help.
//
// **The goal is proportional to what survived.** After a cycle, the heap is
// allowed to grow to the live size plus a percentage of it before the next one
// starts. That is Go's `GOGC`, it defaults to a hundred there and here, and a
// hundred means "collect when the heap has doubled".
//
// The reason it is a proportion and not a fixed number of bytes is the one
// thing about pacing that is not obvious. The work a cycle does is
// proportional to what is *live*, and the room a cycle recovers is
// proportional to what has been allocated since the last one. Setting the
// trigger as a multiple of the live size makes the ratio between those two
// constant, so the fraction of a program's time spent collecting stays the
// same whether its heap is a megabyte or a gigabyte. A fixed trigger would
// make a program with a large live heap collect constantly and recover almost
// nothing each time.
//
// **Assists are the other half.** The goal says when to start; it says nothing
// about finishing before the program allocates past it. A program in a tight
// allocating loop can outrun the marker, and then the heap grows without bound
// while a collection runs forever. So a mutator that allocates during a cycle
// does marking work in proportion to what it asked for, and the faster it
// allocates the faster the cycle it is racing finishes. Go computes the ratio
// from how much scanning is left against how much room is left before the
// goal; what is here is a flat ratio, which is the same idea with the
// controller taken out -- and the controller is what would be worth adding
// first if a program were ever measured overshooting its goal.
//
// **Nothing is given back to the kernel.** Go has a scavenger that returns
// pages it has not used for a while. There is none here, so `reserved` only
// ever grows. For a runtime with no long-running program to be measured
// against, a scavenger would be a guess about a workload nobody has.

// What the heap may grow to before the first cycle. Something has to be
// chosen, because the rule above is written in terms of a live size and there
// is not one yet. Four megabytes is Go's order of magnitude and is a size at
// which a program that never allocates much never collects at all.
pub const FIRST: usize = 4 << 20;

// The default percentage, and where a program may say otherwise.
pub const PERCENT: usize = 100;

// How many objects of marking a mutator does per byte it allocates, as a
// divisor: one object marked for every this many bytes asked for.
const PER_BYTE: usize = 64;

// The most an assist does at once. A single large allocation should not turn
// into an unbounded pause -- the point is to keep the marker ahead, not to
// finish the cycle in one call.
const MOST: usize = 4096;

// What the collector reads at the start. `FORTEC_GC` is spelled after Go's
// `GOGC` and means the same thing; anything that is not a number is ignored
// rather than complained about, because a runtime is not a place to be
// diagnosing a shell.
pub fn percent() -> usize {
    match std::env::var("FORTEC_GC") {
        Ok(held) => held.trim().parse().unwrap_or(PERCENT),
        Err(_) => PERCENT,
    }
}

// What the heap may grow to, given what survived the cycle just finished.
//
// Never less than the first goal: a program whose live heap is tiny would
// otherwise collect on every allocation, spending all its time proving that
// nothing died.
pub fn goal(live: usize) -> usize {
    let held = live.saturating_add(live / 100 * percent());
    held.max(FIRST)
}

// How much marking to do for an allocation of this size.
pub fn assist(bytes: usize) -> usize {
    (bytes / PER_BYTE + 1).min(MOST)
}

#[cfg(test)]
mod tests;
