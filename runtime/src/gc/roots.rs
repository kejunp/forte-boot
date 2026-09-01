// Where marking starts: the words that are reachable without going through
// anything else.
//
// Four of them here, and they are not equally honest.
//
//   the stack        every word between where the mutator is now and where its
//                    stack began. Read **conservatively**: nothing says which
//                    of those words are pointers.
//   the registers    the callee-saved ones, which are the only registers a
//                    value can be sitting in across the call into the runtime.
//                    Also conservative, and for the same reason.
//   what is pinned   `__rt_alloc`'s objects, which nothing collects.
//   the containers   the maps and sets the runtime owns, which it walks
//                    knowingly because it wrote them.
//
// **The stack is the compromise in this whole runtime.** Go's collector is
// precise here: the Go compiler emits, for every function and every point in
// it where a collection can happen, a map saying which stack slots hold
// pointers. Nothing in this compiler emits one -- `mir::regalloc`'s header
// says the prologue is not written, let alone a map of what is in the frame --
// so there is no way to tell a pointer on the stack from an integer that looks
// like one, and both are followed.
//
// What that costs is exactly one thing: an integer whose value happens to be
// the address of a dead object keeps that object alive. It costs nothing else,
// and in particular it is *safe*, for the reason that decides the whole
// design: nothing moves. A precise collector that moved objects could not
// guess, because a guess that was wrong would have it rewriting an integer
// into a different integer. A non-moving one only ever sets a bit.
//
// What it does not cost is precision on the heap, which is the part that is
// large. A stack is thousands of words; a heap is millions. `mark::scan` reads
// only the words a shape named, and that is where the accuracy that matters
// is.
//
// **Where the stack begins has to be told to the runtime.** There is no way to
// work it out from inside: the address of a local says where the stack is now,
// not where it started, and the difference is the whole of what has to be
// scanned. So `__rt_init` records it, and until something does, a cycle will
// not start at all. A heap that grows for ever is the honest failure for a
// program that never said where its roots are; collecting without them would
// free everything the program is holding.

use std::cell::Cell;

use super::super::Runtime;
use super::mark;

thread_local! {
    // The highest address of this thread's stack, as the thread itself
    // reported it. Per thread because a stack is per thread, and a `Cell`
    // because it is written once and read at every collection.
    static BASE: Cell<usize> = const { Cell::new(0) };
}

// Works out where this thread's stack begins, and remembers it. Called by
// `__rt_init` and by the tests.
//
// The address of a local would be the obvious answer and is the wrong one: it
// says where the stack is *now*, and everything the caller's caller is holding
// is above that. Nor can a constant be added to it, because how much is above
// depends on how deep the call was.
//
// So it is asked. The kernel keeps a list of every mapping a process has, and
// a thread's stack is one of them; the one holding the address of a local here
// is this thread's, and its far end is where the stack began. That is the
// exact answer rather than a guess, it works for a thread as well as for the
// main one, and it is read once.
//
// If it cannot be read -- no `/proc`, or a stack the list does not describe --
// nothing is recorded, and a collection will not start. See the header.
pub fn note() {
    let here = 0usize;
    let at = std::ptr::addr_of!(here) as usize;
    if let Some(top) = mapping(at) {
        BASE.with(|held| held.set(top));
    }
}

// The far end of the mapping holding this address, out of the kernel's own
// list. Each line begins `start-end `, in hexadecimal.
fn mapping(at: usize) -> Option<usize> {
    let held = std::fs::read_to_string("/proc/self/maps").ok()?;
    for line in held.lines() {
        let (range, _) = line.split_once(' ')?;
        let (from, to) = range.split_once('-')?;
        let from = usize::from_str_radix(from, 16).ok()?;
        let to = usize::from_str_radix(to, 16).ok()?;
        if at >= from && at < to {
            return Some(to);
        }
    }
    None
}

pub fn base() -> usize {
    BASE.with(|held| held.get())
}

// Where the caller is now. Taken as the address of a local, which is inside
// the caller's frame and so below everything worth scanning.
#[inline(never)]
pub fn here() -> usize {
    let at = 0usize;
    std::ptr::addr_of!(at) as usize
}

// ---- The registers ---------------------------------------------------------

// The callee-saved registers, spilled somewhere they can be read.
//
// A value that was in a caller-saved register when the program called into the
// runtime has already been written to the stack by the caller -- that is what
// caller-saved means -- so the stack scan finds it. A value in a callee-saved
// register has not, and unless it is put somewhere it would be invisible: an
// object whose only reference is in `r14` would be freed underneath a live
// pointer.
//
// The scratch register the addresses are built through is a caller-saved one,
// so it is not one of the ones being read. That matters: a store through a
// register that was itself in the list would write the pointer over the value
// being saved.
#[cfg(target_arch = "x86_64")]
pub fn registers() -> [usize; 6] {
    let mut out = [0usize; 6];
    unsafe {
        std::arch::asm!(
            "mov [rax], rbx",
            "mov [rax + 8], rbp",
            "mov [rax + 16], r12",
            "mov [rax + 24], r13",
            "mov [rax + 32], r14",
            "mov [rax + 40], r15",
            in("rax") out.as_mut_ptr(),
            options(nostack, preserves_flags)
        );
    }
    out
}

#[cfg(target_arch = "aarch64")]
pub fn registers() -> [usize; 11] {
    let mut out = [0usize; 11];
    unsafe {
        std::arch::asm!(
            "stp x19, x20, [x0]",
            "stp x21, x22, [x0, #16]",
            "stp x23, x24, [x0, #32]",
            "stp x25, x26, [x0, #48]",
            "stp x27, x28, [x0, #64]",
            "str x29, [x0, #80]",
            in("x0") out.as_mut_ptr(),
            options(nostack, preserves_flags)
        );
    }
    out
}

// ---- All of them -----------------------------------------------------------

// Colour everything reachable without going through the heap. `stack` is where
// the mutator is, which the caller takes for itself rather than here: taking
// it in this frame would leave out everything between the two.
pub fn all(rt: &mut Runtime, stack: usize) {
    let top = base();
    if top > stack {
        mark::conservative(rt, stack, top);
    }
    for held in registers() {
        mark::shade(rt, held);
    }
    owned(rt);
}

// The roots that are the runtime's own rather than the program's: what
// `__rt_alloc` handed out and nothing collects, and the contents of every map
// and set. Neither is on a stack, so both are found the same way however a
// cycle was started.
pub fn owned(rt: &mut Runtime) {
    for (id, index) in rt.pinned.clone() {
        if rt.heap.span_mut(id).mark(index) && rt.heap.span(id).scan {
            rt.gc.work.push((id, index));
        }
    }
    containers(rt);
}

// The maps and sets the runtime made. Their keys and values are reachable
// through the container however the container itself was reached, and the
// runtime knows exactly where they are -- so these are walked knowingly rather
// than guessed at.
//
// Written as a separate step and not as part of the heap scan because a
// container's own storage is not an object the shape system describes: it was
// made by this runtime, for this runtime, and there is no compiler-emitted
// descriptor for a thing the compiler has never heard of.
fn containers(rt: &mut Runtime) {
    for at in 0..rt.tables.len() {
        for held in rt.tables[at].roots() {
            mark::shade(rt, held);
        }
    }
    for at in 0..rt.sets.len() {
        for held in rt.sets[at].roots() {
            mark::shade(rt, held);
        }
    }
}

#[cfg(test)]
mod tests;
