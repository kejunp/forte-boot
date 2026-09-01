// The write barrier: what happens when the program stores a pointer while a
// collection is running.
//
// The marker walks the heap as it stood when the cycle began. The program
// carries on writing to it. Between them they can hide an object: the marker
// has already looked at A and moved on, the program takes the only pointer to
// C out of B, which the marker has not looked at yet, and puts it in A. Now
// nothing the marker will ever look at points at C, and C is swept while the
// program is holding it.
//
// **The hybrid barrier**, which is Go's since 1.8:
//
//     shade(*slot)      -- what is being overwritten
//     shade(value)      -- what is being written
//     *slot = value
//
// Two shades and not one, and they are two different guarantees.
//
// The first is Yuasa's, a *deletion* barrier: nothing that was reachable when
// the cycle began is ever lost, because a pointer only stops being reachable
// by being overwritten and being overwritten shades it. That is what makes the
// mark a snapshot of the heap at the start of the cycle -- and it is what lets
// a stack be scanned once and never again, which is the whole reason for the
// hybrid. Go's pause fell by orders of magnitude when it stopped rescanning
// stacks.
//
// The second is Dijkstra's, an *insertion* barrier: anything written into the
// heap is reached, whether or not the marker was going to get there. It covers
// the pointer that came from a place the deletion barrier does not see -- off
// a black stack, out of a register.
//
// Either alone leaves a hole. Both together are what Go arrived at after two
// releases of trying one.
//
// **The fast path is a load and a branch.** The phase is kept in an atomic
// outside the runtime's lock precisely so that this can ask it without taking
// one. Between cycles the barrier is a comparison and a store, which is what
// it has to be: this is on the path of every pointer store in the program.
//
// **What the compiler does not emit, this cannot do.** A barrier only runs
// where the lowering put one, and `mir::lower` puts one on stores through an
// address that is not a frame slot. A store the lowering decided was to the
// stack skips this, which is correct exactly because of the deletion half
// above -- the snapshot does not depend on seeing stack writes.

use std::sync::atomic::Ordering;

use super::{mark, Phase, PHASE};

// `__rt_write`: a pointer going into a place.
//
// The whole of the barrier including the store, rather than a hook before it.
// If the store were the caller's, the caller could do it before calling and
// there would be a window in which the old value was already gone and had not
// been shaded.
pub fn write(slot: *mut usize, value: usize) {
    if PHASE.load(Ordering::Acquire) == 0 {
        unsafe { *slot = value };
        return;
    }
    write_in(&mut super::super::runtime(), slot, value);
}

// The barrier proper, over a runtime that has already been reached for.
//
// Split from the entry point above because the flag and the lock are the
// *fast path*, not the barrier: what the barrier does is the three lines
// below, and they are the same three whether the runtime is the program's or
// one a test built.
pub fn write_in(rt: &mut super::super::Runtime, slot: *mut usize, value: usize) {
    if rt.gc.phase == Phase::Mark {
        mark::shade(rt, unsafe { *slot });
        mark::shade(rt, value);
    }
    unsafe { *slot = value };
}

// `__rt_copy`: a whole value moved from one place to another, where the value
// holds pointers somewhere in it.
//
// A structure assignment is a great many pointer stores at once and every one
// of them needs the same two shades. Doing them one at a time through `write`
// would be right and would take the lock once per word; this takes it once and
// walks the map, which is Go's `bulkBarrierPreWrite` and exists for the same
// reason.
//
// The map is the *source* type's, and both sides are of that type -- an
// assignment is between two of one type -- so one map covers what is being
// overwritten and what is being written.
pub fn copy(to: *mut u8, from: *const u8, shape: super::super::shape::Shape) {
    if PHASE.load(Ordering::Acquire) == 0 {
        unsafe { std::ptr::copy(from, to, shape.bytes()) };
        return;
    }
    copy_in(&mut super::super::runtime(), to, from, shape);
}

pub fn copy_in(
    rt: &mut super::super::Runtime,
    to: *mut u8,
    from: *const u8,
    shape: super::super::shape::Shape,
) {
    if rt.gc.phase == Phase::Mark {
        for word in 0..shape.words() {
            if !shape.points(word) {
                continue;
            }
            let old = unsafe { *(to.add(word * 8) as *const usize) };
            let new = unsafe { *(from.add(word * 8) as *const usize) };
            mark::shade(rt, old);
            mark::shade(rt, new);
        }
    }
    unsafe {
        std::ptr::copy(from, to, shape.bytes());
    }
}

#[cfg(test)]
mod tests;
