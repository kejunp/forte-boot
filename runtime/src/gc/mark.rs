// Tri-colour marking: reaching everything that can be reached.
//
// Three colours and only two bits of state, which is the trick the scheme is
// named for. An object is **white** if its mark bit is not set; **grey** if it
// is set and the object is still on the work list; **black** if it is set and
// it is not. So the colour of a thing is not stored anywhere -- it is where
// the thing is -- and turning grey to black is popping it off a list.
//
// The invariant the whole collector rests on is that **no black object points
// at a white one**. If that holds at the end, everything still white is
// unreachable, because anything reachable would have been reached through
// something black. Marking preserves it on its own: an object only becomes
// black by having every pointer in it shaded first. What can break it is the
// program, which is running at the same time and can move a pointer out of a
// white object into a black one -- and that is what `barrier` is for.
//
// **Shading is where the two kinds of precision meet.** `shade` is handed a
// word and asks the heap what object it is inside; a word that is not an
// address of a live object is dropped and costs a lookup. That is what makes
// the same routine usable for a conservative stack scan, where most words are
// numbers, and for a precise heap scan, where every word handed to it came out
// of a slot a shape called a pointer. Only the *caller* differs.
//
// An object in a span that is never scanned is marked and not pushed. There is
// nothing inside it to reach, so putting it on the list would be putting it
// there to pop it off again -- and the spans that are never scanned are most
// of the bytes in a heap full of strings and numbers.

use super::super::heap::span::SpanId;
use super::super::Runtime;

// A word that might be an address. Marks what it points at, and puts it on the
// work list if there is anything inside it worth reading.
pub fn shade(rt: &mut Runtime, addr: usize) {
    let Some((id, index)) = rt.heap.holding(addr) else { return };
    if !rt.heap.span_mut(id).mark(index) {
        return;
    }
    if rt.heap.span(id).scan {
        rt.gc.work.push((id, index));
    }
}

// Look at up to `budget` grey objects. Returns how many were looked at, which
// is what an assist is measured in.
pub fn drain(rt: &mut Runtime, budget: usize) -> usize {
    let mut done = 0;
    while done < budget {
        let Some((id, index)) = rt.gc.work.pop() else { break };
        scan(rt, id, index);
        done += 1;
    }
    done
}

// One object, precisely: the words its shape called pointers and no others.
//
// This is the only place a heap object's contents are read, and the only place
// the map written at allocation is used. A word the map did not name is not
// read at all -- which is the difference between this and the stack scan, and
// the reason an integer in a structure cannot accidentally keep anything
// alive.
fn scan(rt: &mut Runtime, id: SpanId, index: usize) {
    let base = rt.heap.span(id).base_of(index);
    let words = rt.heap.span(id).words;
    for word in 0..words {
        if !rt.heap.span(id).points(index, word) {
            continue;
        }
        let held = unsafe { *((base + word * 8) as *const usize) };
        shade(rt, held);
    }
}

// Every word of a range, as if any of them could be an address.
//
// The conservative half. It is used for a stack and for the registers, where
// nothing says which words are pointers, and its cost is one heap lookup per
// word -- which is why the lookup is three shifts and no search.
pub fn conservative(rt: &mut Runtime, from: usize, to: usize) {
    let mut at = from.div_ceil(8) * 8;
    while at + 8 <= to {
        let held = unsafe { *(at as *const usize) };
        shade(rt, held);
        at += 8;
    }
}

// ---- Counting --------------------------------------------------------------

// How many bytes are marked, which is what survived and so what the next
// goal is set against. Worked out before anything is swept, because a sweep
// throws the marks away.
pub fn marked_bytes(rt: &Runtime) -> usize {
    let mut out = 0;
    for id in every(rt) {
        let held = rt.heap.span(id);
        out += held.marks.count() * held.size;
    }
    out
}

// Every span there is, wherever it happens to be sitting -- in a central list,
// in the cache, or on the large list. A span in the cache is in no list, so
// anything that walked only the lists would miss it, and both counting and
// sweeping have to reach all of them.
pub fn every(rt: &Runtime) -> Vec<SpanId> {
    let mut out = rt.heap.all();
    out.sort_unstable();
    out.dedup();
    out
}

#[cfg(test)]
mod tests;
