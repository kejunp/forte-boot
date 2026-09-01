// Sweeping: turning what was not marked back into room.
//
// **Lazily**, which is the part worth arguing for. When a cycle ends, nothing
// is freed. Every span is one cycle behind, and a span is swept by whoever
// next wants an object out of it -- which is `heap::cache::Central::span`, and
// is why that function takes a cycle number at all.
//
// Three things come out of that. A program that stops allocating never pays
// for the sweep of a heap it is not using. The work is spread across the
// allocations that follow rather than done in one lump at the end of a cycle,
// so no pause is the size of the heap. And the marks are still there for as
// long as anything might want to read them, which is what lets the live total
// be worked out after the cycle rather than during it.
//
// What it costs is that "how much is free" is not knowable without doing the
// work, and that a span nothing ever asks for again is never swept at all --
// which is what this file is for. `all` finishes the job for the spans the
// allocator did not come back to, and it is what a program that asked for a
// collection outright expects to have happened when the call returns.
//
// A span that empties completely goes back to the heap so its pages can become
// a span of some other class. Without that a program that allocates a great
// many of one size and then a great many of another holds both for ever, which
// is the worst kind of leak: one that looks like a working allocator.

use super::super::heap::span::SpanId;
use super::super::Runtime;
use super::mark;

// Sweep every span that is behind, and give back the ones that emptied.
//
// The large objects are done through their own list because they are on no
// class list and nothing else would find them, and because their pages are
// worth giving back individually -- a hundred kilobytes is a hundred kilobytes.
pub fn all(rt: &mut Runtime) -> usize {
    let cycle = rt.gc.cycle;
    let large: Vec<SpanId> = rt.large.all().to_vec();
    let mut freed = rt.large.sweep(&mut rt.heap, cycle);

    for id in mark::every(rt) {
        if large.contains(&id) || rt.heap.span(id).pages == 0 {
            continue;
        }
        if rt.heap.span(id).swept >= cycle {
            continue;
        }
        let size = rt.heap.span(id).size;
        freed += rt.heap.span_mut(id).sweep(cycle) * size;
        empty(rt, id);
    }

    rt.heap.live = rt.heap.live.saturating_sub(freed);
    rt.gc.freed += freed;
    freed
}

// A bounded amount of the same, for the thread behind the marker. Go has a
// background sweeper for exactly this: lazy sweeping means a span nothing asks
// for again is never swept, and "never" is a heap that does not shrink after a
// program stops allocating.
pub fn some(rt: &mut Runtime, most: usize) -> usize {
    let cycle = rt.gc.cycle;
    let mut done = 0;
    let mut freed = 0;
    for id in mark::every(rt) {
        if done >= most {
            break;
        }
        if rt.heap.span(id).swept >= cycle || rt.heap.span(id).pages == 0 {
            continue;
        }
        let size = rt.heap.span(id).size;
        freed += rt.heap.span_mut(id).sweep(cycle) * size;
        empty(rt, id);
        done += 1;
    }
    rt.heap.live = rt.heap.live.saturating_sub(freed);
    rt.gc.freed += freed;
    done
}

// A span with nothing left in it, handed back -- but only if the cache is not
// sitting on it. A span in the cache is one the allocator is about to take
// something out of, and giving its pages away underneath would be handing out
// an object in a span that no longer exists.
fn empty(rt: &mut Runtime, id: SpanId) {
    if rt.heap.span(id).free() != rt.heap.span(id).count {
        return;
    }
    if rt.cache.all().contains(&id) {
        return;
    }
    rt.central.drop_empty(&mut rt.heap, id);
}

#[cfg(test)]
mod tests;
