// An object too big to share a span with anything.
//
// Past the last size class the whole scheme stops paying. A class exists so
// that many objects can share a span and be told apart by arithmetic; when one
// object would fill most of a span there is nothing to tell apart, and the
// rounding up to a class would waste more than the bookkeeping saved. So above
// thirty-two kilobytes an object gets a run of pages of its own, rounded up to
// a whole page and no further.
//
// Such a span has one object in it, at index nought, and everything the rest of
// the runtime does to a span works on it unchanged -- it is marked by raising
// bit nought, it is swept by the same two lines, and an address inside it
// resolves to object nought by the same division. That is the whole reason
// large objects are a span with a count of one rather than a structure of their
// own: nothing above here has to know which kind it is holding.
//
// What they do need is a list. A small span is findable through the central
// list for its class; a large one belongs to no class, so unless something
// keeps them there is nothing to sweep when the program stops asking for more.

use super::classes;
use super::span::SpanId;
use super::Heap;

// Whether this many bytes has to have a span to itself.
pub fn alone(bytes: usize) -> bool {
    bytes > classes::MAX
}

pub struct Large {
    held: Vec<SpanId>,
}

impl Large {
    pub fn new() -> Large {
        Large { held: Vec::new() }
    }

    pub fn make(
        &mut self,
        heap: &mut Heap,
        bytes: usize,
        scan: bool,
        cycle: u32,
    ) -> Option<SpanId> {
        let id = heap.span_of_bytes(bytes, scan)?;
        // Its own object, immediately -- there is only the one, and nothing
        // would ever look for a second.
        heap.span_mut(id).take();
        heap.span_mut(id).swept = cycle;
        self.held.push(id);
        Some(id)
    }

    pub fn all(&self) -> &[SpanId] {
        &self.held
    }

    // A large object that was not reached is not put on a free list -- there
    // is no list for something of this size -- so its pages go straight back
    // to the heap, which is where a run of that many pages is worth something
    // to somebody else.
    pub fn sweep(&mut self, heap: &mut Heap, cycle: u32) -> usize {
        let mut gone = 0;
        let mut kept = Vec::new();
        for id in std::mem::take(&mut self.held) {
            if heap.span(id).swept >= cycle {
                kept.push(id);
                continue;
            }
            let bytes = heap.span(id).size;
            heap.span_mut(id).sweep(cycle);
            if heap.span(id).free() == heap.span(id).count {
                gone += bytes;
                heap.release(id);
            } else {
                kept.push(id);
            }
        }
        self.held = kept;
        gone
    }
}

impl Default for Large {
    fn default() -> Large {
        Large::new()
    }
}

#[cfg(test)]
mod tests;
