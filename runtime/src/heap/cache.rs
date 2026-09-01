// The two levels between a span and an allocation.
//
// Go has three of these and so does this: an mcache that one thread allocates
// out of with no lock at all, an mcentral per size class holding the spans
// that are not in anybody's cache, and the mheap underneath. The reason for
// the middle one is that a span is a big thing to hand over and a small thing
// to run out of -- a cache that went to the heap every time it filled a span
// would take the heap's lock once per few hundred objects instead of once per
// few thousand.
//
// **The lock is not here.** The language has no threads, so there is one
// mutator, one cache, and nothing to contend for. What is kept is the
// *structure*: the cache holds one span per class and gives it up when it
// fills, and the central lists are what it gives it up to. Keeping the shape
// without the lock costs almost nothing and means the lock is an addition
// rather than a rewrite the day something needs one. Dropping the shape and
// allocating straight out of the heap would be the cheaper thing to write and
// the harder thing to undo.
//
// Two lists per class and not one. A span with room in it and a span with none
// are asked for at different times -- the first every time something is
// allocated, the second only by a sweep -- and keeping them apart is what
// makes the first of those a pop rather than a search.
//
// Everything here is doubled on whether the objects hold pointers. A span is
// scanned or it is not, and that is fixed when it is made, so an `i32` and a
// `&Node` of the same size never share one. Paying for two sets of lists is
// what buys never walking a span full of numbers.

use super::classes;
use super::span::SpanId;
use super::Heap;

// Which of the two lists a span goes in: nought for objects with no pointers,
// one for objects with some.
fn which(scan: bool) -> usize {
    usize::from(scan)
}

// ---- The shared lists ------------------------------------------------------

pub struct Central {
    // Spans with room, per class, per whether they are scanned.
    partial: Vec<[Vec<SpanId>; 2]>,
    // And spans with none, which are here only so that a sweep can find them.
    full:    Vec<[Vec<SpanId>; 2]>,
}

impl Central {
    pub fn new() -> Central {
        let empty = || vec![[Vec::new(), Vec::new()]; classes::COUNT + 1];
        Central { partial: empty(), full: empty() }
    }

    // A span of this class with something free in it.
    //
    // A span that has not been swept this cycle is swept here rather than
    // anywhere else, which is what "lazy sweeping" comes to: the work of
    // finding out what died is done by whoever next wants the room, so a
    // program that stops allocating never pays for it at all.
    pub fn span(
        &mut self,
        heap: &mut Heap,
        class: usize,
        scan: bool,
        cycle: u32,
    ) -> Option<SpanId> {
        let side = which(scan);
        while let Some(id) = self.partial[class][side].pop() {
            if heap.span(id).swept < cycle {
                heap.span_mut(id).sweep(cycle);
            }
            if !heap.span(id).full() {
                return Some(id);
            }
            self.full[class][side].push(id);
        }
        // Nothing partial. A full one that has not been swept may have room
        // once it has been, and sweeping one is cheaper than asking the heap
        // for pages it would have to get from the kernel.
        let mut behind = Vec::new();
        self.full[class][side].retain(|&id| {
            if heap.span(id).swept < cycle {
                behind.push(id);
                return false;
            }
            true
        });
        for id in behind {
            heap.span_mut(id).sweep(cycle);
            if heap.span(id).full() {
                self.full[class][side].push(id);
            } else {
                self.partial[class][side].push(id);
            }
        }
        if let Some(id) = self.partial[class][side].pop() {
            return Some(id);
        }

        let id = heap.span_of_class(class, scan)?;
        heap.span_mut(id).swept = cycle;
        Some(id)
    }

    // A span the cache has finished with, put back where it belongs.
    pub fn give(&mut self, heap: &Heap, id: SpanId) {
        let held = heap.span(id);
        let (class, side) = (held.class, which(held.scan));
        if held.full() {
            self.full[class][side].push(id);
        } else {
            self.partial[class][side].push(id);
        }
    }

    // Every span these lists know about, for a sweep that wants to finish
    // rather than wait to be asked.
    pub fn all(&self) -> Vec<SpanId> {
        let mut out = Vec::new();
        for class in 0..=classes::COUNT {
            for side in 0..2 {
                out.extend(self.partial[class][side].iter().copied());
                out.extend(self.full[class][side].iter().copied());
            }
        }
        out
    }

    // A span that turned out to be empty after a sweep goes back to the heap,
    // so that its pages can become a span of some other class. Without this a
    // program that allocates a great many of one size and then a great many of
    // another would hold both at once for ever.
    pub fn drop_empty(&mut self, heap: &mut Heap, id: SpanId) {
        let held = heap.span(id);
        let (class, side) = (held.class, which(held.scan));
        self.partial[class][side].retain(|&one| one != id);
        self.full[class][side].retain(|&one| one != id);
        heap.release(id);
    }
}

impl Default for Central {
    fn default() -> Central {
        Central::new()
    }
}

// ---- What one mutator allocates out of -------------------------------------

pub struct Cache {
    // The span being allocated out of, per class, per scanned-ness.
    held:     Vec<[Option<SpanId>; 2]>,
    // The block small pointer-free objects are being packed into, and how far
    // into it the last one reached. Nought for none.
    pub tiny: usize,
    pub used: usize,
}

impl Cache {
    pub fn new() -> Cache {
        Cache { held: vec![[None, None]; classes::COUNT + 1], tiny: 0, used: 0 }
    }

    pub fn holding(&self, class: usize, scan: bool) -> Option<SpanId> {
        self.held[class][which(scan)]
    }

    pub fn hold(&mut self, class: usize, scan: bool, id: Option<SpanId>) {
        self.held[class][which(scan)] = id;
    }

    // Everything the cache is sitting on, which a sweep has to reach as well:
    // a span in a cache is in no central list, so nothing else would find it.
    pub fn all(&self) -> Vec<SpanId> {
        self.held.iter().flatten().filter_map(|held| *held).collect()
    }

    // What a collection has to undo. The block being packed into may have died
    // in the cycle that just ended, and carrying on filling it would be
    // writing into freed room.
    pub fn forget_tiny(&mut self) {
        self.tiny = 0;
        self.used = 0;
    }
}

impl Default for Cache {
    fn default() -> Cache {
        Cache::new()
    }
}

#[cfg(test)]
mod tests;
