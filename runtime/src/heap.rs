// The heap: every page the runtime has, and which span each of them belongs to.
//
//     mem   ->   heap   ->   cache   ->   alloc
//     pages      spans       one span     an object
//                            per class
//
// Go's three levels, and they are three because each answers a question the
// one below it should not have to ask twice. This file is the bottom of the
// three: it takes reservations from `mem`, cuts runs of pages out of them, and
// remembers what is where. Above it `cache` keeps one span per size class so
// that the common allocation touches nothing shared, and `alloc` is the path
// itself.
//
// The one question everything else leans on is `holding`: given a word that
// might be an address, which object -- if any -- is it inside. A conservative
// root scan asks it once per word of the stack, so it is the operation whose
// cost sets the cost of a collection. It is three steps and no search: the
// arena an address falls in is a shift, the page inside the arena is a shift,
// and the page says which span; then the span's own arithmetic gives the
// object. That is why arenas are aligned to their own size and why a span is
// never allowed to straddle two of them.
//
// The page allocator underneath is *not* Go's. Go keeps a radix tree over the
// whole address space with summaries at each level, so that finding a run of
// N free pages is a descent rather than a walk. What is here is a sorted list
// of free runs and a first fit, which is the same answer computed the slow way
// -- and slow here means proportional to how many separate free runs there
// are, which is small until a program has freed a great deal in a scattered
// pattern. It is the piece to replace first if a heap ever gets big enough to
// notice, and the reason it is not written that way now is that a radix tree
// would be the largest thing in the runtime and would be justified by nothing
// measured.

use super::mem::{self, ARENA, ARENA_SHIFT, PAGE};

pub mod cache;
pub mod classes;
pub mod large;
pub mod span;

use span::{Span, SpanId};

// What a page table holds where no span owns the page.
const NOBODY: usize = usize::MAX;

// A run of pages nothing holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Run {
    at:     usize,
    pages:  usize,
    region: usize,
}

// One arena's worth of address, and what owns each of its pages.
struct Arena {
    at:    usize,
    pages: Vec<usize>,
}

pub struct Heap {
    arenas:       Vec<Arena>,
    // The arena number an address falls in, which arena that is, and which
    // reservation it came out of. Sorted, so finding one is a search over a
    // list that is a handful long.
    index:        Vec<(usize, usize, usize)>,
    spans:        Vec<Span>,
    // Spans that were released and whose place in `spans` can be used again,
    // so that a program allocating and freeing in a loop does not grow this
    // list without bound.
    spare:        Vec<SpanId>,
    // Runs of pages nothing holds, lowest address first. Each says which
    // reservation it came out of, because two runs that touch are only one
    // run when they came from the same one.
    free:         Vec<Run>,
    // How many reservations have been made, which is what numbers them.
    regions:      usize,
    // How many bytes of objects are handed out, which is what pacing is
    // measured against, and how many the runtime has taken from the kernel.
    pub live:     usize,
    pub reserved: usize,
}

impl Heap {
    pub fn new() -> Heap {
        Heap {
            arenas: Vec::new(),
            index: Vec::new(),
            spans: Vec::new(),
            spare: Vec::new(),
            free: Vec::new(),
            regions: 0,
            live: 0,
            reserved: 0,
        }
    }

    // ---- Where an address is -----------------------------------------------

    // Which arena holds it, if any. This is the first of the three steps and
    // the only one that is a search rather than a shift, which is what the
    // number of arenas being small buys.
    fn arena_of(&self, addr: usize) -> Option<usize> {
        let key = addr >> ARENA_SHIFT;
        let at = self.index.binary_search_by_key(&key, |held| held.0).ok()?;
        Some(self.index[at].1)
    }

    // Which reservation an address came out of, for deciding whether two free
    // runs that touch are really one.
    fn region_of(&self, addr: usize) -> usize {
        let key = addr >> ARENA_SHIFT;
        match self.index.binary_search_by_key(&key, |held| held.0) {
            Ok(at) => self.index[at].2,
            Err(_) => usize::MAX,
        }
    }

    pub fn span_at(&self, addr: usize) -> Option<SpanId> {
        let arena = &self.arenas[self.arena_of(addr)?];
        let page = (addr - arena.at) / PAGE;
        let held = *arena.pages.get(page)?;
        if held == NOBODY { None } else { Some(held) }
    }

    // The question the marker asks about every word it finds: is this an
    // address of something on the heap, and if so of what. `None` for a word
    // that is a number, an address of something on the stack, or an address in
    // a part of a span no object covers.
    pub fn holding(&self, addr: usize) -> Option<(SpanId, usize)> {
        let id = self.span_at(addr)?;
        let held = &self.spans[id];
        let at = held.holding(addr)?;
        if !held.taken(at) {
            return None;
        }
        Some((id, at))
    }

    pub fn span(&self, id: SpanId) -> &Span {
        &self.spans[id]
    }

    pub fn span_mut(&mut self, id: SpanId) -> &mut Span {
        &mut self.spans[id]
    }

    pub fn spans(&self) -> usize {
        self.spans.len()
    }

    // Every span that is in use, for the passes that have to walk all of them
    // -- sweeping what the allocator never came back to, and counting.
    pub fn all(&self) -> Vec<SpanId> {
        (0..self.spans.len()).filter(|id| self.spans[*id].pages > 0).collect()
    }

    // ---- Making a span -----------------------------------------------------

    pub fn span_of_class(&mut self, class: usize, scan: bool) -> Option<SpanId> {
        let pages = classes::pages_of(class);
        self.make(pages, class, scan)
    }

    // A span for one object too big to share. It is rounded up to whole pages,
    // and what is left over at the end is the object's as far as anything here
    // is concerned -- there is nothing else in the span to give it to.
    pub fn span_of_bytes(&mut self, bytes: usize, scan: bool) -> Option<SpanId> {
        self.make(bytes.div_ceil(PAGE).max(1), 0, scan)
    }

    fn make(&mut self, pages: usize, class: usize, scan: bool) -> Option<SpanId> {
        let at = match self.take_pages(pages) {
            Some(at) => at,
            None => {
                self.grow(pages)?;
                self.take_pages(pages)?
            }
        };
        let held = Span::new(at, pages, class, scan);
        let id = match self.spare.pop() {
            Some(id) => {
                self.spans[id] = held;
                id
            }
            None => {
                self.spans.push(held);
                self.spans.len() - 1
            }
        };
        self.own(at, pages, id);
        Some(id)
    }

    // Giving a span's pages back, which happens when a sweep finds nothing
    // left in it. The span itself keeps its place in the list and is marked
    // empty, so that an id nothing has finished with does not come back as
    // something else underneath it.
    pub fn release(&mut self, id: SpanId) {
        let (at, pages) = (self.spans[id].at, self.spans[id].pages);
        if pages == 0 {
            return;
        }
        let region = self.region_of(at);
        self.own(at, pages, NOBODY);
        self.spans[id].pages = 0;
        self.spans[id].count = 0;
        self.give_pages(at, pages, region);
        self.spare.push(id);
    }

    // Page by page rather than in one stretch, because a run big enough for a
    // large object may cross from one arena into the next. It can only do that
    // inside a single reservation, which is what makes the crossing safe: the
    // two arenas really are next to each other.
    fn own(&mut self, at: usize, pages: usize, id: usize) {
        let mut page = at;
        for _ in 0..pages {
            if let Some(which) = self.arena_of(page) {
                let arena = &mut self.arenas[which];
                let held = (page - arena.at) / PAGE;
                arena.pages[held] = id;
            }
            page += PAGE;
        }
    }

    // ---- Pages -------------------------------------------------------------

    // First fit. The list is kept lowest address first, which makes giving a
    // run back a matter of finding where it goes and looking at the two
    // neighbours -- and keeping the heap compact at the low end, which is what
    // stops a long-running program from spreading over the address space.
    fn take_pages(&mut self, pages: usize) -> Option<usize> {
        let which = self.free.iter().position(|held| held.pages >= pages)?;
        let run = self.free[which];
        if run.pages == pages {
            self.free.remove(which);
        } else {
            self.free[which] =
                Run { at: run.at + pages * PAGE, pages: run.pages - pages, region: run.region };
        }
        Some(run.at)
    }

    fn give_pages(&mut self, at: usize, pages: usize, region: usize) {
        let which = self.free.partition_point(|held| held.at < at);
        self.free.insert(which, Run { at, pages, region });

        // Coalescing, but never across a reservation: two of them that happen
        // to have come back next to each other are still two, and the kernel
        // may hand the space between them to something else.
        if which + 1 < self.free.len() {
            self.join(which);
        }
        if which > 0 {
            self.join(which - 1);
        }
    }

    fn join(&mut self, at: usize) {
        let (one, two) = (self.free[at], self.free[at + 1]);
        if one.region == two.region && one.at + one.pages * PAGE == two.at {
            self.free[at] = Run { at: one.at, pages: one.pages + two.pages, region: one.region };
            self.free.remove(at + 1);
        }
    }

    // One more reservation. Big enough for what was asked for, which for a
    // large object may be more than an arena.
    fn grow(&mut self, pages: usize) -> Option<()> {
        let want = mem::up(pages * PAGE, ARENA).max(ARENA);
        let at = mem::map_aligned(want, ARENA)? as usize;
        self.reserved += want;
        let region = self.regions;
        self.regions += 1;

        // One arena's worth of page table per arena's worth of address, so
        // that the shift from an address to an arena stays a shift.
        for step in 0..want / ARENA {
            let held = at + step * ARENA;
            self.arenas.push(Arena { at: held, pages: vec![NOBODY; ARENA / PAGE] });
            let key = held >> ARENA_SHIFT;
            let which = self.index.partition_point(|one| one.0 < key);
            self.index.insert(which, (key, self.arenas.len() - 1, region));
        }
        // The whole reservation as one run, so that an object bigger than an
        // arena still has somewhere contiguous to go.
        self.give_pages(at, want / PAGE, region);
        Some(())
    }
}

impl Default for Heap {
    fn default() -> Heap {
        Heap::new()
    }
}

// Giving the reservations back. A program's own heap outlives it and this
// never runs for one; it is here for the tests, each of which builds a heap of
// its own and would otherwise leave every arena it touched mapped for the rest
// of the run.
impl Drop for Heap {
    fn drop(&mut self) {
        let mut done: Vec<usize> = Vec::new();
        for arena in &self.arenas {
            if !done.contains(&arena.at) {
                done.push(arena.at);
                mem::unmap(arena.at as *mut u8, ARENA);
            }
        }
    }
}

#[cfg(test)]
mod tests;
