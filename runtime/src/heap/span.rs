// A run of pages carved into objects of one size, and the bits that say what
// is going on in it.
//
// This is the unit the whole heap is described in. Every object in a span is
// the same size, which is what lets a span hold no per-object header: what
// would have been a header is instead a bit at a fixed index in one of the
// span's bitmaps, and the index is the object's address less the span's over
// the size. That arithmetic is also what answers the question the marker asks
// most -- given a word that might be an address, which object is it inside --
// and it answers it for an address in the *middle* of an object as cheaply as
// for one at the start, which is what makes a conservative scan affordable.
//
// Three bitmaps, and they are three different questions.
//
//   `alloc`  which objects are handed out. Set when one is taken, and reset
//            wholesale at a sweep to whatever survived.
//   `marks`  which the marker has reached this cycle. Cleared at the start of
//            one. The difference between this and `alloc` at the end of a
//            cycle is exactly the garbage.
//   `ptrs`   which *words* of each object are pointers, laid end to end, one
//            object's worth after another. This is the thing that makes the
//            heap scan precise rather than conservative, and it is written
//            when the object is allocated because that is the only moment
//            anything knows the type.
//
// A span whose objects hold no pointers has no `ptrs` at all and is never
// scanned. That split is worth more than any other single thing here: a run of
// bytes, a string's characters, an array of numbers -- the common large
// objects are all pointer-free, and a collector that walked them would spend
// most of a cycle reading numbers.
//
// There is no free list. The next object to hand out is found by looking for a
// nought in `alloc` from where the last one was found, which is Go's design
// and is faster than a list for the reason that surprises people: it touches
// only the bitmap, and a free list touches the free memory itself, which is
// exactly the memory that is not in cache.

use super::classes;

// ---- Bits ------------------------------------------------------------------

// A bitmap of a fixed length. Nothing here is clever; it is written out rather
// than pulled in because the two operations that matter -- counting what is
// set, and finding the next nought from somewhere -- both want to work a word
// at a time, and a bitmap that hid its words could not.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bits {
    words: Vec<u64>,
    len:   usize,
}

impl Bits {
    pub fn new(len: usize) -> Bits {
        Bits { words: vec![0; len.div_ceil(64)], len }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get(&self, at: usize) -> bool {
        at < self.len && self.words[at / 64] >> (at % 64) & 1 == 1
    }

    pub fn set(&mut self, at: usize) {
        if at < self.len {
            self.words[at / 64] |= 1 << (at % 64);
        }
    }

    pub fn unset(&mut self, at: usize) {
        if at < self.len {
            self.words[at / 64] &= !(1 << (at % 64));
        }
    }

    // Whether it was not set before, which is what a marker wants: the answer
    // says whether this is the first time anything reached the object, and so
    // whether its own contents still need looking at.
    pub fn raise(&mut self, at: usize) -> bool {
        if at >= self.len || self.get(at) {
            return false;
        }
        self.set(at);
        true
    }

    pub fn none(&mut self) {
        for word in &mut self.words {
            *word = 0;
        }
    }

    pub fn count(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    // The first nought at or after `from`, a word at a time. The mask is what
    // makes "at or after" free: everything below `from` is turned to a one so
    // that `trailing_zeros` cannot land on it.
    pub fn empty_from(&self, from: usize) -> Option<usize> {
        let mut at = from;
        while at < self.len {
            let word = at / 64;
            let held = !self.words[word] & (u64::MAX << (at % 64));
            if held != 0 {
                let found = word * 64 + held.trailing_zeros() as usize;
                // Past the end is the tail of the last word, which is nought
                // because nothing ever set it and is not a free object.
                return if found < self.len { Some(found) } else { None };
            }
            at = (word + 1) * 64;
        }
        None
    }

    // What is set here and not there, which is how a sweep is written: the
    // objects that were allocated and were not marked are the ones to free.
    pub fn without(&self, other: &Bits) -> usize {
        self.words
            .iter()
            .zip(other.words.iter())
            .map(|(a, b)| (a & !b).count_ones() as usize)
            .sum()
    }

    pub fn copy_from(&mut self, other: &Bits) {
        self.words.copy_from_slice(&other.words);
    }
}

// ---- A span ----------------------------------------------------------------

pub type SpanId = usize;

#[derive(Debug, Clone)]
pub struct Span {
    // Where it begins, and how far it goes.
    pub at:    usize,
    pub pages: usize,
    // Which size class, or nought for an object big enough to have the span to
    // itself -- there is no class for those and `size` is what was asked for.
    pub class: usize,
    pub size:  usize,
    pub count: usize,
    // Whether anything in here can hold a pointer. A span where nothing can is
    // never read by the marker at all.
    pub scan:  bool,
    // How many words one object is, which is how far apart two objects' runs
    // of pointer bits are.
    pub words: usize,
    pub alloc: Bits,
    pub marks: Bits,
    pub ptrs:  Bits,
    // Where the search for a free object starts. Everything below it is taken,
    // which is true because a sweep is what puts it back to nought.
    pub next:  usize,
    // The cycle this span was last swept in. A span whose number is behind the
    // heap's has garbage in it that is still counted as allocated, and the
    // allocator sweeps it before taking anything out.
    pub swept: u32,
}

impl Span {
    // A large object has no class, so the span is the object: one of it, as
    // many bytes as the pages it was given.
    pub fn new(at: usize, pages: usize, class: usize, scan: bool) -> Span {
        let whole = pages * super::super::mem::PAGE;
        let size = if class == 0 { whole } else { classes::size_of(class) };
        let count = if class == 0 { 1 } else { classes::count_of(class) };
        let words = size / 8;
        Span {
            at,
            pages,
            class,
            size,
            count,
            scan,
            words,
            alloc: Bits::new(count),
            marks: Bits::new(count),
            // A span nothing scans needs no map of where its pointers are, and
            // for a large object that map is most of a page.
            ptrs: Bits::new(if scan { count * words } else { 0 }),
            next: 0,
            swept: 0,
        }
    }

    pub fn bytes(&self) -> usize {
        self.pages * super::super::mem::PAGE
    }

    pub fn ends(&self) -> usize {
        self.at + self.bytes()
    }

    pub fn base_of(&self, index: usize) -> usize {
        self.at + index * self.size
    }

    // Which object an address is inside, for an address anywhere inside it.
    // The interior case is not an afterthought: a conservative scan of a stack
    // finds addresses that were computed -- a field's, an element's -- far more
    // often than it finds one that happens to be an object's first byte.
    pub fn holding(&self, addr: usize) -> Option<usize> {
        if addr < self.at || addr >= self.at + self.count * self.size {
            return None;
        }
        Some((addr - self.at) / self.size)
    }

    // ---- Handing one out ---------------------------------------------------

    pub fn take(&mut self) -> Option<usize> {
        let at = self.alloc.empty_from(self.next)?;
        self.alloc.set(at);
        self.next = at + 1;
        Some(at)
    }

    pub fn free(&self) -> usize {
        self.count - self.alloc.count()
    }

    pub fn full(&self) -> bool {
        self.alloc.empty_from(self.next).is_none()
    }

    // ---- What the marker reads ---------------------------------------------

    pub fn mark(&mut self, index: usize) -> bool {
        self.marks.raise(index)
    }

    pub fn marked(&self, index: usize) -> bool {
        self.marks.get(index)
    }

    pub fn taken(&self, index: usize) -> bool {
        self.alloc.get(index)
    }

    // Whether word `word` of object `index` holds a pointer. False for every
    // word of a span nothing scans, which is what stops the marker before it
    // starts rather than in the middle.
    pub fn points(&self, index: usize, word: usize) -> bool {
        self.scan && word < self.words && self.ptrs.get(index * self.words + word)
    }

    // Written at the moment of allocation, from the shape the caller passed.
    // `bits` is one bit per word, low bit of byte nought first, which is the
    // order `mir::shape` writes it in.
    pub fn describe(&mut self, index: usize, bits: &[u8], words: usize) {
        if !self.scan {
            return;
        }
        let base = index * self.words;
        for word in 0..self.words {
            let held = word < words && bits.get(word / 8).is_some_and(|b| b >> (word % 8) & 1 == 1);
            if held {
                self.ptrs.set(base + word);
            } else {
                self.ptrs.unset(base + word);
            }
        }
    }

    // ---- Sweeping ----------------------------------------------------------

    // What survived becomes what is allocated, and the marks go back to
    // nothing. The objects that were allocated and not marked are the garbage,
    // and this is the only place they are counted -- nothing walks them and
    // nothing writes to them, which is why a sweep costs the same whether the
    // span was full of garbage or full of survivors.
    pub fn sweep(&mut self, cycle: u32) -> usize {
        let gone = self.alloc.without(&self.marks);
        self.alloc.copy_from(&self.marks);
        self.marks.none();
        self.next = 0;
        self.swept = cycle;
        gone
    }
}

#[cfg(test)]
mod tests;
