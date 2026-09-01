// What the compiler says a type is, read back.
//
// This is the one place the two halves of this project touch. `mir::shape`
// writes these bytes into the constant pool under `__T` and the type's
// spelling; this reads them. Neither can move without the other, and the
// layout below is the whole of the contract -- so it is written out here in
// the same table `mir::shape` writes it from, and the two are meant to be read
// side by side.
//
//      +0   u64   bytes      what one value takes
//      +8   u64   align
//     +16   u64   words      how many words the map below covers
//     +24   u8    kind       how a key is hashed and ordered
//     +25   u8    indirect   whether a register holding one holds its address
//     +26   u8    [6]        nothing, so the map starts on a word
//     +32   u8    []         one bit per word, low bit of byte nought first;
//                            a one means that word holds a pointer
//
// Two questions and not one, and they are separate on purpose.
//
// The **map** is what the collector needs. Without it a heap scan has to treat
// every word as a possible address, which is what the stack scan does and what
// it costs: an integer that happens to look like an address keeps something
// alive. On the heap that is avoidable, because the compiler knew the type,
// and this is how it says so. A shape whose map is empty makes the object
// unscanned, which is the split the whole allocator is built around.
//
// The **kind** is what a map and a set need. Ordering two keys and hashing one
// are questions about what the bytes *mean* -- two's complement, a float's
// sign bit, a string's characters behind a pointer -- and an address plus a
// length cannot answer either. A function pointer per type would be the
// general answer, and it would mean the compiler emitting three routines per
// key type before a map could hold anything. A small closed set of kinds
// covers what a key can actually be in this language and costs a byte.

// How far the map is from the start.
pub const HEADER: usize = 32;

// What the bytes of a value mean, for the two operations that have to know.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    // Bytes and nothing more: compared as bytes, hashed as bytes. A struct, a
    // tuple, an array. Two of these are equal when they are the same bytes,
    // which is not the same question as whether the language would call them
    // equal -- and until the language says what equality is, it is the
    // question that can be answered.
    Opaque,
    Signed,
    Unsigned,
    Float,
    Pointer,
    // A pointer and a length, and what is at the pointer is what matters.
    Str,
}

impl Kind {
    pub fn of(byte: u8) -> Kind {
        match byte {
            1 => Kind::Signed,
            2 => Kind::Unsigned,
            3 => Kind::Float,
            4 => Kind::Pointer,
            5 => Kind::Str,
            _ => Kind::Opaque,
        }
    }

    pub fn byte(self) -> u8 {
        match self {
            Kind::Opaque => 0,
            Kind::Signed => 1,
            Kind::Unsigned => 2,
            Kind::Float => 3,
            Kind::Pointer => 4,
            Kind::Str => 5,
        }
    }
}

// A view onto a descriptor somebody else owns -- the constant pool, which
// outlives everything. Nothing here copies it: a shape is passed once per
// allocation and read once per scan, and copying thirty-two bytes each time to
// avoid a raw pointer would be paying for tidiness on the hottest path there
// is.
#[derive(Debug, Clone, Copy)]
pub struct Shape {
    at: *const u8,
}

unsafe impl Send for Shape {}
unsafe impl Sync for Shape {}

impl Shape {
    // A null shape is a real thing and not a mistake: it is what an allocation
    // that has nothing to say about its contents passes, and it means the same
    // as a shape whose map is empty.
    pub fn at(p: *const u8) -> Option<Shape> {
        if p.is_null() { None } else { Some(Shape { at: p }) }
    }

    fn word(&self, off: usize) -> usize {
        unsafe { (self.at.add(off) as *const u64).read_unaligned() as usize }
    }

    fn byte(&self, off: usize) -> u8 {
        unsafe { *self.at.add(off) }
    }

    pub fn bytes(&self) -> usize {
        self.word(0)
    }

    pub fn align(&self) -> usize {
        self.word(8).max(1)
    }

    pub fn words(&self) -> usize {
        self.word(16)
    }

    pub fn kind(&self) -> Kind {
        Kind::of(self.byte(24))
    }

    pub fn indirect(&self) -> bool {
        self.byte(25) != 0
    }

    // The map itself, as the bytes it is. Handed to `Span::describe`, which is
    // the only thing that reads it more than a word at a time.
    pub fn map(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.at.add(HEADER), self.words().div_ceil(8)) }
    }

    pub fn points(&self, word: usize) -> bool {
        word < self.words() && self.byte(HEADER + word / 8) >> (word % 8) & 1 == 1
    }

    // Whether anything in here is worth the collector's time. A type with no
    // pointers anywhere goes in an unscanned span and is never read again.
    pub fn scan(&self) -> bool {
        self.map().iter().any(|held| *held != 0)
    }
}

// ---- Writing one -----------------------------------------------------------

// The same bytes, built rather than read. This exists for the tests and for
// the runtime's own types -- a map's node holds pointers and has to be
// described to the collector like anything else, and there is no compiler
// emitting a descriptor for something the compiler has never heard of.
pub struct Made {
    held: Vec<u8>,
}

impl Made {
    pub fn new(bytes: usize, align: usize, kind: Kind) -> Made {
        let words = bytes.div_ceil(8);
        let mut held = vec![0u8; HEADER + words.div_ceil(8).max(1)];
        held[0..8].copy_from_slice(&(bytes as u64).to_le_bytes());
        held[8..16].copy_from_slice(&(align as u64).to_le_bytes());
        held[16..24].copy_from_slice(&(words as u64).to_le_bytes());
        held[24] = kind.byte();
        Made { held }
    }

    // Says that the word at this offset holds a pointer. Written in bytes
    // rather than words because every caller has an offset in hand and none of
    // them has a word number.
    pub fn points_at(mut self, offset: usize) -> Made {
        let word = offset / 8;
        if word < self.words() {
            self.held[HEADER + word / 8] |= 1 << (word % 8);
        }
        self
    }

    pub fn indirect(mut self) -> Made {
        self.held[25] = 1;
        self
    }

    fn words(&self) -> usize {
        usize::from_le_bytes(self.held[16..24].try_into().unwrap_or([0; 8]))
    }

    pub fn shape(&self) -> Shape {
        Shape { at: self.held.as_ptr() }
    }

    pub fn bytes(&self) -> &[u8] {
        &self.held
    }
}

#[cfg(test)]
mod tests;
