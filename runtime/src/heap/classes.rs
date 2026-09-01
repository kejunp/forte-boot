// The sizes an object is allowed to be.
//
// An allocator that gave out exactly what was asked for would have a free list
// per size and a fragmented heap. Go's answer, and this one, is that there are
// sixty-seven sizes: a request is rounded up to the smallest that holds it, and
// every object in a span is that size. Then a span needs no per-object header,
// freeing is putting an index back on a list, and the mark bits are one bit per
// object at a fixed stride.
//
// **The table is Go's, copied whole.** It is not a table anyone should derive
// again: each row is a size and how many pages a span of that size takes, and
// the pair is chosen together so that the tail left over at the end of the span
// is small *and* the gap up from the previous class is small. Those two pull
// against each other, and the sixty-seven rows are the result of a search over
// both. Picking round numbers instead -- powers of two, or every multiple of
// sixteen -- is worse in a way that does not show up until a program's live
// heap is measured against what it asked for.
//
// The two lookup tables underneath are Go's too. A search over sixty-seven rows
// would be seven comparisons on the busiest path in the runtime; an index into
// an array is one. They are built here at compile time from the table above
// them, so the three cannot disagree.

use super::super::mem::PAGE;

// The largest object that gets a class at all. Anything bigger gets a span to
// itself -- see `heap::large`.
pub const MAX: usize = 32768;

// What a small pointer-free object is packed into. Several of them share one
// sixteen-byte block, which is worth doing only because such an object has
// nothing in it the marker would ever look at: a block is free when all of its
// tenants are, and none of them needs to be told apart from the others.
pub const TINY: usize = 16;

// How many classes there are, not counting the nought that means "no class".
pub const COUNT: usize = 67;

// Every class: how many bytes an object of it takes, and how many pages a span
// of it is. Row nought is not a class; it is there so that a class number
// indexes this directly.
pub const CLASSES: [(usize, usize); COUNT + 1] = [
    (0, 0),
    (8, 1),
    (16, 1),
    (24, 1),
    (32, 1),
    (48, 1),
    (64, 1),
    (80, 1),
    (96, 1),
    (112, 1),
    (128, 1),
    (144, 1),
    (160, 1),
    (176, 1),
    (192, 1),
    (208, 1),
    (224, 1),
    (240, 1),
    (256, 1),
    (288, 1),
    (320, 1),
    (352, 1),
    (384, 1),
    (416, 1),
    (448, 1),
    (480, 1),
    (512, 1),
    (576, 1),
    (640, 1),
    (704, 1),
    (768, 1),
    (896, 1),
    (1024, 1),
    (1152, 1),
    (1280, 1),
    (1408, 2),
    (1536, 1),
    (1792, 2),
    (2048, 1),
    (2304, 2),
    (2688, 1),
    (3072, 3),
    (3200, 2),
    (3456, 3),
    (4096, 1),
    (4864, 3),
    (5376, 2),
    (6144, 3),
    (6528, 4),
    (6784, 5),
    (6912, 6),
    (8192, 1),
    (9472, 7),
    (9728, 6),
    (10240, 5),
    (10880, 4),
    (12288, 3),
    (13568, 5),
    (14336, 7),
    (16384, 2),
    (18432, 9),
    (19072, 7),
    (20480, 5),
    (21760, 8),
    (24576, 3),
    (27264, 10),
    (28672, 7),
    (32768, 4),
];

// ---- Finding the class -----------------------------------------------------

// Where the two tables meet. Below this a size is looked up every eight bytes
// and above it every hundred and twenty-eight, which is why there are two: one
// table at the fine step would be four thousand entries to say the same thing.
const SMALL: usize = 1024;
const SMALL_STEP: usize = 8;
const LARGE_STEP: usize = 128;

const SMALL_ROWS: usize = SMALL / SMALL_STEP + 1;
const LARGE_ROWS: usize = (MAX - SMALL) / LARGE_STEP + 1;

static TO_CLASS_SMALL: [u8; SMALL_ROWS] = small_table();
static TO_CLASS_LARGE: [u8; LARGE_ROWS] = large_table();

const fn holding(bytes: usize) -> u8 {
    let mut c = 1;
    while c <= COUNT {
        if CLASSES[c].0 >= bytes {
            return c as u8;
        }
        c += 1;
    }
    0
}

const fn small_table() -> [u8; SMALL_ROWS] {
    let mut out = [0u8; SMALL_ROWS];
    let mut i = 1;
    while i < SMALL_ROWS {
        out[i] = holding(i * SMALL_STEP);
        i += 1;
    }
    out
}

const fn large_table() -> [u8; LARGE_ROWS] {
    let mut out = [0u8; LARGE_ROWS];
    let mut i = 0;
    while i < LARGE_ROWS {
        out[i] = holding(SMALL + i * LARGE_STEP);
        i += 1;
    }
    out
}

// The class an object of this many bytes goes in, or `None` where it is too
// big to share a span with anything.
pub fn class_of(bytes: usize) -> Option<usize> {
    if bytes == 0 {
        return Some(1);
    }
    if bytes > MAX {
        return None;
    }
    let held = if bytes <= SMALL {
        TO_CLASS_SMALL[bytes.div_ceil(SMALL_STEP)]
    } else {
        TO_CLASS_LARGE[(bytes - SMALL).div_ceil(LARGE_STEP)]
    };
    Some(held as usize)
}

// ---- What a class is -------------------------------------------------------

pub fn size_of(class: usize) -> usize {
    CLASSES[class].0
}

pub fn pages_of(class: usize) -> usize {
    CLASSES[class].1
}

pub fn bytes_of(class: usize) -> usize {
    CLASSES[class].1 * PAGE
}

// How many objects fit, which is what a span's free list and its mark bits are
// both as long as. The remainder is the tail waste the table was chosen to
// keep small, and it is left unused rather than given to the last object.
pub fn count_of(class: usize) -> usize {
    if class == 0 {
        return 0;
    }
    bytes_of(class) / size_of(class)
}

#[cfg(test)]
mod tests;
