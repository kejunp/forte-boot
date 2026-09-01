// What a key is, given only a machine word and a description of it.
//
// The whole difficulty of writing a map for a compiled language is here. The
// call the compiler emits is `__rt_map_insert(map, key, value)` and the key is
// one register: for an `i32` that register holds the number, for a struct it
// holds an address, and nothing in the call says which. `mir::shape` is what
// closes that -- the map was made with a descriptor for its key type, and this
// file is everything that descriptor is used for.
//
// Three questions, and a map needs all three.
//
//   **Keeping it.** The word the caller passed may be the address of a slot in
//   the caller's frame, which is gone when the call returns. So an indirect
//   key is copied into the runtime's own heap and the copy is what is kept.
//   A direct one is the value itself and there is nothing to copy.
//
//   **Ordering it.** `Map` keeps its keys in order (§8: "a map or set written
//   without it keeps its keys in order"), so two keys have to be comparable.
//   What that means is the kind's business: two's complement for a signed
//   number, unsigned for an address, the characters for a string, and the
//   bytes for anything else.
//
//   **Hashing it.** `HashMap` needs a number from a key, and two keys that are
//   equal have to give the same number. FNV-1a, which is short, has no
//   constants to get wrong, and is what a runtime uses before it has anything
//   to measure a better one against. It is not resistant to a chosen-key
//   attack; Go's is, through a per-process seed, and the day this holds keys
//   from outside a program that is the first thing to add.
//
// Comparing two `Opaque` values as bytes is a decision and not an obvious one.
// It says that two structures are the same key when they are the same bytes,
// which is not what the language means by equality -- there is no equality in
// the language yet to mean anything else. Padding between fields makes it
// worse: two structures that a reader would call equal can differ in a byte
// nobody wrote. The allocator clears every object it hands out, which makes
// that true in practice for anything built on the heap, and it is not a
// guarantee. It is written down here rather than left to be found.

use std::cmp::Ordering;

use super::super::shape::{Kind, Shape};
use super::super::{alloc, Runtime};

// A key or a value as the runtime keeps it: one word, which is the value
// itself or the address of the runtime's own copy.
pub type Word = usize;

// The caller's word, made into one the runtime may keep after the call
// returns.
pub fn take(rt: &mut Runtime, word: Word, shape: Shape) -> Word {
    if !shape.indirect() || word == 0 {
        return word;
    }
    let at = alloc::object(rt, shape.bytes().max(1), Some(shape));
    if at != 0 {
        unsafe {
            std::ptr::copy_nonoverlapping(word as *const u8, at as *mut u8, shape.bytes());
        }
    }
    at
}

// ---- Reading one -----------------------------------------------------------

// The bytes of a value, wherever they are. For a direct value they are in the
// word itself, so the word is handed back as a slice of its own address --
// which is why this takes the word by reference.
fn bytes<'a>(word: &'a Word, shape: Shape) -> &'a [u8] {
    let count = shape.bytes().max(1);
    if shape.indirect() {
        if *word == 0 {
            return &[];
        }
        unsafe { std::slice::from_raw_parts(*word as *const u8, count) }
    } else {
        let at = word as *const Word as *const u8;
        unsafe { std::slice::from_raw_parts(at, count.min(8)) }
    }
}

// A string, as the pointer and length it is. `str` is fat -- two words -- so
// the register holds the address of the pair, and what is compared is what the
// first word points at for as far as the second says.
fn text<'a>(word: &'a Word, shape: Shape) -> &'a [u8] {
    if !shape.indirect() {
        // A bare pointer with no length beside it, which is what a string
        // literal used to become. Nothing can be said about how long it is, so
        // it is compared as the address it is.
        return &[];
    }
    if *word == 0 {
        return &[];
    }
    unsafe {
        let pair = *word as *const usize;
        let (at, len) = (*pair, *pair.add(1));
        if at == 0 { &[] } else { std::slice::from_raw_parts(at as *const u8, len) }
    }
}

// A direct value read as the number it is, sign extended from its own width.
// A one-byte `-1` is `0xff` in a register and is less than nought, and reading
// eight bytes of a register that holds one would compare the seven bytes above
// it as well.
fn signed(word: Word, shape: Shape) -> i64 {
    let bits = shape.bytes().clamp(1, 8) * 8;
    if bits == 64 {
        return word as i64;
    }
    let held = word & ((1u64 << bits) - 1) as usize;
    let sign = 1usize << (bits - 1);
    if held & sign != 0 { (held | !((1usize << bits) - 1)) as i64 } else { held as i64 }
}

fn unsigned(word: Word, shape: Shape) -> u64 {
    let bits = shape.bytes().clamp(1, 8) * 8;
    if bits == 64 {
        return word as u64;
    }
    (word & ((1u64 << bits) - 1) as usize) as u64
}

fn floating(word: Word, shape: Shape) -> f64 {
    if shape.bytes() <= 4 {
        f32::from_bits(word as u32) as f64
    } else {
        f64::from_bits(word as u64)
    }
}

// ---- The three questions ---------------------------------------------------

pub fn order(a: Word, b: Word, shape: Shape) -> Ordering {
    match shape.kind() {
        Kind::Signed => signed(a, shape).cmp(&signed(b, shape)),
        Kind::Unsigned | Kind::Pointer => unsigned(a, shape).cmp(&unsigned(b, shape)),
        // Two floats that are not ordered are put in a fixed order rather than
        // left to a comparison that says no. A map has to be able to hold a
        // NaN somewhere, and the somewhere has to be the same place every
        // time or a lookup could not find it.
        Kind::Float => floating(a, shape)
            .partial_cmp(&floating(b, shape))
            .unwrap_or_else(|| floating(a, shape).is_nan().cmp(&floating(b, shape).is_nan())),
        // A string that arrived as a pair is compared by its characters. One
        // that arrived as a bare pointer has no length beside it, so nothing
        // can be said about it but where it is -- which is what a `str`
        // literal used to become, and is why the lowering builds the pair.
        Kind::Str if shape.indirect() => text(&a, shape).cmp(text(&b, shape)),
        Kind::Str => a.cmp(&b),
        Kind::Opaque => bytes(&a, shape).cmp(bytes(&b, shape)),
    }
}

pub fn same(a: Word, b: Word, shape: Shape) -> bool {
    order(a, b, shape) == Ordering::Equal
}

// FNV-1a over whatever the kind says the key's bytes are.
pub fn hash(word: Word, shape: Shape) -> u64 {
    match shape.kind() {
        Kind::Str if shape.indirect() => fnv(text(&word, shape)),
        Kind::Str => fnv(&(word as u64).to_le_bytes()),
        Kind::Opaque => fnv(bytes(&word, shape)),
        // A number is hashed as the number and not as the register: a one-byte
        // key has seven bytes above it that nothing wrote.
        Kind::Signed => fnv(&signed(word, shape).to_le_bytes()),
        Kind::Unsigned | Kind::Pointer => fnv(&unsigned(word, shape).to_le_bytes()),
        // Through the bits, so that a key hashes the same way it compares --
        // except for a nought, which has two spellings and one place in a map.
        Kind::Float => {
            let held = floating(word, shape);
            fnv(&(if held == 0.0 { 0.0 } else { held }).to_bits().to_le_bytes())
        }
    }
}

const SEED: u64 = 0xcbf2_9ce4_8422_2325;
const PRIME: u64 = 0x0000_0100_0000_01b3;

fn fnv(held: &[u8]) -> u64 {
    let mut out = SEED;
    for byte in held {
        out ^= u64::from(*byte);
        out = out.wrapping_mul(PRIME);
    }
    out
}

// ---- What the collector has to see -----------------------------------------

// Every word of a kept key or value that might be an address into the heap.
//
// A copied key is one, and a string's characters are another -- the pair is in
// the heap and what it points at may be too. Everything else is a number, and
// handing a number to the marker costs a lookup that fails.
pub fn roots(word: Word, shape: Shape, out: &mut Vec<usize>) {
    if shape.indirect() && word != 0 {
        out.push(word);
        if shape.kind() == Kind::Str {
            out.push(unsafe { *(word as *const usize) });
        }
    } else if shape.kind() == Kind::Pointer {
        out.push(word);
    }
}

#[cfg(test)]
mod tests;
