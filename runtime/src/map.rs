// The map, in both of the kinds the language has.
//
// §8 says a map is "syntax for a type a library declares", and that is the
// right answer: `{1: 2}` builds a `Map<K, V>` that somebody wrote, the way
// `[1, 2]` builds an array. But no library exists, and there cannot be one
// until the language can write a container that grows -- §3 says as much, and
// the growing container is named there as the thing a library is expected to
// provide and cannot yet. Meanwhile `mir::lower::calls` already emits
// `__rt_map_new` and `__rt_map_insert`, so something has to be on the other
// end of those.
//
// So this stands in for a library, and it should be deleted the day one can be
// written. What is here is deliberately shaped like something a library would
// have: no part of the collector knows what a map is except through `roots`
// below, and no part of the compiler knows what this does except through the
// four symbols.
//
//   `Map<K, V>`      keys in order, `ordered`
//   `HashMap<K, V>`  keys in the table's own order, `hashed`
//
// **Which one you get is which one you named**, not a flag on one
// implementation -- that is §8's decision and it is followed here by there
// being two structures rather than one with a branch.
//
// A handle is a number and not an address. `__rt_map_new` gives back an index
// into a list the runtime keeps, which costs a bounds check on every operation
// and buys two things: the handle stays valid however the list is reallocated,
// and a handle that was never given out is caught rather than dereferenced.
// The second matters more than it looks -- the register the compiler hands
// back is one it also uses for addresses, and the day something passes the
// wrong one, a number that is not an index is a message and an address that is
// not a map is a crash somewhere else.

pub mod hashed;
pub mod keys;
pub mod ordered;

use super::shape::Shape;
use super::{alloc, Runtime};
use hashed::Hashed;
use keys::Word;
use ordered::Ordered;

enum Store {
    Ordered(Ordered),
    Hashed(Hashed),
}

pub struct Table {
    store: Store,
    key:   Shape,
    // A set is a map with nothing on the other side, which is what lets both
    // of them be this one structure. Everything about a key is the hard part
    // and a set has all of it.
    value: Option<Shape>,
    // Room for the pair that walking one yields, allocated once and written
    // over at each turn.
    //
    // The alternative is allocating a pair per turn of the loop, which would
    // make walking a map of n entries n allocations -- and every one of them
    // garbage by the next turn. The lowering reads the pair straight into the
    // loop's binding before it steps, so one is enough. It is written down
    // because it is the one place here where a value handed to the program is
    // not the program's to keep.
    pair:  usize,
}

impl Table {
    pub fn new(rt: &mut Runtime, hashed: bool, key: Shape, value: Option<Shape>) -> Table {
        let store =
            if hashed { Store::Hashed(Hashed::new()) } else { Store::Ordered(Ordered::new()) };
        // Only a map yields a pair; a set yields the element itself.
        let pair = if value.is_some() { alloc::kept(rt, 16) } else { 0 };
        Table { store, key, value, pair }
    }

    pub fn len(&self) -> usize {
        match &self.store {
            Store::Ordered(held) => held.len(),
            Store::Hashed(held) => held.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn hashed(&self) -> bool {
        matches!(self.store, Store::Hashed(_))
    }

    // ---- Putting something in ----------------------------------------------

    pub fn key_shape(&self) -> Shape {
        self.key
    }

    pub fn value_shape(&self) -> Option<Shape> {
        self.value
    }

    // A key and a value that have already been copied into the runtime's own
    // room. Kept apart from the copying because the copying allocates, and
    // allocating while holding a borrow of the list the table is in is what
    // the two-step below is avoiding.
    pub fn put_kept(&mut self, key: Word, value: Word) {
        let shape = self.key;
        match &mut self.store {
            Store::Ordered(store) => store.put(key, value, shape),
            Store::Hashed(store) => store.put(key, value, shape),
        }
    }

    pub fn get(&self, key: Word) -> Option<Word> {
        match &self.store {
            Store::Ordered(held) => held.get(key, self.key),
            Store::Hashed(held) => held.get(key, self.key),
        }
    }

    pub fn has(&self, key: Word) -> bool {
        match &self.store {
            Store::Ordered(held) => held.has(key, self.key),
            Store::Hashed(held) => held.has(key, self.key),
        }
    }

    // ---- Walking it --------------------------------------------------------

    pub fn step(&self, at: i64) -> i64 {
        match &self.store {
            Store::Ordered(held) => held.step(at),
            Store::Hashed(held) => held.step(at),
        }
    }

    pub fn valid(&self, at: i64) -> bool {
        match &self.store {
            Store::Ordered(held) => held.valid(at),
            Store::Hashed(held) => held.valid(at),
        }
    }

    fn entry(&self, at: i64) -> Option<(Word, Word)> {
        match &self.store {
            Store::Ordered(held) => held.at(at),
            Store::Hashed(held) => held.at(at),
        }
    }

    // What one turn of a `for` over this yields.
    //
    // A map yields the address of a pair, because `(K, V)` is a tuple and a
    // tuple is reached by its address like every other aggregate. A set yields
    // the element as the register held it -- the value itself for something
    // direct, its address for something not.
    pub fn elem(&self, at: i64) -> Word {
        let Some((key, value)) = self.entry(at) else { return 0 };
        let Some(_) = self.value else { return key };
        if self.pair != 0 {
            unsafe {
                *(self.pair as *mut usize) = key;
                *((self.pair + 8) as *mut usize) = value;
            }
        }
        self.pair
    }

    // ---- What the collector has to see -------------------------------------

    // Every word in here that might be an address. The collector cannot reach
    // these any other way: a key copied into the heap is reachable only
    // through this structure, and this structure is not one the shape system
    // describes -- it is the runtime's own.
    pub fn roots(&self) -> Vec<usize> {
        let mut out = Vec::new();
        if self.pair != 0 {
            out.push(self.pair);
        }
        match &self.store {
            Store::Ordered(held) => held.roots(self.key, self.value, &mut out),
            Store::Hashed(held) => held.roots(self.key, self.value, &mut out),
        }
        out
    }
}

// `__rt_map_insert`, less the looking up of the handle.
//
// The key and the value are copied out of the caller's frame first. What the
// caller passed for an indirect type is the address of a slot that is gone
// when the call returns, so keeping the word would be keeping a pointer into a
// frame that no longer exists.
//
// Two steps and two lookups, because the copying allocates and allocating may
// collect, and a collection walks the very list the table is in.
pub fn insert(rt: &mut Runtime, which: usize, key: Word, value: Word) {
    let Some(held) = rt.tables.get(which) else { return };
    let (kshape, vshape) = (held.key, held.value);
    let key = keys::take(rt, key, kshape);
    let value = match vshape {
        Some(shape) => keys::take(rt, value, shape),
        None => 0,
    };
    if let Some(held) = rt.tables.get_mut(which) {
        held.put_kept(key, value);
    }
}

#[cfg(test)]
mod tests;
