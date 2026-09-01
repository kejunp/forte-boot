// `Map` and `Set`: the ones that keep their keys in order.
//
// "A map or set written without it keeps its keys in order" (§8), so the
// unhashed kind is not merely an unhashed hash map -- the order is part of
// what it is, and walking one has to yield the keys in it.
//
// **Entries in one sorted run, found by halving.** Not a B-tree, and the
// reason is the cursor rather than the data structure. The protocol the
// compiler emits is an *ordinal*: `mir::lower::calls` starts the cursor at -1
// and steps it, so `elem(it, k)` has to answer with the k-th entry in order.
// A sorted run answers that by indexing. A B-tree answers it only if every
// node carries the size of its subtree, which is a real structure -- an
// order-statistic tree -- and is a great deal more code than a binary search
// for an advantage that shows up only in the cost of inserting.
//
// And that cost is what this gives up: inserting in the middle moves
// everything after it, so building a map of n entries is quadratic. For a
// literal, which is what builds one today, n is what somebody typed. For a map
// built a key at a time in a loop, it is not, and this is the file to replace
// when that happens -- the order-statistic tree above is the replacement, and
// the interface it would have to offer is the four functions below.

use std::cmp::Ordering;

use super::super::shape::Shape;
use super::keys::{self, Word};

pub struct Ordered {
    // Keys and their values, lowest key first. Two runs and not one run of
    // pairs, so that a search touches only the keys.
    keys:   Vec<Word>,
    values: Vec<Word>,
}

impl Ordered {
    pub fn new() -> Ordered {
        Ordered { keys: Vec::new(), values: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    // Where a key is, or where it would go.
    fn find(&self, key: Word, shape: Shape) -> Result<usize, usize> {
        let mut low = 0;
        let mut high = self.keys.len();
        while low < high {
            let at = (low + high) / 2;
            match keys::order(self.keys[at], key, shape) {
                Ordering::Less => low = at + 1,
                Ordering::Greater => high = at,
                Ordering::Equal => return Ok(at),
            }
        }
        Err(low)
    }

    // Inserting a key that is already here writes over its value rather than
    // adding a second entry, which is what makes a map a map. The key that
    // stays is the one that was already there; they are equal, so which of the
    // two is kept can only matter to something that can tell equal keys apart,
    // and nothing can.
    pub fn put(&mut self, key: Word, value: Word, shape: Shape) {
        match self.find(key, shape) {
            Ok(at) => self.values[at] = value,
            Err(at) => {
                self.keys.insert(at, key);
                self.values.insert(at, value);
            }
        }
    }

    pub fn get(&self, key: Word, shape: Shape) -> Option<Word> {
        self.find(key, shape).ok().map(|at| self.values[at])
    }

    pub fn has(&self, key: Word, shape: Shape) -> bool {
        self.find(key, shape).is_ok()
    }

    // ---- Walking it --------------------------------------------------------

    // The cursor is the ordinal, so all three of these are what they look
    // like. `step` from -1 gives nought, which is the contract the lowering
    // fixed when it made `IterStart` a constant.
    pub fn step(&self, at: i64) -> i64 {
        at + 1
    }

    pub fn valid(&self, at: i64) -> bool {
        at >= 0 && (at as usize) < self.keys.len()
    }

    pub fn at(&self, at: i64) -> Option<(Word, Word)> {
        let held = usize::try_from(at).ok()?;
        Some((*self.keys.get(held)?, *self.values.get(held)?))
    }

    pub fn key_at(&self, at: i64) -> Option<Word> {
        self.at(at).map(|held| held.0)
    }

    // ---- What the collector has to see -------------------------------------

    pub fn roots(&self, key: Shape, value: Option<Shape>, out: &mut Vec<usize>) {
        for held in &self.keys {
            keys::roots(*held, key, out);
        }
        if let Some(value) = value {
            for held in &self.values {
                keys::roots(*held, value, out);
            }
        }
    }
}

impl Default for Ordered {
    fn default() -> Ordered {
        Ordered::new()
    }
}

#[cfg(test)]
mod tests;
