// The set, in both of the kinds the language has.
//
// A set is a map with nothing on the other side of the key, and that is not a
// convenient framing -- it is what a set is. Everything difficult about a map
// is about the key: copying it out of the caller's frame, ordering it, hashing
// it, keeping it where the collector can see it. A value is carried alongside
// and is not asked any questions. So a set is `map::Table` with no value
// shape, and the two share every line of that.
//
// What a set does not share is what walking one yields. A map's turn is a
// `(K, V)` pair and has to be handed over by address; a set's turn is the
// element, which is a value like any other and reaches the program the way the
// register held it. That is the whole of this file.
//
// `Set<T>` and `HashSet<T>` are separate types in the language and separate
// structures here, for the reason §8 gives: "which one you named says how it
// behaves". The unhashed one walks its elements in order.

use super::map::{keys::Word, Table};
use super::shape::Shape;
use super::Runtime;

pub struct Held {
    table: Table,
}

impl Held {
    pub fn new(rt: &mut Runtime, hashed: bool, elem: Shape) -> Held {
        Held { table: Table::new(rt, hashed, elem, None) }
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    pub fn hashed(&self) -> bool {
        self.table.hashed()
    }

    pub fn has(&self, elem: Word) -> bool {
        self.table.has(elem)
    }

    // Adding something that is already here does nothing, which is what makes
    // a set a set. It falls out of the map underneath: putting a key that is
    // already there writes over its value, and there is no value.
    pub fn put(rt: &mut Runtime, which: usize, elem: Word) {
        let Some(held) = rt.sets.get(which) else { return };
        // Copied before the table is reached for, not after: copying allocates
        // and allocating may collect, and a collection walks the list this
        // table is in.
        let shape = held.table.key_shape();
        let elem = super::map::keys::take(rt, elem, shape);
        if let Some(held) = rt.sets.get_mut(which) {
            held.table.put_kept(elem, 0);
        }
    }

    // ---- Walking it --------------------------------------------------------

    pub fn step(&self, at: i64) -> i64 {
        self.table.step(at)
    }

    pub fn valid(&self, at: i64) -> bool {
        self.table.valid(at)
    }

    pub fn elem(&self, at: i64) -> Word {
        self.table.elem(at)
    }

    pub fn roots(&self) -> Vec<usize> {
        self.table.roots()
    }
}

#[cfg(test)]
mod tests;
