// `HashMap` and `HashSet`: Go's map, as far as the shape of it goes.
//
// **Buckets of eight, with a byte of the hash kept beside each slot.** That
// pair is the whole design and it is worth saying why. A lookup finds its
// bucket from the low bits of the hash, and then has to find its key among
// eight. Comparing eight keys would mean eight key comparisons, and a key may
// be a string or a structure. So the top byte of each key's hash is kept in
// the bucket, and the eight bytes are compared first: a byte that does not
// match rules that slot out without touching the key at all. Only a slot whose
// byte matches is worth a real comparison, and for a table that is not
// pathologically collided that is one slot.
//
// A byte of nought means the slot is empty, so a real hash's top byte is
// nudged off nought -- one bit of the hash given up to save a second array.
//
// **Overflow buckets rather than probing.** A bucket that fills chains to
// another. The alternative -- open addressing, walking on to the next bucket
// -- makes deletion hard and makes a table's worst case depend on the order
// things were put in it. Go chose chaining and this follows.
//
// Where it departs: **growing is one lump.** Go evacuates a growing table
// incrementally, moving a bucket or two on each operation, so that no single
// insertion pays for the whole table. Here a table that grows is rehashed
// there and then. That is the same objection as a stop-the-world collector,
// at a smaller scale, and it is the piece to change first -- the interface
// would not move, because `put` is already the only place that grows.
//
// The buckets are one flat run and an overflow bucket is an index into it,
// rather than a pointer. That is what makes the cursor below possible: a
// position in a hash table has to be a single number for the protocol the
// compiler emits, and `bucket * 8 + slot` is one only if the buckets are
// countable.

use super::super::shape::Shape;
use super::keys::{self, Word};

// How many slots share one byte-array. Eight is Go's, and it is eight because
// eight bytes are one word: the byte comparison is a word load and a mask.
pub const SLOTS: usize = 8;

// A byte of nought means nothing is here.
const EMPTY: u8 = 0;

#[derive(Clone)]
struct Bucket {
    top:    [u8; SLOTS],
    keys:   [Word; SLOTS],
    values: [Word; SLOTS],
    // The next bucket in this chain, as an index. `None` for the end.
    over:   Option<usize>,
}

impl Bucket {
    fn new() -> Bucket {
        Bucket {
            top: [EMPTY; SLOTS],
            keys: [0; SLOTS],
            values: [0; SLOTS],
            over: None,
        }
    }
}

pub struct Hashed {
    buckets: Vec<Bucket>,
    // How many of the buckets at the front are the table proper. The rest are
    // overflow, and the low bits of a hash never select one.
    main:    usize,
    count:   usize,
}

// The top byte of a hash, nudged off the value that means "empty".
fn top(hash: u64) -> u8 {
    let held = (hash >> 56) as u8;
    if held == EMPTY { 1 } else { held }
}

impl Hashed {
    pub fn new() -> Hashed {
        Hashed { buckets: vec![Bucket::new()], main: 1, count: 0 }
    }

    pub fn len(&self) -> usize {
        self.count
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn home(&self, hash: u64) -> usize {
        (hash as usize) & (self.main - 1)
    }

    // ---- Looking one up ----------------------------------------------------

    // Which slot holds this key, walking the chain. The byte is compared
    // first, which is the whole point of keeping it.
    fn find(&self, key: Word, shape: Shape) -> Option<(usize, usize)> {
        let hash = keys::hash(key, shape);
        let want = top(hash);
        let mut at = Some(self.home(hash));
        while let Some(which) = at {
            let held = &self.buckets[which];
            for slot in 0..SLOTS {
                if held.top[slot] == want && keys::same(held.keys[slot], key, shape) {
                    return Some((which, slot));
                }
            }
            at = held.over;
        }
        None
    }

    pub fn get(&self, key: Word, shape: Shape) -> Option<Word> {
        self.find(key, shape).map(|(b, s)| self.buckets[b].values[s])
    }

    pub fn has(&self, key: Word, shape: Shape) -> bool {
        self.find(key, shape).is_some()
    }

    // ---- Putting one in ----------------------------------------------------

    pub fn put(&mut self, key: Word, value: Word, shape: Shape) {
        if let Some((b, s)) = self.find(key, shape) {
            self.buckets[b].values[s] = value;
            return;
        }
        if self.crowded() {
            self.grow(shape);
        }
        self.place(key, value, keys::hash(key, shape));
        self.count += 1;
    }

    // Six and a half slots out of eight, which is Go's load factor. Higher and
    // the chains get long; lower and the table is mostly empty buckets. It is
    // written as a comparison over doubled numbers so that the half is exact.
    fn crowded(&self) -> bool {
        self.count * 2 >= self.main * 13
    }

    // Into the first empty slot of the chain, adding a bucket to the end of it
    // if every slot is taken.
    fn place(&mut self, key: Word, value: Word, hash: u64) {
        let want = top(hash);
        let mut which = self.home(hash);
        loop {
            for slot in 0..SLOTS {
                if self.buckets[which].top[slot] == EMPTY {
                    self.buckets[which].top[slot] = want;
                    self.buckets[which].keys[slot] = key;
                    self.buckets[which].values[slot] = value;
                    return;
                }
            }
            match self.buckets[which].over {
                Some(next) => which = next,
                None => {
                    self.buckets.push(Bucket::new());
                    let made = self.buckets.len() - 1;
                    self.buckets[which].over = Some(made);
                    which = made;
                }
            }
        }
    }

    // Twice as many buckets, and everything put in again. The hash is worked
    // out afresh rather than kept beside each entry: keeping it would be eight
    // more words per bucket to save a hash on the one operation that already
    // touches every key in the table.
    fn grow(&mut self, shape: Shape) {
        let held: Vec<(Word, Word)> = self.entries();
        self.main *= 2;
        self.buckets = vec![Bucket::new(); self.main];
        self.count = 0;
        for (key, value) in held {
            self.place(key, value, keys::hash(key, shape));
            self.count += 1;
        }
    }

    fn entries(&self) -> Vec<(Word, Word)> {
        let mut out = Vec::with_capacity(self.count);
        for held in &self.buckets {
            for slot in 0..SLOTS {
                if held.top[slot] != EMPTY {
                    out.push((held.keys[slot], held.values[slot]));
                }
            }
        }
        out
    }

    // ---- Walking it --------------------------------------------------------

    // A position is `bucket * 8 + slot` over every bucket there is, overflow
    // ones included. The order that gives is the table's own and is not the
    // order anything was put in -- which is what "hashed" means, and is why
    // `Map` exists beside this one.
    fn slots(&self) -> i64 {
        (self.buckets.len() * SLOTS) as i64
    }

    fn full(&self, at: i64) -> bool {
        let held = at as usize;
        at >= 0 && at < self.slots() && self.buckets[held / SLOTS].top[held % SLOTS] != EMPTY
    }

    // The next position holding something. Empty slots are skipped here rather
    // than reported by `valid`, so that a table that is mostly empty still
    // takes one turn of the loop per entry.
    pub fn step(&self, at: i64) -> i64 {
        let mut held = at + 1;
        while held < self.slots() && !self.full(held) {
            held += 1;
        }
        held
    }

    pub fn valid(&self, at: i64) -> bool {
        self.full(at)
    }

    pub fn at(&self, at: i64) -> Option<(Word, Word)> {
        if !self.full(at) {
            return None;
        }
        let held = at as usize;
        let bucket = &self.buckets[held / SLOTS];
        Some((bucket.keys[held % SLOTS], bucket.values[held % SLOTS]))
    }

    pub fn key_at(&self, at: i64) -> Option<Word> {
        self.at(at).map(|held| held.0)
    }

    // ---- What the collector has to see -------------------------------------

    pub fn roots(&self, key: Shape, value: Option<Shape>, out: &mut Vec<usize>) {
        for held in &self.buckets {
            for slot in 0..SLOTS {
                if held.top[slot] == EMPTY {
                    continue;
                }
                keys::roots(held.keys[slot], key, out);
                if let Some(value) = value {
                    keys::roots(held.values[slot], value, out);
                }
            }
        }
    }
}

impl Default for Hashed {
    fn default() -> Hashed {
        Hashed::new()
    }
}

#[cfg(test)]
mod tests;
