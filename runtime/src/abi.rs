// The symbols themselves: what a compiled program actually calls.
//
// Every name here is one `mir::runtime` spells, and the two files are meant to
// be read together -- that one says what the call is for and this one is what
// happens. Nothing in this file decides anything. It takes the lock, converts
// a machine word into whatever the runtime calls that thing, and hands over.
// The reason for it being one file rather than a routine beside each piece of
// the runtime is the reason `mir::runtime` gives for itself: a name spelled in
// five files is a name that will one day differ by a letter in one of them,
// and the failure is a link error about a function nobody can find.
//
// **A handle is a number.** `__rt_map_new` gives back an index into a list the
// runtime keeps, shifted up by one and tagged in the low bit with whether it
// is a map or a set -- so the three cursor routines, which the compiler emits
// for both, can tell which they were handed. Nought is not a handle, which
// means a register that was never filled is caught here rather than followed.
//
// **The stack pointer is taken in this file and nowhere deeper.** A collection
// scans from where the mutator is to where its stack began, and "where the
// mutator is" has to be read in the outermost runtime frame -- read it three
// calls further in and the three frames above it, which may hold the only
// pointer to something, are not scanned.

use super::gc::{self, roots};
use super::map::keys::Word;
use super::set;
use super::shape::Shape;
use super::{alloc, map, runtime};

// ---- Starting up -----------------------------------------------------------

// `__rt_init()`: called once, from the program's outermost frame.
//
// Two things, and the first is not optional. The collector's roots are the
// mutator's stack, and where that stack begins cannot be worked out from
// inside -- the address of a local says where the stack is *now*. So a program
// that never calls this never collects, and its heap grows for ever. That is
// the safe failure of the two available, and the other one is freeing
// everything the program is holding.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_init() {
    roots::note();
    runtime().gc.rooted = true;
    gc::begin();
}

// ---- Room ------------------------------------------------------------------

// `__rt_alloc(bytes) -> ptr`: room the collector does not own.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_alloc(bytes: i64) -> *mut u8 {
    let want = usize::try_from(bytes).unwrap_or(0);
    alloc::kept(&mut runtime(), want) as *mut u8
}

// `__rt_gc_alloc(bytes, shape) -> ptr`: room the collector does own.
//
// The shape is what makes the heap scan precise: it says which words of the
// new object are pointers, and an object whose shape names none goes in a span
// the marker never reads. A null shape is allowed and means the same as a
// shape naming none.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_gc_alloc(bytes: i64, shape: *const u8) -> *mut u8 {
    let want = usize::try_from(bytes).unwrap_or(0);
    let stack = roots::here();
    let at = {
        let mut rt = runtime();
        let at = alloc::object(&mut rt, want, Shape::at(shape));
        gc::after(&mut rt, want, stack);
        at
    };
    at as *mut u8
}

// `__rt_collect()`: a whole cycle, now, on this thread.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_collect() {
    let stack = roots::here();
    gc::cycle_now(&mut runtime(), stack);
}

// ---- The barrier -----------------------------------------------------------

// `__rt_write(slot, value)`: a pointer going into a place that is not a frame.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_write(slot: *mut usize, value: usize) {
    gc::barrier::write(slot, value);
}

// `__rt_copy(to, from, shape)`: a whole value moved, where it holds pointers.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_copy(to: *mut u8, from: *const u8, shape: *const u8) {
    match Shape::at(shape) {
        Some(held) => gc::barrier::copy(to, from, held),
        // Nothing said how big it is, so there is nothing that can be moved.
        None => {}
    }
}

// ---- Handles ---------------------------------------------------------------

const SET: usize = 1;

fn handle(index: usize, set: bool) -> usize {
    ((index + 1) << 1) | usize::from(set)
}

fn which(held: usize) -> Option<(usize, bool)> {
    if held == 0 {
        return None;
    }
    Some(((held >> 1) - 1, held & SET == SET))
}

// ---- Maps ------------------------------------------------------------------

fn new_map(hashed: bool, key: *const u8, value: *const u8) -> usize {
    let Some(key) = Shape::at(key) else { return 0 };
    let mut rt = runtime();
    let held = map::Table::new(&mut rt, hashed, key, Some(Shape::at(value).unwrap_or(key)));
    rt.tables.push(held);
    handle(rt.tables.len() - 1, false)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_map_new(key: *const u8, value: *const u8) -> usize {
    new_map(false, key, value)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_hashmap_new(key: *const u8, value: *const u8) -> usize {
    new_map(true, key, value)
}

fn put_map(held: usize, key: Word, value: Word) {
    let Some((at, false)) = which(held) else { return };
    map::insert(&mut runtime(), at, key, value);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_map_insert(held: usize, key: Word, value: Word) {
    put_map(held, key, value);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_hashmap_insert(held: usize, key: Word, value: Word) {
    put_map(held, key, value);
}

// ---- Sets ------------------------------------------------------------------

fn new_set(hashed: bool, elem: *const u8) -> usize {
    let Some(elem) = Shape::at(elem) else { return 0 };
    let mut rt = runtime();
    let held = set::Held::new(&mut rt, hashed, elem);
    rt.sets.push(held);
    handle(rt.sets.len() - 1, true)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_set_new(elem: *const u8) -> usize {
    new_set(false, elem)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_hashset_new(elem: *const u8) -> usize {
    new_set(true, elem)
}

fn put_set(held: usize, elem: Word) {
    let Some((at, true)) = which(held) else { return };
    set::Held::put(&mut runtime(), at, elem);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_set_insert(held: usize, elem: Word) {
    put_set(held, elem);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_hashset_insert(held: usize, elem: Word) {
    put_set(held, elem);
}

// ---- Walking one -----------------------------------------------------------

// The cursor is an ordinal and starts at -1, which the lowering fixed when it
// made `IterStart` a constant rather than a call: "-1 is -1 whatever is being
// walked". So the first thing every loop does is step from -1, and what comes
// back has to be the first entry.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_iter_step(held: usize, at: i64) -> i64 {
    let rt = runtime();
    match which(held) {
        Some((index, true)) => rt.sets.get(index).map_or(at + 1, |one| one.step(at)),
        Some((index, false)) => rt.tables.get(index).map_or(at + 1, |one| one.step(at)),
        None => at + 1,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_iter_valid(held: usize, at: i64) -> i64 {
    let rt = runtime();
    let held = match which(held) {
        Some((index, true)) => rt.sets.get(index).is_some_and(|one| one.valid(at)),
        Some((index, false)) => rt.tables.get(index).is_some_and(|one| one.valid(at)),
        None => false,
    };
    i64::from(held)
}

// A set yields its element; a map yields the address of a `(K, V)` pair the
// table owns and writes over at each turn.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_iter_elem(held: usize, at: i64) -> Word {
    let rt = runtime();
    match which(held) {
        Some((index, true)) => rt.sets.get(index).map_or(0, |one| one.elem(at)),
        Some((index, false)) => rt.tables.get(index).map_or(0, |one| one.elem(at)),
        None => 0,
    }
}

#[cfg(test)]
mod tests;
