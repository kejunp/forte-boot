// Getting an object: the path from a number of bytes to an address.
//
// Three paths, and which one is taken is decided by the size and by whether
// the thing holds pointers. Go has the same three and for the same reasons.
//
//   tiny    under sixteen bytes and holding no pointers. Several share one
//           sixteen-byte block. This is worth doing only because such an
//           object has nothing the marker would ever look at, so the block
//           needs no way of telling its tenants apart -- it is free when all
//           of them are. A great deal of what a program allocates is small and
//           pointer-free, and giving each of those a whole object would round
//           a three-byte thing up to eight and leave five unused.
//   small   up to thirty-two kilobytes. Rounded to a size class and taken out
//           of the span the cache is holding for that class, which is a bit in
//           a bitmap and an addition. This is the path that matters.
//   large   anything bigger, with a run of pages to itself.
//
// **Everything handed out is nought.** A page from the kernel already is, but
// an object being reused after a sweep is not, and it has to be: the marker
// reads the words a shape called pointers, and a word left over from whatever
// was there before would be followed. So the cost is paid on every allocation
// rather than reasoned about, and the alternative -- tracking which spans have
// never been written to -- is Go's and is an optimisation for a heap much
// larger than anything here.
//
// **An object made during a cycle is marked as it is made.** It cannot be
// garbage: the marker is working from the reachable set as it stood when the
// cycle began, so nothing it can reach knows about this object, and sweeping
// what it did not reach would free something the program is holding right now.
// Allocating black is the standard answer and it is why a program that
// allocates furiously during a collection ends the collection with a bigger
// heap rather than a broken one.

use super::heap::{classes, large, span::SpanId};
use super::shape::Shape;
use super::Runtime;

// The largest thing that goes in a shared block. Sixteen bytes is Go's, and
// the block is sixteen bytes, so two eight-byte objects fill one exactly.
pub const TINY_MAX: usize = 16;

// Room for one value of `shape`, or of `bytes` with nothing said about it.
//
// A shape that says nothing about pointers puts the object in an unscanned
// span, which is the same thing as passing no shape at all -- the caller has
// said the collector will never have to read this, either way.
pub fn object(rt: &mut Runtime, bytes: usize, shape: Option<Shape>) -> usize {
    let scan = shape.is_some_and(|held| held.scan());
    let bytes = bytes.max(1);

    let at = if !scan && bytes <= TINY_MAX {
        let align = shape.map_or_else(|| natural(bytes), |held| held.align()).max(1);
        tiny(rt, bytes, align)
    } else if large::alone(bytes) {
        big(rt, bytes, scan, shape)
    } else {
        small(rt, bytes, scan, shape)
    };
    at.unwrap_or(0)
}

// ---- Small -----------------------------------------------------------------

fn small(rt: &mut Runtime, bytes: usize, scan: bool, shape: Option<Shape>) -> Option<usize> {
    let class = classes::class_of(bytes)?;
    loop {
        let id = match rt.cache.holding(class, scan) {
            Some(id) => id,
            None => {
                let cycle = rt.gc.cycle;
                let id = rt.central.span(&mut rt.heap, class, scan, cycle)?;
                rt.cache.hold(class, scan, Some(id));
                id
            }
        };
        if let Some(index) = rt.heap.span_mut(id).take() {
            return Some(settle(rt, id, index, shape));
        }
        // It filled. Back to the central lists, and round again for another.
        rt.central.give(&rt.heap, id);
        rt.cache.hold(class, scan, None);
    }
}

// ---- Tiny ------------------------------------------------------------------

// The block being filled, or a fresh one. `used` is how far into the current
// block the last tenant reached; a new tenant starts at the next offset its
// own alignment allows, and if that does not fit the block is abandoned where
// it stands. Abandoned and not remembered: the few bytes left at the end of a
// block are not worth a list to hold them in.
// What an allocation with nothing said about it has to be aligned to. Go's
// rule, and it is the only one available: with no type in hand, the size is
// the only thing that says anything about what is going in the room, and a
// four-byte thing wants four.
fn natural(bytes: usize) -> usize {
    match bytes {
        _ if bytes % 8 == 0 => 8,
        _ if bytes % 4 == 0 => 4,
        _ if bytes % 2 == 0 => 2,
        _ => 1,
    }
}

fn tiny(rt: &mut Runtime, bytes: usize, align: usize) -> Option<usize> {
    let offset = super::mem::up(rt.cache.used, align);
    if rt.cache.tiny != 0 && offset + bytes <= TINY_MAX {
        let at = rt.cache.tiny + offset;
        rt.cache.used = offset + bytes;
        return Some(at);
    }
    let at = small(rt, TINY_MAX, false, None)?;
    rt.cache.tiny = at;
    rt.cache.used = bytes;
    Some(at)
}

// ---- Large -----------------------------------------------------------------

fn big(rt: &mut Runtime, bytes: usize, scan: bool, shape: Option<Shape>) -> Option<usize> {
    let cycle = rt.gc.cycle;
    let id = rt.large.make(&mut rt.heap, bytes, scan, cycle)?;
    Some(settle(rt, id, 0, shape))
}

// ---- What every path finishes with -----------------------------------------

// Clear it, say what is in it, mark it if a cycle is running, and count it.
// Four things every path does and none of them may be skipped, so they are
// here once rather than three times.
fn settle(rt: &mut Runtime, id: SpanId, index: usize, shape: Option<Shape>) -> usize {
    let at = rt.heap.span(id).base_of(index);
    let size = rt.heap.span(id).size;

    unsafe {
        std::ptr::write_bytes(at as *mut u8, 0, size);
    }
    if let Some(held) = shape {
        if rt.heap.span(id).scan {
            let (map, words) = (held.map().to_vec(), held.words());
            rt.heap.span_mut(id).describe(index, &map, words);
        }
    }
    if rt.gc.black {
        rt.heap.span_mut(id).mark(index);
    }
    rt.heap.live += size;
    at
}

// ---- Room the collector does not own ---------------------------------------

// `__rt_alloc`: room that outlives the frame and that nothing ever frees.
//
// It comes out of the same heap and is deliberately *not* the same thing as an
// allocation with no shape. An unscanned object is still collected -- it is
// swept when nothing points at it -- and this is not: it is marked as it is
// made and never unmarked, so it survives every cycle whatever points at it.
//
// That is what the caller asked for. A closure's environment, which is what
// this is for today, is reached through a fn value the collector cannot yet
// read: the compiler builds the pair and `mir::lower::calls` never hands the
// environment over at a call, so following the value would be following half a
// thing. Until that is settled, the honest answer is to leak, and to say that
// is what is happening rather than to collect something whose liveness nothing
// can work out.
pub fn kept(rt: &mut Runtime, bytes: usize) -> usize {
    let at = object(rt, bytes, None);
    if let Some((id, index)) = rt.heap.holding(at) {
        rt.heap.span_mut(id).mark(index);
        rt.pinned.push((id, index));
    }
    at
}

#[cfg(test)]
mod tests;
