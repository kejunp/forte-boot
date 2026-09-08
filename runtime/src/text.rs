// What a `str` comes to when two of them are compared.
//
// A `str` is fat -- an address and a length -- and every comparison the
// language writes over one is a comparison of what it *says*. That is not
// something a machine instruction does: `a == b` over two words compares the
// two addresses, and two strings holding the same characters in two places are
// two different addresses. What that came to is worse than a wrong answer at
// one optimisation level and a right one at another, which is what it was:
// literals are pooled, so equal literals shared a symbol and compared equal by
// accident, and anything copied into a frame did not.
//
// So the four orderings and the two equalities all go through here. It answers
// the way `strcmp` does -- negative, nought, positive -- and `mir::lower` turns
// that into whichever comparison was written by holding the answer against
// nought. One symbol for the six, and the ordering is the same lexicographic
// one `runtime/src/map/keys.rs` compares a string key by.

// The pair a `str` is, as the register holds it: the address of two words, the
// first the characters and the second how many.
fn text<'a>(at: usize) -> &'a [u8] {
    if at == 0 {
        return &[];
    }
    unsafe {
        let pair = at as *const usize;
        let (held, len) = (*pair, *pair.add(1));
        if held == 0 || len == 0 {
            return &[];
        }
        std::slice::from_raw_parts(held as *const u8, len)
    }
}

// Negative where `a` sorts before `b`, nought where they say the same thing,
// positive otherwise. Byte order and then length, which is what a reader means
// by alphabetical for the characters that have an order at all.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_str_cmp(a: usize, b: usize) -> i64 {
    match text(a).cmp(text(b)) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[cfg(test)]
mod tests;
