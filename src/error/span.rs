//! Where in a source something is.

/// A piece of the source: where it begins, and how much of it there is.
///
/// Counted in characters and from one, as a token's position is -- a column is
/// what a reader counts along a line, and bytes would put a caret in the wrong
/// place the first time a source held anything but ASCII.
///
/// A `len` of zero is a place rather than a piece: the end of the file, or a
/// separator the lexer inserted where nothing was written. There is nothing to
/// underline at one, and a reader is pointed at it with a single caret.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub col:  usize,
    pub len:  usize,
}

impl Span {
    pub fn new(line: usize, col: usize, len: usize) -> Span {
        Span { line, col, len }
    }

    /// A span standing at a position with nothing written there.
    pub fn at(line: usize, col: usize) -> Span {
        Span { line, col, len: 0 }
    }
}
