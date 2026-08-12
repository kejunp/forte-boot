// Where in a source something is.

// A piece of the source, counted in characters from one so a caret lands right
// on non-ASCII. A `len` of zero is a place rather than a piece -- end of file,
// or an inserted separator -- and is drawn as a single caret.
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

    // A position with nothing written there.
    pub fn at(line: usize, col: usize) -> Span {
        Span { line, col, len: 0 }
    }
}
