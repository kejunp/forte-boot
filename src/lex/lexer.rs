// The lexer: characters to tokens, with the separators nobody wrote put in.
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR
//              ^^^
//
// A lexer is usually the dullest pass in a compiler and this one is not, for
// one reason: §7. A newline ends a statement where a statement could end and
// does not where one could not, so this pass cannot hand back a flat run of
// tokens without deciding, at every newline, whether a statement ended there.
// That decision needs the token before, the token after, and sometimes a scan
// of what is inside the braces ahead -- which is why there is a snapshot type,
// a rollback, and a stack of brace kinds in a file that would otherwise be a
// loop over characters.
//
// The state is all in one struct because all of it is asked at once. What
// stood in front of the current token decides whether `&&` is one operator or
// two, whether `{` opens a block or a map, whether `<` opens generic arguments
// or is less-than, and whether `.1` is a tuple index or part of a float. None
// of those can be answered by looking at the characters in hand.
//
// One file each below, and the two at the top are the ones to read first:
//
//   `rules`    the questions asked about a token, as free functions -- a rule
//              that cannot see where the scanner is cannot be wrong about it.
//   `layout`   §7 itself: braces, separators, and what a `{` opens.
//   `cursor`   where the scanner is, and how to put it back.
//   `scan`     the loop, and what a token means where it turned up.
//   `read`     one token off the front, which is the dull part.
//   `words`    strings, characters, names and lifetimes.
//   `numbers`  numbers, and the words stuck to the end of them.


mod cursor;
mod layout;
mod numbers;
mod read;
mod rules;
mod scan;
mod words;

#[cfg(test)]
mod tests;


pub struct Lexer {
    input: Vec<char>,
    index: usize,
    line:  usize,
    col:   usize,

    // Automatic separator insertion state.
    last_can_end:      bool,
    last_closed_block: bool,
    bracket_depth:     usize,

    // Whether an operand stands in front of the token being scanned, which is
    // what splits `&&` into two prefix `&`. See `read_operator`.
    last_ends_operand: bool,

    // Whether an `@attribute` is still being read. See `next_token`.
    in_attribute:      bool,
    attr_bracket_depth: usize,

    // The same wait for the `(suite)` of a `pub(suite)`, and for the same
    // reason: its `)` closes a visibility and not an operand.
    in_visibility:     bool,
    vis_bracket_depth: usize,

    // Brace context. See `push_brace`.
    brace_depth:        usize,
    entry_braces:       u64,
    value_braces:       u64,
    pending_entry_body: bool,
    pending_header:     bool,
    header_depth:       usize,
    header_brace_depth: usize,

    // What stood in front of the current token, for deciding a `{`.
    hash_prefix:    bool,
    path_prefix:    bool,
    prev_ends_stmt: bool,
    prev_was_brace: bool,

    // Whether a `.` stands in front of the token being scanned, which keeps
    // `t.0.1` two tuple indexes rather than a float. See `read_number`.
    prev_was_dot:   bool,

    // Generic argument list state.
    generic_depth:     usize,
    last_was_name:     bool,
    last_was_impl:     bool,
    last_was_type_end: bool,
    // Whether the token just read was a word that names a declaration, and
    // whether the one before it was the keyword introducing one. Together they
    // say that a `<` here opens generic *parameters* and not a call's
    // arguments: `fn sort<T>(xs)` looks exactly like `sort<T>(xs)` otherwise.
    last_was_decl_kw:   bool,
    last_was_decl_name: bool,
}

// Everything `next_token` mutates, so a lookahead can be rolled back. The input
// never changes, so it stays out of the snapshot.
#[derive(Clone, Copy)]
pub(super) struct State {
    index: usize,
    line:  usize,
    col:   usize,

    last_can_end:      bool,
    last_closed_block: bool,
    bracket_depth:     usize,
    last_ends_operand: bool,

    in_attribute:       bool,
    attr_bracket_depth: usize,

    in_visibility:      bool,
    vis_bracket_depth:  usize,

    brace_depth:        usize,
    entry_braces:       u64,
    value_braces:       u64,
    pending_entry_body: bool,
    pending_header:     bool,
    header_depth:       usize,
    header_brace_depth: usize,

    hash_prefix:    bool,
    path_prefix:    bool,
    prev_ends_stmt: bool,
    prev_was_brace: bool,
    prev_was_dot:   bool,

    generic_depth:     usize,
    last_was_name:     bool,
    last_was_impl:     bool,
    last_was_type_end: bool,
    last_was_decl_kw:   bool,
    last_was_decl_name: bool,
}

// What a look inside a `{` says about the body it opens. See `scan_brace_body`.
pub(super) enum BraceScan {
    // A `,` or `:` turned up between its entries: a map or a set.
    Collection,
    // A `;` or a keyword no expression can start with: statements.
    Block,
    // Neither — `{}` or `{ x }`, which read equally well as both.
    Undecided,
}
