// Braces, and the separators §7 says are there without being written.
//
//     A newline ends a statement where a statement could end, and does not
//     where one could not.                              (docs/prose.txt, §7)
//
// Which is easy to say and is most of the length of this lexer, because "could
// end" is a question about the token before *and* the token after, and because
// a `{` in this language opens four different things: a block, a map literal,
// a set literal, and the body of a declaration whose header is still being
// read. Telling them apart is what `scan_brace_body` does, and it does it by
// reading the body and rolling back.
//
// The state is a stack in a bitfield rather than a `Vec`: brace nesting is
// bounded by anything a person will write, and a `u64` of it costs nothing to
// save and restore -- which happens on every lookahead.

use crate::lex::tokens::*;

use super::rules::*;
use super::{BraceScan, Lexer};

impl Lexer {
    // Records what kind of body a `{` opens. There are four:
    //
    //   - a header's body — the first `{` at the bracket depth the heading
    //     keyword was seen at, since the grammar keeps a struct literal out of
    //     the top level of a header;
    //   - a struct literal, where a type name ends right before it: `Point {`;
    //   - a map or set literal — `{1: 2}`, `{1, 2}`, anything after a glued `#`;
    //   - an import's group, where a `::` stands in front of it;
    //   - a block otherwise.
    //
    // Bit `n` of `entry_braces` is set when the brace at depth `n` holds
    // comma-separated entries rather than statements; nothing is inserted inside
    // one, as the commas are written. Bit `n` of `value_braces` narrows that to
    // the literals, whose `}` closes a value and so ends no line either.
    //
    // A bitmask keeps the snapshot `Copy`, so a `peek` costs no allocation; past
    // 64 levels of nesting a body reverts to statements.
    //
    // Returns whether the brace opened a value: a literal's `{` is `LCurlyValue`
    // and a block's or a body's is `LCurlyBracket`, which is what the grammar
    // needs to tell them apart.
    pub(super) fn push_brace(
        &mut self,
        after_type_name: bool,
        after_hash: bool,
        after_path: bool,
        value_only: bool,
    ) -> bool {
        let at_header = self.pending_header
            && self.bracket_depth == self.header_depth
            && self.brace_depth == self.header_brace_depth;
        let literal = !at_header && after_type_name;

        // A collection literal *can* stand at the top level of a header —
        // `for x in {1, 2, 3} {` — where a struct literal cannot, so a header
        // gives up a brace that can only be a literal: one with a `,` or `:` at
        // its top level, or a `#` glued in front. A body of statements never
        // has those. A struct, enum or match body does, so those three keep
        // their brace whatever is inside it.
        // An import's group is entries whatever is written inside it, and a `::`
        // in front is the whole of what says so — no other brace may follow one.
        let collection = !literal
            && (after_hash
                || after_path
                || if at_header {
                    !self.pending_entry_body
                        && matches!(self.scan_brace_body(), BraceScan::Collection)
                } else {
                    self.opens_collection(value_only)
                });

        let heads_body = at_header && !collection;
        let entries = literal || collection || (heads_body && self.pending_entry_body);

        if self.brace_depth < 64 {
            let bit = 1u64 << self.brace_depth;
            if entries {
                self.entry_braces |= bit;
            } else {
                self.entry_braces &= !bit;
            }
            if literal || collection {
                self.value_braces |= bit;
            } else {
                self.value_braces &= !bit;
            }
        }
        self.brace_depth += 1;
        // A `{` deeper than the header's — `match f({ ... }) {` — is not the
        // body, so the header keeps waiting for the one that is.
        if heads_body {
            self.pending_header = false;
            self.pending_entry_body = false;
        }
        literal || collection
    }

    // Whether a `{` that no header and no type name claimed opens a map or a set
    // rather than a block. Nothing in front of the brace can say, so the lexer
    // looks inside: statements are separated by `;` and entries by `,`, and
    // neither separator is legal in the other's body.
    //
    // `{}` and `{ x }` hold neither, and there `value_only` decides — where only
    // a value can stand it is a literal, and where a statement could stand it is
    // a block.
    //
    // The cost is that a block used as a value has to hold a statement boundary,
    // which every block worth writing does. `{ f() }` after an `=` is the set of
    // one it looks like; the empty map is `{:}` in either position, the empty
    // set `{,}`.
    fn opens_collection(&mut self, value_only: bool) -> bool {
        match self.scan_brace_body() {
            BraceScan::Collection => true,
            BraceScan::Block => false,
            BraceScan::Undecided => value_only,
        }
    }

    // Reads ahead over the body of the `{` just scanned, stopping at the first
    // token that tells the two kinds apart, and rewinds. Only the brace's own
    // level counts: the `,` of `{ f(a, b) }` is the call's, so it is skipped and
    // the brace left `Undecided`.
    //
    // A line break that would end a statement counts as a `;`, since that is what
    // it is about to become: a block need contain no separator at all, and
    // `{ f()` / newline / `g() }` is two statements. Between entries a newline
    // means nothing, and a real literal's `,` or `:` comes first anyway.
    //
    // The scan runs to the end of the body in the worst case, so nested literals
    // are quadratic in principle; in practice it stops a token or two in.
    fn scan_brace_body(&mut self) -> BraceScan {
        let saved = self.save();
        let mut depth = 0usize;
        // How many type argument lists are open. Kept apart from `depth`
        // because a `>` is a comparison as readily as a closer, and a `>`
        // inside a `(` must not be taken for one: `{ f(a > b, c) }` has its
        // comma inside the call and is no collection.
        let mut angles = 0usize;
        // Whether a closure's parameter list is open. Its commas separate its
        // own parameters and not the brace's entries: `{ |x, s| true }` is a
        // block whose value is a closure, not a set of two things.
        let mut pipes = false;
        let mut prev_can_end = false;
        let verdict = loop {
            // `scan_token` reads from where it stands; only `next_token` skips
            // ahead, and this look is taken without it.
            let crossed_newline = self.skip_whitespace();
            if depth == 0 && crossed_newline && prev_can_end && self.breaks_statement(false) {
                break BraceScan::Block;
            }
            let tok = self.scan_token();
            // Whether a name stood in front of this token, which is what makes
            // a `<` a type argument list rather than a comparison. Read before
            // the flags below move on to this token.
            let after_name = self.last_was_name && !self.last_was_decl_name;
            // Whether the token before this one could have ended an operand,
            // which is what tells a closure's opening `|` from a bitwise one.
            // Read before the flags below move on to this token.
            let after_operand = self.last_ends_operand;
            prev_can_end = can_end_statement(&tok.toktype);
            // Kept up to date through the look so a `&&` inside the body reads
            // the same here as it will when the body is really scanned, and a
            // `.0` the same. The rewind below puts them back.
            self.last_ends_operand = ends_an_operand(&tok.toktype);
            self.prev_was_dot = tok.toktype == TokType::Dot;
            // And these three, or a `<` inside the body is a comparison here
            // and a type argument list when the body is really scanned -- and
            // the two disagree about whether the comma after it separates
            // entries. `opens_type_args` is asked only after a name.
            self.last_was_decl_name =
                self.last_was_decl_kw && matches!(tok.toktype, TokType::Identifier(_));
            self.last_was_decl_kw = matches!(
                tok.toktype,
                TokType::Fn | TokType::Struct | TokType::Enum | TokType::Trait | TokType::Macro
            );
            self.last_was_name = matches!(tok.toktype, TokType::Identifier(_));
            match tok.toktype {
                TokType::LParen | TokType::LBracket | TokType::LCurlyBracket => depth += 1,
                TokType::RParen | TokType::RBracket => depth = depth.saturating_sub(1),
                // The `}` closing the body itself: nothing decided it.
                TokType::RCurlyBracket => {
                    if depth == 0 {
                        break BraceScan::Undecided;
                    }
                    depth -= 1;
                }
                // A call's type arguments, which hold commas of their own:
                // `id<i32, str>(1)` is one thing and not two, so its comma
                // separates no entries.
                //
                // The look is taken here rather than read off the token,
                // because this scan takes its tokens from `scan_token` and it
                // is `next_token` that turns a `<` into a `LessGeneric`. Inside
                // a list everything is a type, so a `<` there opens a nested
                // one without being asked again.
                TokType::LessThan if angles > 0 => angles += 1,
                TokType::LessThan if after_name && self.opens_type_args() => angles += 1,
                TokType::GreaterThan if angles > 0 => angles -= 1,
                // `Vec<Map<K, V>>` closes two at once.
                TokType::RShift if angles > 0 => angles = angles.saturating_sub(2),
                // A `|` where no operand stands in front opens a closure's
                // parameter list, and the next one closes it.
                TokType::Pipe if depth == 0 && pipes => pipes = false,
                TokType::Pipe if depth == 0 && !after_operand => pipes = true,
                TokType::Comma | TokType::Colon if depth == 0 && angles == 0 && !pipes => {
                    break BraceScan::Collection
                }
                TokType::Semicolon if depth == 0 => break BraceScan::Block,
                ref t if depth == 0 && starts_statement(t) => break BraceScan::Block,
                // Unterminated, or malformed past the point of guessing.
                TokType::EOF | TokType::Error(_) => break BraceScan::Undecided,
                _ => {}
            }
        };
        self.restore(saved);
        verdict
    }

    // Whether the `<` just scanned opens a call's type arguments rather than
    // being a comparison. `foo<MyType>(x)` is the case that needs it: a bare
    // name is a type and an expression both, so what stands *inside* the angles
    // settles nothing. What settles it is the shape as a whole -- a matching
    // `>` with a `(` after it.
    //
    // Called with the `<` already consumed. Anything that cannot appear in a
    // type argument gives it up at once, which is what keeps `a < b && c` a
    // comparison; `fits_in_generics` is the same list the speculative context
    // above uses.
    pub(super) fn opens_type_args(&mut self) -> bool {
        let saved = self.save();
        let mut depth = 1usize;
        // A `(` may stand inside a type argument -- a grouped type, a tuple --
        // so one is followed in. What must not be followed is a closer this
        // look did not open: `(a < b) > (c)` is a comparison inside a group,
        // and without this the scan walks out of the group and finds the `(`
        // of `(c)` sitting where a call's would be.
        let mut brackets = 0usize;
        let verdict = loop {
            self.skip_whitespace();
            let tok = self.scan_token();
            match tok.toktype {
                TokType::LParen | TokType::LBracket => brackets += 1,
                TokType::RParen | TokType::RBracket => {
                    if brackets == 0 {
                        break false;
                    }
                    brackets -= 1;
                }
                TokType::LessThan => depth += 1,
                TokType::GreaterThan => {
                    depth -= 1;
                    if depth == 0 {
                        // The whole of the rule: a call follows a type argument
                        // list, and nothing else does.
                        self.skip_whitespace();
                        break self.peek_char() == Some('(');
                    }
                }
                // A `>>` closing two lists at once, which the scan sees whole:
                // nothing has opened a generic context here for it to split in,
                // so it counts for the two it is. `Map<K, V>>` ends this way.
                TokType::RShift => {
                    if depth < 2 {
                        break false;
                    }
                    depth -= 2;
                    if depth == 0 {
                        self.skip_whitespace();
                        break self.peek_char() == Some('(');
                    }
                }
                TokType::EOF | TokType::Error(_) => break false,
                ref t if !fits_in_generics(t) => break false,
                _ => {}
            }
        };
        self.restore(saved);
        verdict
    }

    // Whether the innermost open brace holds comma-separated entries.
    pub(super) fn in_entry_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.entry_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    // Whether the innermost open brace closes a value — a struct, map or set
    // literal's — rather than a statement.
    pub(super) fn in_value_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.value_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    // Decides whether to synthesize a separator at the current position.
    pub(super) fn wants_separator(&self, crossed_newline: bool) -> bool {
        if !self.last_can_end {
            return false;
        }
        // Inside `(...)` or `[...]` a newline is just formatting, so argument
        // lists and indexes can span lines. Braces are blocks, so they count.
        if self.bracket_depth > 0 {
            return false;
        }
        // Entries are the writer's to separate. The fields of a struct, the
        // variants of an enum, the arms of a match and the fields of a struct
        // literal all take a written `,`, so a newline inside one of those
        // braces inserts nothing — as inside `(...)`, and for the same reason.
        // Only a statement body gets a separator, which is why this asks about
        // the innermost brace: a block nested in an entry is a body again.
        if self.in_entry_body() {
            return false;
        }

        match self.peek_char() {
            // End of input, with a statement left open.
            None => true,
            Some(_) if !crossed_newline => false,
            _ => self.breaks_statement(self.last_closed_block),
        }
    }

    // Whether what stands at the current position starts a statement rather than
    // continuing the one before it. Asked at a line break, of the line below;
    // end of input is the caller's. `closed_block` says whether the token just
    // read was a block's `}`, which narrows what may still continue the line.
    fn breaks_statement(&self, closed_block: bool) -> bool {
        match self.peek_char() {
            None => false,
            // A `}` closes the body by itself, so the entry or statement in
            // front of it needs no separator. That is what lets the last field
            // of a struct go without a trailing comma, and the last statement
            // of a block without a semicolon.
            Some('}') => false,
            // Keyword continuations come first, so `else` still follows the `}`
            // of an if branch and `as` still follows a block it casts.
            Some(c) if c.is_alphabetic() || c == '_' => !continues_statement(&self.peek_word()),
            Some(c) if closed_block => !continues_after_brace(c),
            // `%` spells the remainder operator and an attribute both. Glued to
            // a name it is the attribute, which begins a declaration and so
            // breaks the line; with anything else after it, it is the operator
            // continuing one. See `read_operator`, which settles the same
            // question from the other side.
            Some('%') => matches!(self.peek_char_at(1), Some(n) if n.is_alphabetic() || n == '_'),
            Some(c) if starts_continuation(c) => false,
            Some(_) => true,
        }
    }

    // Whether a `{` is next in the input, whitespace aside. A newline counts as
    // whitespace: `unsafe` cannot end a statement, so a brace on the line below
    // is still the body it opens. Comments are already blanked to spaces.
    pub(super) fn brace_follows(&self) -> bool {
        let mut i = self.index;
        while let Some(&c) = self.input.get(i) {
            if !c.is_whitespace() {
                return c == '{';
            }
            i += 1;
        }
        false
    }

    // Whether a name stands next, which is what tells `fn f(..)` from `fn(..)`.
    pub(super) fn name_follows(&self) -> bool {
        let mut i = self.index;
        while let Some(&c) = self.input.get(i) {
            if !c.is_whitespace() {
                return c.is_alphabetic() || c == '_';
            }
            i += 1;
        }
        false
    }

    // Reads the word at the current position without consuming it.
    fn peek_word(&self) -> String {
        let mut word = String::new();
        let mut i = self.index;
        while let Some(&c) = self.input.get(i) {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
                i += 1;
            } else {
                break;
            }
        }
        word
    }
}
