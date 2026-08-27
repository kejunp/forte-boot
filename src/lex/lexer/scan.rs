// The loop: one token at a time, and the separators nobody wrote.
//
// `next_token` is where every other file here is called from, and most of what
// it does is not reading characters -- that is `read.rs` -- but deciding what
// the token that came back means in the place it turned up. A newline may be a
// separator or nothing; a `{` may open four different things; a `<` may open
// generic arguments or be less-than.
//
// `peek` is the same loop run and rolled back, which is what `cursor.rs`
// exists for.

use crate::lex::tokens::*;

use super::rules::*;
use super::Lexer;

impl Lexer {
    // The token `next_token` would return, without consuming it. Lexing is
    // context-sensitive, so this runs the real scanner and rewinds rather than
    // taking a lookahead path that could drift out of step — hence `&mut self`.
    // Peeking is otherwise free of side effects, and repeats give the same token.
    pub fn peek(&mut self) -> Tok {
        let saved = self.save();
        let tok = self.next_token();
        self.restore(saved);
        tok
    }

    pub fn next_token(&mut self) -> Tok {
        // Position just past the previous token — where an inserted semicolon
        // belongs, at the end of that line rather than the start of the next.
        let line = self.line;
        let col = self.col;

        let mut crossed_newline = self.skip_whitespace();

        // `->` splices the following line onto this one, cancelling any pending
        // insertion: `let x = y ->` / newline / `+ 2` is one statement.
        while self.peek_char() == Some('-') && self.peek_char_at(1) == Some('>') {
            self.advance();
            self.advance();
            self.skip_whitespace();
            crossed_newline = false;
        }

        if self.wants_separator(crossed_newline) {
            self.last_can_end = false;
            self.last_closed_block = false;
            // The statement is over, so no operand stands in front of what
            // follows: a line beginning `&&x` begins with two references.
            self.last_ends_operand = false;
            self.last_was_type_end = false;
            self.hash_prefix = false;
            // An inserted separator ends the statement as a written one does, so
            // a `{` after it opens a block.
            self.prev_ends_stmt = true;
            self.prev_was_brace = false;
            // The statement is over, so nothing it opened is still pending.
            self.pending_header = false;
            self.pending_entry_body = false;
            return Tok { toktype: TokType::Semicolon, line, col, len: 0 };
        }

        // What stands in front of this token, which is what decides a `{`.
        // Captured before the scan overwrites it.
        let after_type_name = self.last_was_type_end;
        let after_hash = self.hash_prefix;
        let after_path = self.path_prefix;
        let value_only = !self.prev_ends_stmt && !(self.prev_was_brace && !self.in_entry_body());

        // Where the token starts, so that its width can be had from how far the
        // scan moves rather than from what it produced. Taken after the
        // whitespace and any `->` are behind us, so it is the first character
        // the token was written with.
        let start = self.index;
        let mut tok = self.scan_token();

        // A `<` after a name may open a call's type arguments. `last_was_name`
        // is still the previous token's here, which is what this has to ask.
        // `fn sort<T>(xs)` reads exactly as `sort<T>(xs)` does from here, so a
        // name that a declaration keyword introduced is the one name a `<` may
        // not open a call's arguments after.
        let opens_generic = tok.toktype == TokType::LessThan
            && self.last_was_name
            && !self.last_was_decl_name
            && self.opens_type_args();

        // A `>` only closes a generic if one was open; that also makes it the
        // end of a type, and so a place a statement can end: `let v: Vec<i32>`.
        let closed_generic = self.generic_depth > 0 && tok.toktype == TokType::GreaterThan;
        match &tok.toktype {
            // Only a name can be generic, which rules out `1 < 2` and `) < x`.
            // `impl` is the one keyword a `<` may follow, since an impl
            // introduces its own parameters before naming a type: `impl<T>`.
            TokType::LessThan if self.last_was_name || self.last_was_impl => {
                self.generic_depth += 1;
            }
            TokType::GreaterThan => {
                self.generic_depth = self.generic_depth.saturating_sub(1);
            }
            t if self.generic_depth > 0 && !fits_in_generics(t) => self.generic_depth = 0,
            _ => {}
        }
        // A `_` is deliberately not one. It names no type, so it opens no
        // generic context and heads no struct literal: `_ < 2` is a comparison
        // and the `{` after a `_` is whatever it would have been on its own.
        self.last_was_decl_name =
            self.last_was_decl_kw && matches!(tok.toktype, TokType::Identifier(_));
        self.last_was_decl_kw = matches!(
            tok.toktype,
            TokType::Fn | TokType::Struct | TokType::Enum | TokType::Trait | TokType::Macro
        );
        self.last_was_name = matches!(tok.toktype, TokType::Identifier(_));
        self.last_was_impl = tok.toktype == TokType::Impl;
        // A name, or the `>` closing its type arguments: `Point {`, `Vec<i32> {`.
        self.last_was_type_end = self.last_was_name || closed_generic;

        self.last_can_end = can_end_statement(&tok.toktype) || closed_generic;
        // An attribute is a prefix of the declaration it annotates, so nothing
        // inside one ends a statement: `@inline` / newline / `fn f()` is a
        // single item, and the name that closes the attribute must not have a
        // separator inserted after it.
        // The `(suite)` of a visibility is a prefix in the same way, and so is
        // nothing a statement may end inside of.
        if self.in_attribute || self.in_visibility {
            self.last_can_end = false;
        }
        // The `>` closing a type argument list ends a type, and so an operand.
        self.last_ends_operand = ends_an_operand(&tok.toktype) || closed_generic;
        self.last_closed_block = false;
        // A `#` marks the brace behind it as a hash map or hash set, but only
        // when glued to it — `#{`, as `#[` opens an attribute.
        self.hash_prefix = tok.toktype == TokType::HashTag && self.peek_char() == Some('{');
        // A `{` after a `::` is the group of an import and nothing else, which
        // is what `push_brace` needs to hear: the scan inside would call the
        // one-name `a::{b}` undecided and fall back on where it stands.
        self.path_prefix = tok.toktype == TokType::ColonColon;
        self.prev_ends_stmt = matches!(tok.toktype, TokType::Semicolon | TokType::FatArrow);
        self.prev_was_brace =
            matches!(tok.toktype, TokType::LCurlyBracket | TokType::RCurlyBracket);
        // Only the lone `.`: the dots of a range are their own token, so
        // `0..0.5` keeps its float.
        self.prev_was_dot = tok.toktype == TokType::Dot;
        // Set for the `{` of a struct, map or set literal, and reported to the
        // parser as `LCurlyValue` once the rest of the state is up to date.
        let mut opens_value = false;
        match &tok.toktype {
            TokType::LParen | TokType::LBracket => self.bracket_depth += 1,
            TokType::RParen | TokType::RBracket => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
            }
            TokType::LCurlyBracket => {
                opens_value =
                    self.push_brace(after_type_name, after_hash, after_path, value_only);
            }
            TokType::RCurlyBracket => {
                // Only a block's `}` ends the line it sits on; the `}` of a
                // literal — a struct's, a map's, a set's — closes a value that
                // an operator may continue.
                self.last_closed_block = !self.in_value_body();
                self.brace_depth = self.brace_depth.saturating_sub(1);
                // A `}` that closes the body a header was waiting inside of
                // ends the wait: a signature with no body, `fn show(this):
                // str`, gets no separator before the `}` of the trait around
                // it, and its header must not outlive it. A `}` at the
                // header's own depth closed something the header contains —
                // the literal in `if (Cfg { on: true }).on {` — and the body
                // it is waiting for is still to come.
                if self.brace_depth < self.header_brace_depth {
                    self.pending_header = false;
                }
            }
            // A written separator ends the statement, as an inserted one does.
            TokType::Semicolon => {
                self.pending_header = false;
                self.pending_entry_body = false;
            }
            // A `,` ends one too, but only where it stands at the header's own
            // bracket depth. The commas of a parameter list, of an argument
            // list and of a tuple type are inside a bracket the header itself
            // opened -- they separate nothing it has finished, and the body is
            // still to come: `fn divmod(a: i32, b: i32): (i32, i32) {`. A
            // shallower depth than the header's means the bracket it stood in
            // has closed and the header went with it.
            //
            // A generic parameter list is that same bracket written `<..>`,
            // which `bracket_depth` does not count: the commas of `struct
            // Pair<A, B> {` separate parameters of the header itself, so the
            // brace after them is still its body. `generic_depth` is settled
            // above, before this runs.
            TokType::Comma
                if self.bracket_depth <= self.header_depth && self.generic_depth == 0 =>
            {
                self.pending_header = false;
                self.pending_entry_body = false;
            }
            // The flags survive the rest of the header — a name, generic
            // parameters, a scrutinee expression — until its `{` claims them.
            t if heads_a_body(t) => {
                // `unsafe` heads a body only where a `{` really follows it.
                // Every other keyword here is followed by one eventually; this
                // one may prefix any statement instead, and then the next brace
                // belongs to that statement — the literal in `unsafe p = P {
                // x: 1 }` — and a waiting header would swallow it.
                //
                // `fn` heads one only where a name follows. A declaration is
                // `fn` and a name; a fn *type* is `fn` and a `(`, and it has no
                // body at all — a waiting header set inside a parameter list
                // would outlive the list and claim the declaration's own brace.
                let heads = match t {
                    TokType::Unsafe => self.brace_follows(),
                    TokType::Fn => self.name_follows(),
                    _ => true,
                };
                if heads {
                    self.pending_header = true;
                    self.header_depth = self.bracket_depth;
                    self.header_brace_depth = self.brace_depth;
                    // Of those, only these three hold comma-separated entries.
                    if matches!(t, TokType::Struct | TokType::Enum | TokType::Match) {
                        self.pending_entry_body = true;
                    }
                }
            }
            _ => {}
        }

        // `%repr` is one token, so an attribute with no arguments needs nothing
        // tracked: the token ends no operand and no separator can follow it.
        // What still needs tracking is the `)` of `%repr(C)`, which does end
        // one -- so the wait is opened only by a name with a glued `(`, as the
        // `[` of the old `#[...]` was glued. A space there ends the attribute at
        // its name and leaves the parenthesis for the parser to complain about.
        if matches!(tok.toktype, TokType::AttrName(_)) && self.peek_char() == Some('(') {
            self.in_attribute = true;
            self.attr_bracket_depth = self.bracket_depth;
        } else if self.in_attribute {
            if tok.toktype == TokType::RParen && self.bracket_depth == self.attr_bracket_depth {
                self.in_attribute = false;
                // The `)` of `%repr(C)` closes the attribute and not an
                // operand, so the `%` of the next one in the list is an
                // attribute too. Left alone, that `)` would make it the
                // remainder operator -- see `read_operator`, which asks
                // exactly this.
                self.last_ends_operand = false;
            }
        }

        // `pub(suite)` waits the same way, and for the same reason one line
        // down: its `)` ends a visibility, so a newline after it must not be
        // read as the end of a statement. `pub` on a line of its own is a
        // declaration missing everything after it either way.
        if tok.toktype == TokType::Pub && self.peek_char() == Some('(') {
            self.in_visibility = true;
            self.vis_bracket_depth = self.bracket_depth;
        } else if self.in_visibility
            && tok.toktype == TokType::RParen
            && self.bracket_depth == self.vis_bracket_depth
        {
            self.in_visibility = false;
            self.last_ends_operand = false;
        }
        // Everything above reads the brace as the `{` it was scanned as; only
        // what leaves the lexer says which kind it opened.
        if opens_value {
            tok.toktype = TokType::LCurlyValue;
        }
        if opens_generic {
            tok.toktype = TokType::LessGeneric;
        }
        // What the scan consumed is what was written: a `>` that split off a
        // `>>` moved one character and is one wide, and an EOF moved none.
        //
        // The one place a width is worked out. Every `Tok` a scan builds leaves
        // it at zero, because none of them knows where its own token began --
        // that is `start` above, and it is only in scope here.
        tok.len = self.index - start;
        tok
    }
}
