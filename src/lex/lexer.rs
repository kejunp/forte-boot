use crate::lex::tokens::*;

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
struct State {
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
enum BraceScan {
    // A `,` or `:` turned up between its entries: a map or a set.
    Collection,
    // A `;` or a keyword no expression can start with: statements.
    Block,
    // Neither — `{}` or `{ x }`, which read equally well as both.
    Undecided,
}

// Whether a token ends an operand — a value or a type — and so stands where an
// infix operator may follow. This tells the two readings of `&&` apart: an
// operand in front makes it the logical operator, none makes it two prefix `&`.
fn ends_an_operand(t: &TokType) -> bool {
    matches!(
        t,
        TokType::Identifier(_)
            | TokType::IntLiteral(..)
            | TokType::FloatLiteral(..)
            | TokType::StringLiteral(_)
            | TokType::CharLiteral(_)
            | TokType::True
            | TokType::False
            | TokType::SelfKw
            // A literal, and a type name besides.
            | TokType::Null
            // A wildcard names a binding, so it stands where a name stands.
            | TokType::Underscore
            // `$x` stands where a name stands too, in whichever of the three
            // positions its fragment lets it.
            | TokType::MacroParam(_)
            | TokType::RParen
            | TokType::RBracket
            | TokType::RCurlyBracket
            // A type name ends a type, which is an operand for this purpose:
            // the `&&` of a bound list follows one.
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64 | TokType::I128
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64 | TokType::U128
            | TokType::F32 | TokType::F64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Never
    )
}

// Whether a token can end a statement, making it a candidate for an inserted
// separator at a newline. Everything that ends an operand does, plus three
// keywords and a `..` that no operator could take.
fn can_end_statement(t: &TokType) -> bool {
    ends_an_operand(t)
        || matches!(
            t,
            TokType::Return
                | TokType::Break
                | TokType::Continue
                // An open range is a complete expression: `let rest = 1..`.
                // `..=` is not — it always needs an upper bound — so it keeps
                // looking.
                | TokType::DotDot
                // `::*` ends the import it globs, so one may drop its `;` like
                // any other declaration. It is not in `ends_an_operand`: no
                // infix operator may follow a glob. `super` and `suite` are in
                // neither list — each opens a path and no path ends on one.
                | TokType::Glob
        )
}

// Tokens that can appear inside a `<...>` type argument list. `<` is ambiguous
// — `Vec<i32>` opens a generic, `a < b` compares — so the lexer opens a generic
// context after a name and abandons it at the first token no type argument could
// contain. Only `>>` splitting and semicolon insertion depend on the guess.
fn fits_in_generics(t: &TokType) -> bool {
    matches!(
        t,
        TokType::Identifier(_)
            | TokType::Comma
            // Trait bounds, e.g. `<T: Show + Clone>`.
            | TokType::Colon
            | TokType::Plus
            // A lifetime parameter or argument, e.g. `<'a>`, `<'a, T>`, and the
            // `'a` of a `&'a i32` nested in one.
            | TokType::Lifetime(_)
            // A macro's parameter standing in for a type: `Vec<$t>`.
            | TokType::MacroParam(_)
            // An inferred type argument, e.g. `Vec<_>`.
            | TokType::Underscore
            // A qualified type name, e.g. `<limits::Kind>`. A type path is all
            // `::`, so a `.` inside one says the `<` was a comparison.
            | TokType::ColonColon
            // The roots one may start from, e.g. `<super::Node>`, `<Vec<self::T>>`.
            | TokType::SelfKw
            | TokType::Super
            | TokType::Suite
            // A grouped type, e.g. `<(&i32)[8]>`.
            | TokType::LParen
            | TokType::RParen
            // An array size, e.g. `<i32[8]>`. A literal cannot *start* a type
            // argument, but `<array_suffix>` takes a constant expression, so
            // one may well turn up inside it.
            | TokType::IntLiteral(..)
            // Nested arguments and array types, e.g. `<Map<str, i32[]>>`.
            | TokType::LessThan
            | TokType::GreaterThan
            | TokType::LBracket
            | TokType::RBracket
            // Reference types, e.g. `<&i32>`, `<Map<str, *Node>>`. `&&` is not
            // here: a `<` in front of one was a comparison.
            | TokType::Ampersand
            | TokType::Star
            // A pointer type, e.g. `<ptr u8>`.
            | TokType::Ptr
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64 | TokType::I128
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64 | TokType::U128
            | TokType::F32 | TokType::F64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Never
            // `null` names a type as well as a value: `Map<str, null>`.
            | TokType::Null
    )
}

// Characters that continue the previous line rather than starting a new
// statement, so no semicolon is inserted before them.
fn starts_continuation(c: char) -> bool {
    matches!(
        c,
        '.' | '+' | '-' | '*' | '/' | '%' | '=' | '<' | '>' | '&' | '|' | '^' | ',' | ':'
    )
}

// The ones that still continue a line ending in the `}` of a *block*. A block
// expression is never an operand, so a block's `}` ends a statement and the `-1`
// of `match x { ... }` / newline / `-1` stands alone. What survives here is
// punctuation that separates rather than operates — a leading `,`, a `:`.
//
// A literal's `}` closes a value, not a statement, so none of this applies to it
// and a chained `.norm()` on the next line still continues the line.
// `push_brace` tells the two apart.
fn continues_after_brace(c: char) -> bool {
    matches!(c, ',' | ':')
}

// Keywords whose header runs up to the `{` that opens their body. The header is
// what makes a `{` decidable: inside one, the first `{` at the bracket and brace
// depth the keyword was seen at opens the body, which is what the grammar buys
// by banning a struct literal from the top level of a header (section 5.1).
// Outside one, a `{` straight after a type name is a struct literal.
//
// Collection literals are the exception, handled in `push_brace`: one may stand
// at the top level of a header. `else` is here with an empty header, since
// nothing can stand between it and its `{`.
fn heads_a_body(t: &TokType) -> bool {
    matches!(
        t,
        TokType::If
            | TokType::Elif
            | TokType::Else
            | TokType::While
            | TokType::For
            | TokType::Match
            | TokType::Fn
            | TokType::Struct
            | TokType::Enum
            | TokType::Trait
            | TokType::Impl
            // Its body holds items, so it is a statement body like a fn's.
            | TokType::Namespace
            | TokType::Type
            // A macro's body is a block, and its `{` is claimed the way a fn's
            // is -- across the commas of its own parameter list.
            | TokType::Macro
            // The one whose body is optional: `unsafe` prefixes any statement
            // at all, and only the `{` of a block is a body. `brace_follows`
            // is what decides, at the one place this is asked.
            | TokType::Unsafe
    )
}

// Keywords that can only begin a statement, so a `{` holding one holds
// statements. Inside a brace they appear only at its top level and only before
// the first `;`, which is as far as `scan_brace_body` looks. The control-flow
// keywords are absent on purpose: they are expressions, so one may be an element
// of a set as easily as the start of a statement.
fn starts_statement(t: &TokType) -> bool {
    matches!(
        t,
        TokType::Let
            | TokType::Var
            | TokType::Const
            | TokType::Return
            | TokType::Break
            | TokType::Continue
            | TokType::Fn
            | TokType::Struct
            | TokType::Enum
            | TokType::Trait
            | TokType::Impl
            | TokType::Import
            | TokType::Namespace
            | TokType::Pub
            | TokType::Priv
            // It prefixes a statement, so it is the start of one.
            | TokType::Unsafe
            // An attribute only ever prefixes a declaration.
            | TokType::AttrName(_)
            // `macro` declares one, so it begins a declaration like `fn`.
            | TokType::Macro
    )
}

// Keywords that continue the previous statement, e.g. the `else` in `}` /
// newline / `else {`. No statement begins with one, so a line that starts with
// one is always a continuation.
fn continues_statement(word: &str) -> bool {
    // `where` is here so a signature may put its bounds on the next line.
    matches!(word, "else" | "elif" | "as" | "in" | "where")
}

// Base prefixes accepted after a leading `0`, e.g. `0xFF`, `0b1010`.
fn radix_of(c: char) -> Option<u32> {
    match c {
        'x' | 'X' => Some(16),
        'o' | 'O' => Some(8),
        't' | 'T' => Some(3),
        'b' | 'B' => Some(2),
        'd' | 'D' => Some(10),
        _ => None,
    }
}

// A token that is nothing but the complaint it carries. `len` is 0 like every
// other token's: what a diagnostic underlines is the report's to work out.
fn bad(message: String, line: usize, col: usize) -> Tok {
    Tok { toktype: TokType::Error(message), line, col, len: 0 }
}

// A word glued to a number that names no type. Spelled out in full, since the
// twelve are the whole of what may be written there.
fn suffix_error(word: &str, literal: &str) -> String {
    format!(
        "Unknown suffix '{}' on number literal '{}'; expected one of i8, i16, i32, i64, \
         i128, u8, u16, u32, u64, u128, f32, f64",
        word, literal
    )
}

// Reserved words. Anything not listed here lexes as an `Identifier`.
fn keyword_of(word: &str) -> Option<TokType> {
    let tok = match word {
        // Types
        "i8" => TokType::I8,
        "i16" => TokType::I16,
        "i32" => TokType::I32,
        "i64" => TokType::I64,
        "i128" => TokType::I128,
        "u8" => TokType::U8,
        "u16" => TokType::U16,
        "u32" => TokType::U32,
        "u64" => TokType::U64,
        "u128" => TokType::U128,
        "f32" => TokType::F32,
        "f64" => TokType::F64,
        "bool" => TokType::Bool,
        "char" => TokType::Char,
        "str" => TokType::Str,
        "never" => TokType::Never,
        "ptr" => TokType::Ptr,

        // Declarations
        "fn" => TokType::Fn,
        "let" => TokType::Let,
        "var" => TokType::Var,
        "const" => TokType::Const,
        "struct" => TokType::Struct,
        "trait" => TokType::Trait,
        "type" => TokType::Type,
        "impl" => TokType::Impl,
        "pub" => TokType::Pub,
        "priv" => TokType::Priv,
        "import" => TokType::Import,
        "suite" => TokType::Suite,
        "super" => TokType::Super,
        "enum" => TokType::Enum,
        "namespace" => TokType::Namespace,
        "macro" => TokType::Macro,
        "unsafe" => TokType::Unsafe,
        "gc" => TokType::Gc,

        // Control flow
        "if" => TokType::If,
        "elif" => TokType::Elif,
        "else" => TokType::Else,
        "while" => TokType::While,
        "for" => TokType::For,
        "in" => TokType::In,
        "return" => TokType::Return,
        "break" => TokType::Break,
        "continue" => TokType::Continue,
        "match" => TokType::Match,

        // Type operators
        "as" => TokType::As,
        "where" => TokType::Where,
        "move" => TokType::Move,
        "addr" => TokType::Addr,

        // Literals
        "true" => TokType::True,
        "false" => TokType::False,
        "self" => TokType::SelfKw,
        "null" => TokType::Null,

        // The wildcard. Reserved as a whole word and not as a prefix, so `_foo`
        // and `__` fall through and lex as the identifiers they are.
        "_" => TokType::Underscore,

        _ => return None,
    };
    Some(tok)
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Lexer {
            input: input.chars().collect(),
            index: 0,
            line:  1,
            col:   1,

            last_can_end:      false,
            last_closed_block: false,
            bracket_depth:     0,
            // Nothing precedes the first token, so a `&&` there is two `&`.
            last_ends_operand: false,

            in_attribute:       false,
            attr_bracket_depth: 0,
            in_visibility:      false,
            vis_bracket_depth:  0,

            brace_depth:        0,
            entry_braces:       0,
            value_braces:       0,
            pending_entry_body: false,
            pending_header:     false,
            header_depth:       0,
            header_brace_depth: 0,

            hash_prefix:    false,
            path_prefix:    false,
            // Nothing precedes the first token, and a statement may start there.
            prev_ends_stmt: true,
            prev_was_brace: false,
            prev_was_dot:   false,

            generic_depth:     0,
            last_was_name:     false,
            last_was_impl:     false,
            last_was_type_end: false,
            last_was_decl_kw: false,
            last_was_decl_name: false,
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.input.get(self.index).copied()
    }

    fn peek_char_at(&self, offset: usize) -> Option<char> {
        self.input.get(self.index + offset).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek_char();
        if let Some(c) = ch {
            self.index += 1;
            if c == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        ch
    }

    fn save(&self) -> State {
        State {
            index: self.index,
            line:  self.line,
            col:   self.col,

            last_can_end:      self.last_can_end,
            last_closed_block: self.last_closed_block,
            bracket_depth:     self.bracket_depth,
            last_ends_operand: self.last_ends_operand,

            in_attribute:       self.in_attribute,
            attr_bracket_depth: self.attr_bracket_depth,

            in_visibility:      self.in_visibility,
            vis_bracket_depth:  self.vis_bracket_depth,

            brace_depth:        self.brace_depth,
            entry_braces:       self.entry_braces,
            value_braces:       self.value_braces,
            pending_entry_body: self.pending_entry_body,
            pending_header:     self.pending_header,
            header_depth:       self.header_depth,
            header_brace_depth: self.header_brace_depth,

            hash_prefix:    self.hash_prefix,
            path_prefix:    self.path_prefix,
            prev_ends_stmt: self.prev_ends_stmt,
            prev_was_brace: self.prev_was_brace,
            prev_was_dot:   self.prev_was_dot,

            generic_depth:     self.generic_depth,
            last_was_name:     self.last_was_name,
            last_was_impl:     self.last_was_impl,
            last_was_type_end: self.last_was_type_end,
            last_was_decl_kw: self.last_was_decl_kw,
            last_was_decl_name: self.last_was_decl_name,
        }
    }

    fn restore(&mut self, s: State) {
        self.index = s.index;
        self.line = s.line;
        self.col = s.col;

        self.last_can_end = s.last_can_end;
        self.last_closed_block = s.last_closed_block;
        self.bracket_depth = s.bracket_depth;
        self.last_ends_operand = s.last_ends_operand;
        self.in_attribute = s.in_attribute;
        self.attr_bracket_depth = s.attr_bracket_depth;
        self.in_visibility = s.in_visibility;
        self.vis_bracket_depth = s.vis_bracket_depth;

        self.brace_depth = s.brace_depth;
        self.entry_braces = s.entry_braces;
        self.value_braces = s.value_braces;
        self.pending_entry_body = s.pending_entry_body;
        self.pending_header = s.pending_header;
        self.header_depth = s.header_depth;
        self.header_brace_depth = s.header_brace_depth;

        self.hash_prefix = s.hash_prefix;
        self.path_prefix = s.path_prefix;
        self.prev_ends_stmt = s.prev_ends_stmt;
        self.prev_was_brace = s.prev_was_brace;
        self.prev_was_dot = s.prev_was_dot;

        self.generic_depth = s.generic_depth;
        self.last_was_name = s.last_was_name;
        self.last_was_impl = s.last_was_impl;
        self.last_was_type_end = s.last_was_type_end;
        self.last_was_decl_kw = s.last_was_decl_kw;
        self.last_was_decl_name = s.last_was_decl_name;
    }

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
                if *t != TokType::Unsafe || self.brace_follows() {
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
    fn push_brace(
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
        let mut prev_can_end = false;
        let verdict = loop {
            // `scan_token` reads from where it stands; only `next_token` skips
            // ahead, and this look is taken without it.
            let crossed_newline = self.skip_whitespace();
            if depth == 0 && crossed_newline && prev_can_end && self.breaks_statement(false) {
                break BraceScan::Block;
            }
            let tok = self.scan_token();
            prev_can_end = can_end_statement(&tok.toktype);
            // Kept up to date through the look so a `&&` inside the body reads
            // the same here as it will when the body is really scanned, and a
            // `.0` the same. The rewind below puts them back.
            self.last_ends_operand = ends_an_operand(&tok.toktype);
            self.prev_was_dot = tok.toktype == TokType::Dot;
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
                TokType::Comma | TokType::Colon if depth == 0 => break BraceScan::Collection,
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
    fn opens_type_args(&mut self) -> bool {
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
    fn in_entry_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.entry_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    // Whether the innermost open brace closes a value — a struct, map or set
    // literal's — rather than a statement.
    fn in_value_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.value_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    // Decides whether to synthesize a separator at the current position.
    fn wants_separator(&self, crossed_newline: bool) -> bool {
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
    fn brace_follows(&self) -> bool {
        let mut i = self.index;
        while let Some(&c) = self.input.get(i) {
            if !c.is_whitespace() {
                return c == '{';
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

    fn scan_token(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;

        let c = match self.peek_char() {
            Some(c) => c,
            None => return Tok { toktype: TokType::EOF, line, col, len: 0 },
        };

        if c.is_ascii_digit() {
            return self.read_number();
        }
        if c.is_alphabetic() || c == '_' {
            return self.read_word();
        }

        match c {
            '"' => self.read_str(false),
            '`' => self.read_str(true),
            // `'a` is a lifetime and `'a'` a character. Which one is settled
            // by looking past the name for the closing quote -- see below.
            '\'' => {
                if self.opens_lifetime() {
                    self.read_lifetime()
                } else {
                    self.read_char()
                }
            }
            '@' => self.read_sigil_name('@'),
            '$' => self.read_sigil_name('$'),
            _ => self.read_operator(),
        }
    }

    // Consumes `expected` if it is next, reporting whether it did.
    fn eat(&mut self, expected: char) -> bool {
        if self.peek_char() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    // Reads one operator or delimiter, longest match first.
    fn read_operator(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        let c = match self.advance() {
            Some(c) => c,
            None => return Tok { toktype: TokType::EOF, line, col, len: 0 },
        };

        let toktype = match c {
            '+' => if self.eat('=') { TokType::PlusEquals } else { TokType::Plus },
            // `->` never reaches here; `next_token` consumes it as a line
            // continuation before dispatching.
            '-' => if self.eat('=') { TokType::MinusEquals } else { TokType::Minus },
            '*' => if self.eat('=') { TokType::StarEquals } else { TokType::Star },
            '/' => if self.eat('=') { TokType::SlashEquals } else { TokType::Slash },
            '%' => {
                // The same question `*` answers: an operand in front makes it
                // the operator, and nothing in front makes it the other thing.
                // `a % b` and `a%b` are remainders; a `%` beginning a line, or
                // following a `;` or a `{`, is an attribute's name.
                if !self.last_ends_operand
                    && matches!(self.peek_char(), Some(n) if n.is_alphabetic() || n == '_')
                {
                    return self.finish_sigil_name(line, col);
                }
                TokType::Percent
            }

            '=' => {
                if self.eat('=') { TokType::EqualsEquals }
                else if self.eat('>') { TokType::FatArrow }
                else { TokType::Equals }
            }
            '!' => if self.eat('=') { TokType::BangEquals } else { TokType::Bang },

            '<' => {
                if self.eat('<') {
                    if self.eat('=') { TokType::LShiftEquals } else { TokType::LShift }
                } else if self.eat('=') {
                    TokType::LessOrEqual
                } else {
                    TokType::LessThan
                }
            }
            '>' => {
                // Inside a type argument list every `>` closes one level, so the
                // `>>` ending `Map<str, List<i32>>` is two closers, not a shift.
                if self.generic_depth > 0 {
                    TokType::GreaterThan
                } else if self.eat('>') {
                    if self.eat('=') { TokType::RShiftEquals } else { TokType::RShift }
                } else if self.eat('=') {
                    TokType::GreaterOrEqual
                } else {
                    TokType::GreaterThan
                }
            }

            // A lone `&` takes an immutable reference — `&x`, `&i32` — and `&&`
            // is either the logical operator or two of those, which is decided
            // by what stands in front of it: an operand makes it infix, and no
            // operand makes it a pair of prefixes. Only the first `&` is taken
            // in that case, so the second is scanned on its own and `&&&T` needs
            // no further thought. This is how `>>` is split in a type argument
            // list, asked of the other side of the token.
            '&' => {
                if self.last_ends_operand && self.eat('&') { TokType::And }
                else if self.eat('=') { TokType::AndEquals }
                else { TokType::Ampersand }
            }
            // A lone `|` separates the alternatives of a pattern and delimits a
            // closure's parameters, so `||` is split the same way `&&` is: an
            // operand in front of it makes it the logical operator, and none
            // makes it two `|` — which is how a closure of no parameters,
            // `|| f()`, is told from a disjunction.
            '|' => {
                if self.last_ends_operand && self.eat('|') { TokType::Or }
                else if self.eat('=') { TokType::OrEquals }
                else { TokType::Pipe }
            }

            // `^` is exclusive or on the bits and `^^` the same on two
            // booleans. Neither `&`'s question nor `|`'s arises: nothing is
            // written with a prefix `^`, so what stands in front of it decides
            // nothing and a doubled one is always the logical operator.
            '^' => {
                if self.eat('^') { TokType::Xor }
                else if self.eat('=') { TokType::CaretEquals }
                else { TokType::Caret }
            }

            '(' => TokType::LParen,
            ')' => TokType::RParen,
            '[' => TokType::LBracket,
            ']' => TokType::RBracket,
            '{' => TokType::LCurlyBracket,
            '}' => TokType::RCurlyBracket,
            // `::` reaches into a type — `Color::Red` — where `:` annotates one,
            // and `::*` glued to it is the glob of an import. A `*` can only
            // ever follow a `::` there, so taking it here costs nothing and buys
            // the glob a token that ends an operand: see `TokType::Glob`.
            ':' => {
                if self.eat(':') {
                    if self.eat('*') { TokType::Glob } else { TokType::ColonColon }
                } else {
                    TokType::Colon
                }
            }
            ',' => TokType::Comma,
            '.' => {
                if self.eat('.') {
                    if self.eat('=') { TokType::DotDotEquals } else { TokType::DotDot }
                } else {
                    TokType::Dot
                }
            }
            ';' => TokType::Semicolon,
            '#' => TokType::HashTag,

            _ => TokType::Error(format!("Unexpected character '{}'", c)),
        };

        Tok { toktype, line, col, len: 0 }
    }

    // Skips whitespace, reporting whether any of it was a line break.
    fn skip_whitespace(&mut self) -> bool {
        let mut crossed_newline = false;
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() {
                if c == '\n' {
                    crossed_newline = true;
                }
                self.advance();
            } else {
                break;
            }
        }
        crossed_newline
    }

    fn read_str(&mut self, is_backtick: bool) -> Tok {
        let line = self.line;
        let col = self.col;
        let quote = if is_backtick { '`' } else { '"' };
        let mut s = String::new();
        self.advance(); // opening quote
        while let Some(c) = self.advance() {
            if c == quote {
                return Tok { toktype: TokType::StringLiteral(s), line, col, len: 0 };
            } else if c == '\\' && !is_backtick {
                match self.read_escape() {
                    Ok(ch) => s.push(ch),
                    Err(e) => return Tok { toktype: TokType::Error(e), line, col, len: 0 },
                }
            } else {
                s.push(c);
            }
        }
        Tok { toktype: TokType::Error("Unterminated string".to_string()), line, col, len: 0 }
    }

    fn read_char(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        self.advance(); // opening quote
        let value = match self.advance() {
            Some('\'') => {
                return Tok { toktype: TokType::Error("Empty character literal".to_string()), line, col, len: 0 };
            }
            Some('\\') => match self.read_escape() {
                Ok(c) => c,
                Err(e) => return Tok { toktype: TokType::Error(e), line, col, len: 0 },
            },
            Some(c) => c,
            None => {
                return Tok { toktype: TokType::Error("Unterminated character literal".to_string()), line, col, len: 0 };
            }
        };

        if self.peek_char() != Some('\'') {
            // Skip to the closing quote so one bad literal doesn't cascade.
            while let Some(c) = self.peek_char() {
                if c == '\n' {
                    break;
                }
                self.advance();
                if c == '\'' {
                    break;
                }
            }
            return Tok {
                toktype: TokType::Error("Character literal must contain exactly one character".to_string()),
                line,
                col,
                len: 0,
            };
        }
        self.advance(); // closing quote
        Tok { toktype: TokType::CharLiteral(value), line, col, len: 0 }
    }

    // Reads a lifetime, `'a`, its `'` known to open one by `opens_lifetime`.
    //
    // The name follows an identifier's rules, so `'_` is the one with no name
    // worth giving and `'1` is not a lifetime at all -- it is the start of a
    // character literal the reader below will complain about.
    // Reads `@name`, `$name` and the `%name` of an attribute. The sigil is
    // already known to be one of those and is consumed here; what each becomes
    // is `finish_sigil_name`'s, which the `%` of `read_operator` reaches
    // directly, having had to answer a question the other two never face.
    fn read_sigil_name(&mut self, sigil: char) -> Tok {
        let line = self.line;
        let col = self.col;
        self.advance(); // the sigil

        let starts = matches!(self.peek_char(), Some(c) if c.is_alphabetic() || c == '_');
        if !starts {
            let what = if sigil == '@' { "A macro is `@` and a name, as in `@println`" }
                       else { "A macro parameter is `$` and a name, as in `$x`" };
            return Tok { toktype: TokType::Error(what.to_string()), line, col, len: 0 };
        }
        let name = self.read_name();
        let toktype = if sigil == '@' {
            TokType::MacroName(name)
        } else {
            TokType::MacroParam(name)
        };
        Tok { toktype, line, col, len: 0 }
    }

    // The `%name` of an attribute, its `%` already consumed and a name known to
    // follow. `line` and `col` are the sigil's, so a message points at the whole.
    fn finish_sigil_name(&mut self, line: usize, col: usize) -> Tok {
        let name = self.read_name();
        Tok { toktype: TokType::AttrName(name), line, col, len: 0 }
    }

    // The identifier characters at the current position, which every sigil above
    // takes for its name.
    fn read_name(&mut self) -> String {
        let mut name = String::new();
        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }
        name
    }

    // Whether the `'` at the current position opens a lifetime rather than a
    // character. The two are told apart by what follows the name: `'a'` closes
    // and is a character, `'a` does not and is a lifetime.
    //
    // The look is bounded by the name, which is what makes it affordable -- it
    // never runs past the identifier, and a character literal is never longer
    // than one escape. This is Rust's rule and it is Rust's for the same reason.
    fn opens_lifetime(&self) -> bool {
        let first = match self.peek_char_at(1) {
            Some(c) => c,
            None => return false,
        };
        if !(first.is_alphabetic() || first == '_') {
            return false;
        }
        let mut at = 1;
        while matches!(self.peek_char_at(at), Some(c) if c.is_alphanumeric() || c == '_') {
            at += 1;
        }
        // A quote here closes a character literal; anything else leaves the
        // name standing on its own, which is what a lifetime is.
        self.peek_char_at(at) != Some('\'')
    }

    fn read_lifetime(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        self.advance(); // the `'`

        let mut name = String::new();
        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }
        Tok { toktype: TokType::Lifetime(name), line, col, len: 0 }
    }

    // Decodes one escape sequence. The leading `\` is already consumed.
    fn read_escape(&mut self) -> Result<char, String> {
        match self.advance() {
            Some('n') => Ok('\n'),
            Some('t') => Ok('\t'),
            Some('r') => Ok('\r'),
            Some('0') => Ok('\0'),
            Some('\\') => Ok('\\'),
            Some('"') => Ok('"'),
            Some('\'') => Ok('\''),
            Some('`') => Ok('`'),
            Some('a') => Ok('\x07'),
            Some('b') => Ok('\x08'),
            Some('f') => Ok('\x0C'),
            Some('v') => Ok('\x0B'),
            Some('x') => {
                let mut hex = String::new();
                for _ in 0..2 {
                    match self.peek_char() {
                        Some(c) if c.is_ascii_hexdigit() => {
                            hex.push(c);
                            self.advance();
                        }
                        _ => return Err("Expected two hex digits after '\\x'".to_string()),
                    }
                }
                let value = u8::from_str_radix(&hex, 16)
                    .map_err(|_| format!("Invalid '\\x' escape: '\\x{}'", hex))?;
                Ok(value as char)
            }
            Some('u') => {
                if self.advance() != Some('{') {
                    return Err("Expected '{' after '\\u'".to_string());
                }
                let mut hex = String::new();
                loop {
                    match self.peek_char() {
                        Some('}') => {
                            self.advance();
                            break;
                        }
                        Some(c) if c.is_ascii_hexdigit() => {
                            hex.push(c);
                            self.advance();
                        }
                        Some(_) => return Err("Invalid character in Unicode escape".to_string()),
                        None => return Err("Unterminated Unicode escape".to_string()),
                    }
                }
                if hex.is_empty() {
                    return Err("Empty Unicode escape".to_string());
                }
                let value = u32::from_str_radix(&hex, 16)
                    .map_err(|_| format!("Unicode escape out of range: '\\u{{{}}}'", hex))?;
                std::char::from_u32(value)
                    .ok_or_else(|| format!("Invalid Unicode code point: U+{:X}", value))
            }
            Some(c) => Err(format!("Unknown escape sequence '\\{}'", c)),
            None => Err("Unterminated escape sequence".to_string()),
        }
    }

    fn read_number(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;

        // Prefixed integer literal: `0` followed by a base marker.
        if self.peek_char() == Some('0') {
            if let Some(radix) = self.peek_char_at(1).and_then(radix_of) {
                let prefix = self.peek_char_at(1).unwrap();
                self.advance(); // '0'
                self.advance(); // base marker
                return self.read_radix_int(radix, prefix, line, col);
            }
        }

        // A number written just after a `.` is a tuple index, and a whole one:
        // the second `.` of `t.0.1` opens the next index rather than a decimal
        // point, and there is no float a lone `.` can stand in front of.
        let index = self.prev_was_dot;

        let mut is_float = false;
        let mut num_str = String::new();
        while let Some(c) = self.peek_char() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.advance();
            } else if c == '_' {
                // A digit separator: `1_000_000`. Dropped, never part of the
                // value. It cannot lead, since a word starting with `_` was
                // read as an identifier long before this.
                self.advance();
            } else if c == '.' && !is_float && !index
                && matches!(self.peek_char_at(1), Some(d) if d.is_ascii_digit())
            {
                // Only the first '.' with a digit behind it belongs to the number;
                // `1.foo` stays an int followed by a Dot.
                is_float = true;
                num_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // The type the number named for itself, `5_u8` and `2.6_f32`. The `_`
        // in front of it is the digit separator, already dropped by the loop
        // above, so `5u8` says the same thing and reads the same way.
        //
        // Not after a `.`, where the number is a tuple index: `t.0` reaches a
        // member, and a member has whatever type it has.
        let mut suffix = None;
        if !index && matches!(self.peek_char(), Some(c) if c.is_alphabetic()) {
            let word = self.read_suffix_word();
            match NumSuffix::of(&word) {
                Some(s) if is_float && !s.is_float() => {
                    self.consume_literal_tail();
                    return bad(
                        format!("Float literal '{}' cannot have the suffix '{}'", num_str, word),
                        line,
                        col,
                    );
                }
                Some(s) => suffix = Some(s),
                None => {
                    self.consume_literal_tail();
                    return bad(suffix_error(&word, &num_str), line, col);
                }
            }
        }

        // Reject junk glued to the literal: `1.2.3`, and the `abc` of `t.0abc`,
        // which the suffix above did not take because an index carries none. A
        // second '.' can only appear here once `is_float` is set, so this
        // catches a repeated decimal point without touching `1..2`, where the
        // dots are a range.
        if let Some(c) = self.peek_char() {
            let bad_dot = !index
                && c == '.'
                && matches!(self.peek_char_at(1), Some(d) if d.is_ascii_digit());
            if bad_dot || c.is_alphabetic() {
                self.consume_literal_tail();
                return bad(format!("Malformed number literal '{}'", num_str), line, col);
            }
        }

        // A float suffix on a whole number makes a float of it: `5_f32` is the
        // same value as `5.0_f32`, said with the point left out.
        if is_float || suffix.is_some_and(NumSuffix::is_float) {
            match num_str.parse::<f64>() {
                Ok(v) => Tok { toktype: TokType::FloatLiteral(v, suffix), line, col, len: 0 },
                Err(_) => bad(format!("Invalid float literal '{}'", num_str), line, col),
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(v) => Tok { toktype: TokType::IntLiteral(v, suffix), line, col, len: 0 },
                Err(_) => {
                    bad(format!("Integer literal '{}' out of range for i64", num_str), line, col)
                }
            }
        }
    }

    // The word glued to the end of a number, which is meant to be a suffix.
    // Read whole, valid or not, so a wrong one is named in full by the error.
    fn read_suffix_word(&mut self) -> String {
        let mut word = String::new();
        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
                self.advance();
            } else {
                break;
            }
        }
        word
    }

    fn read_radix_int(&mut self, radix: u32, prefix: char, line: usize, col: usize) -> Tok {
        let mut digits = String::new();
        let mut suffix = None;
        // A digit of some other base, and a word that was meant to be a suffix
        // and is not. Kept apart so the error names whichever came first.
        let mut bad_digit = false;
        let mut junk = None;
        while let Some(c) = self.peek_char() {
            if c.is_digit(radix) {
                digits.push(c);
                self.advance();
            } else if c == '_' {
                // A digit separator: `0xFF_FF`.
                self.advance();
            } else if c == '.' && self.peek_char_at(1) == Some('.') {
                // `0x10..0x20` — the dots are a range, not part of the literal.
                break;
            } else if c.is_alphabetic() {
                // A letter that is no digit of this base opens the suffix:
                // `0xFF_u8`, `0b1010_i32`. The digits above were taken as
                // greedily as ever, so a suffix spelled in them is not one --
                // `0x1_f32` is the number 0x1f32, and every hex float with it.
                let word = self.read_suffix_word();
                match NumSuffix::of(&word) {
                    Some(s) => suffix = Some(s),
                    None => junk = Some(word),
                }
                break;
            } else if c.is_numeric() || c == '.' {
                // A digit outside this base, or a decimal point: consume it so the
                // error covers the whole malformed literal.
                bad_digit = true;
                self.advance();
            } else {
                break;
            }
        }

        if bad_digit || junk.is_some() {
            let literal = format!("0{}{}", prefix, digits);
            self.consume_literal_tail();
            return match junk {
                Some(word) if !bad_digit => bad(suffix_error(&word, &literal), line, col),
                _ => bad(
                    format!("Invalid digit in base-{} literal '{}'", radix, literal),
                    line,
                    col,
                ),
            };
        }
        if digits.is_empty() {
            return bad(format!("Expected digits after '0{}'", prefix), line, col);
        }
        match i64::from_str_radix(&digits, radix) {
            // A float suffix makes a float of the number it was written on, as
            // it does in `5_f32`. The base said how to read the digits, and
            // nothing more: `0b1010_f32` is 10.0.
            Ok(v) if suffix.is_some_and(NumSuffix::is_float) => {
                Tok { toktype: TokType::FloatLiteral(v as f64, suffix), line, col, len: 0 }
            }
            Ok(v) => Tok { toktype: TokType::IntLiteral(v, suffix), line, col, len: 0 },
            Err(_) => bad(
                format!("Integer literal '0{}{}' out of range for i64", prefix, digits),
                line,
                col,
            ),
        }
    }

    // Reads an identifier or a keyword. Assumes the current char is a valid
    // identifier start (alphabetic or `_`).
    fn read_word(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        let mut word = String::new();
        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if word.is_empty() {
            return Tok {
                toktype: TokType::Error("Expected an identifier".to_string()),
                line,
                col,
                len: 0,
            };
        }

        let toktype = keyword_of(&word).unwrap_or(TokType::Identifier(word));
        Tok { toktype, line, col, len: 0 }
    }

    // Swallow the rest of a malformed literal so the next token starts clean.
    // Stops at `..` so one bad literal doesn't eat the range operator behind it.
    fn consume_literal_tail(&mut self) {
        while let Some(c) = self.peek_char() {
            if c == '.' && self.peek_char_at(1) == Some('.') {
                break;
            }
            if c.is_alphanumeric() || c == '_' || c == '.' {
                self.advance();
            } else {
                break;
            }
        }
    }
}
