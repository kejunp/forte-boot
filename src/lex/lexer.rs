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
    prev_ends_stmt: bool,
    prev_was_brace: bool,

    // Generic argument list state.
    generic_depth:     usize,
    last_was_name:     bool,
    last_was_impl:     bool,
    last_was_type_end: bool,
}

/// Everything `next_token` mutates, so that a lookahead can be rolled back.
/// The input itself never changes, so it stays out of the snapshot.
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

    brace_depth:        usize,
    entry_braces:       u64,
    value_braces:       u64,
    pending_entry_body: bool,
    pending_header:     bool,
    header_depth:       usize,
    header_brace_depth: usize,

    hash_prefix:    bool,
    prev_ends_stmt: bool,
    prev_was_brace: bool,

    generic_depth:     usize,
    last_was_name:     bool,
    last_was_impl:     bool,
    last_was_type_end: bool,
}

/// What a look inside a `{` says about the kind of body it opens. See
/// `scan_brace_body`.
enum BraceScan {
    /// A `,` or `:` turned up between its entries: a map or a set.
    Collection,
    /// A `;` or a keyword no expression can start with: statements.
    Block,
    /// Neither — `{}` or `{ x }`, which read equally well as both.
    Undecided,
}

/// Whether a token ends an operand — a value or a type — and so stands where an
/// *infix* operator may follow.
///
/// This is what tells the two readings of `&&` apart: an operand in front of it
/// makes it the logical operator, and no operand makes it two prefix `&`. See
/// `read_operator`.
fn ends_an_operand(t: &TokType) -> bool {
    matches!(
        t,
        TokType::Identifier(_)
            | TokType::IntLiteral(_)
            | TokType::FloatLiteral(_)
            | TokType::StringLiteral(_)
            | TokType::CharLiteral(_)
            | TokType::True
            | TokType::False
            | TokType::This
            // A literal, and a type name besides.
            | TokType::Null
            // A wildcard names a binding, so it stands where a name stands.
            | TokType::Underscore
            | TokType::RParen
            | TokType::RBracket
            | TokType::RCurlyBracket
            // A type name ends a type, which is an operand for this purpose:
            // the `&&` of a bound list follows one.
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64
            | TokType::F32 | TokType::F64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Never
    )
}

/// Whether a token can legally end a statement, making it a candidate for a
/// separator to be inserted after it at a newline.
///
/// Everything that ends an operand does, and three keywords and a `..` besides,
/// which end a statement without being anything an operator could take.
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
        )
}

/// Tokens that can legally appear inside a `<...>` type argument list.
///
/// `<` is ambiguous — `Vec<i32>` opens a generic, `a < b` is a comparison — and
/// a lexer cannot tell them apart. So the lexer optimistically opens a generic
/// context after a name and abandons it the moment something turns up that no
/// type argument could contain. Only `>>` splitting and semicolon insertion
/// depend on the guess, so a wrong one stays cheap.
fn fits_in_generics(t: &TokType) -> bool {
    matches!(
        t,
        TokType::Identifier(_)
            | TokType::Comma
            // Trait bounds, e.g. `<T: Show + Clone>`.
            | TokType::Colon
            | TokType::Plus
            // An inferred type argument, e.g. `Vec<_>`.
            | TokType::Underscore
            // A qualified type name, e.g. `<limits::Kind>`. A type path is all
            // `::`, so a `.` inside one says the `<` was a comparison.
            | TokType::ColonColon
            // A grouped type, e.g. `<(&i32)[8]>`.
            | TokType::LParen
            | TokType::RParen
            // An array size, e.g. `<i32[8]>`. A literal cannot *start* a type
            // argument, but `<array_suffix>` takes a constant expression, so
            // one may well turn up inside it.
            | TokType::IntLiteral(_)
            // Nested arguments and array types, e.g. `<Map<str, i32[]>>`.
            | TokType::LessThan
            | TokType::GreaterThan
            | TokType::LBracket
            | TokType::RBracket
            // Reference types, e.g. `<&i32>`, `<Map<str, *Node>>`. `&&` is not
            // here: a `<` in front of one was a comparison.
            | TokType::Ampersand
            | TokType::Star
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64
            | TokType::F32 | TokType::F64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Never
            // `null` names a type as well as a value: `Map<str, null>`.
            | TokType::Null
    )
}

/// Characters that continue the previous line rather than starting a new
/// statement, so no semicolon is inserted before them.
fn starts_continuation(c: char) -> bool {
    matches!(c, '.' | '+' | '-' | '*' | '/' | '%' | '=' | '<' | '>' | '&' | '|' | ',' | ':')
}

/// The ones that still continue a line ending in the `}` of a *block*.
///
/// `if`, `while`, `for` and `match` are expressions, so a block's `}` can close
/// either a statement or an operand, and an operator on the next line is
/// ambiguous between them:
///
/// ```text
/// match x { ... }
/// -1
/// ```
///
/// A statement is overwhelmingly the common case, so a block's `}` at the end of
/// a line ends it and the `-1` stands alone. `->` splices the two lines back
/// together for the rare case that wanted an operand. What survives here is
/// punctuation that separates rather than operates — a leading `,` in an entry
/// body, a `:` — which no expression could have continued anyway.
///
/// A literal's `}` — a struct's, a map's, a set's — closes a value, not a
/// statement, so none of this applies to it and a chained `.norm()` on the next
/// line still continues the line. `push_brace` is what tells the two apart.
fn continues_after_brace(c: char) -> bool {
    matches!(c, ',' | ':')
}

/// Keywords whose header runs up to the `{` that opens their body.
///
/// The header is what makes a `{` decidable. Inside one, the first `{` at the
/// bracket *and* brace depth the keyword was seen at opens the body, and almost
/// nothing else can be there — which is what the grammar buys by banning a
/// struct literal from the top level of a header (section 5.1). Outside one, a
/// `{` straight after a type name is a struct literal.
///
/// The exception a collection literal makes to that is in `push_brace`: it may
/// stand at the top level of a header, so a body of statements gives up a brace
/// that can only be a literal.
///
/// `else` is here with an empty header: the `{` after it is its body, since
/// nothing can stand between the two.
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
    )
}

/// Keywords that can only begin a statement, so a `{` holding one holds
/// statements. Inside a brace they can only appear at its top level, and only
/// before the first `;` if they appear at all — which is exactly as far as
/// `scan_brace_body` looks.
///
/// The control-flow keywords are deliberately absent: `if`, `while`, `for` and
/// `match` are expressions, so one of them may just as well be an element of a
/// set as the start of a statement.
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
            | TokType::Public
            | TokType::Private
            // An attribute only ever prefixes a declaration.
            | TokType::At
    )
}

/// Keywords that continue the previous statement, e.g. the `else` in
/// `}` / newline / `else {`. No statement begins with one of these, so a line
/// that starts with one is always a continuation — including a cast split
/// across lines, `let n = x` / newline / `as i64`.
fn continues_statement(word: &str) -> bool {
    // `where` is here so a signature may put its bounds on the next line.
    matches!(word, "else" | "elif" | "as" | "in" | "where")
}

/// Base prefixes accepted after a leading `0`, e.g. `0xFF`, `0b1010`.
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

/// Reserved words. Anything not listed here lexes as an `Identifier`.
fn keyword_of(word: &str) -> Option<TokType> {
    let tok = match word {
        // Types
        "i8" => TokType::I8,
        "i16" => TokType::I16,
        "i32" => TokType::I32,
        "i64" => TokType::I64,
        "u8" => TokType::U8,
        "u16" => TokType::U16,
        "u32" => TokType::U32,
        "u64" => TokType::U64,
        "f32" => TokType::F32,
        "f64" => TokType::F64,
        "bool" => TokType::Bool,
        "char" => TokType::Char,
        "str" => TokType::Str,
        "never" => TokType::Never,

        // Declarations
        "fn" => TokType::Fn,
        "let" => TokType::Let,
        "var" => TokType::Var,
        "const" => TokType::Const,
        "struct" => TokType::Struct,
        "trait" => TokType::Trait,
        "impl" => TokType::Impl,
        "public" => TokType::Public,
        "private" => TokType::Private,
        "import" => TokType::Import,
        "enum" => TokType::Enum,
        "namespace" => TokType::Namespace,

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

        // Literals
        "true" => TokType::True,
        "false" => TokType::False,
        "this" => TokType::This,
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

            brace_depth:        0,
            entry_braces:       0,
            value_braces:       0,
            pending_entry_body: false,
            pending_header:     false,
            header_depth:       0,
            header_brace_depth: 0,

            hash_prefix:    false,
            // Nothing precedes the first token, and a statement may start there.
            prev_ends_stmt: true,
            prev_was_brace: false,

            generic_depth:     0,
            last_was_name:     false,
            last_was_impl:     false,
            last_was_type_end: false,
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

            brace_depth:        self.brace_depth,
            entry_braces:       self.entry_braces,
            value_braces:       self.value_braces,
            pending_entry_body: self.pending_entry_body,
            pending_header:     self.pending_header,
            header_depth:       self.header_depth,
            header_brace_depth: self.header_brace_depth,

            hash_prefix:    self.hash_prefix,
            prev_ends_stmt: self.prev_ends_stmt,
            prev_was_brace: self.prev_was_brace,

            generic_depth:     self.generic_depth,
            last_was_name:     self.last_was_name,
            last_was_impl:     self.last_was_impl,
            last_was_type_end: self.last_was_type_end,
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

        self.brace_depth = s.brace_depth;
        self.entry_braces = s.entry_braces;
        self.value_braces = s.value_braces;
        self.pending_entry_body = s.pending_entry_body;
        self.pending_header = s.pending_header;
        self.header_depth = s.header_depth;
        self.header_brace_depth = s.header_brace_depth;

        self.hash_prefix = s.hash_prefix;
        self.prev_ends_stmt = s.prev_ends_stmt;
        self.prev_was_brace = s.prev_was_brace;

        self.generic_depth = s.generic_depth;
        self.last_was_name = s.last_was_name;
        self.last_was_impl = s.last_was_impl;
        self.last_was_type_end = s.last_was_type_end;
    }

    /// Returns the token `next_token` would return, without consuming it.
    ///
    /// Lexing is context-sensitive — semicolon insertion and `>>` splitting
    /// both depend on state the scanner updates as it goes — so the token is
    /// produced by running the real scanner and rewinding it afterwards, not by
    /// a separate lookahead path that could drift out of step. Takes `&mut
    /// self` for that reason; peeking is otherwise free of side effects, and
    /// repeated peeks return the same token.
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
            return Tok { toktype: TokType::Semicolon, line, col };
        }

        // What stands in front of this token, which is what decides a `{`.
        // Captured before the scan overwrites it.
        let after_type_name = self.last_was_type_end;
        let after_hash = self.hash_prefix;
        let value_only = !self.prev_ends_stmt && !(self.prev_was_brace && !self.in_entry_body());

        let tok = self.scan_token();

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
        self.last_was_name = matches!(tok.toktype, TokType::Identifier(_));
        self.last_was_impl = tok.toktype == TokType::Impl;
        // A name, or the `>` closing its type arguments: `Point {`, `Vec<i32> {`.
        self.last_was_type_end = self.last_was_name || closed_generic;

        self.last_can_end = can_end_statement(&tok.toktype) || closed_generic;
        // An attribute is a prefix of the declaration it annotates, so nothing
        // inside one ends a statement: `@inline` / newline / `fn f()` is a
        // single item, and the name that closes the attribute must not have a
        // separator inserted after it.
        if self.in_attribute {
            self.last_can_end = false;
        }
        // The `>` closing a type argument list ends a type, and so an operand.
        self.last_ends_operand = ends_an_operand(&tok.toktype) || closed_generic;
        self.last_closed_block = false;
        // A `#` marks the brace behind it as a hash map or hash set, but only
        // when glued to it — `#{`, as `#[` opens an attribute.
        self.hash_prefix = tok.toktype == TokType::HashTag && self.peek_char() == Some('{');
        self.prev_ends_stmt = matches!(tok.toktype, TokType::Semicolon | TokType::FatArrow);
        self.prev_was_brace =
            matches!(tok.toktype, TokType::LCurlyBracket | TokType::RCurlyBracket);
        match &tok.toktype {
            TokType::LParen | TokType::LBracket => self.bracket_depth += 1,
            TokType::RParen | TokType::RBracket => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
            }
            TokType::LCurlyBracket => self.push_brace(after_type_name, after_hash, value_only),
            TokType::RCurlyBracket => {
                // Only a block's `}` ends the line it sits on; the `}` of a
                // literal — a struct's, a map's, a set's — closes a value that
                // an operator may continue.
                self.last_closed_block = !self.in_value_body();
                self.brace_depth = self.brace_depth.saturating_sub(1);
                // Whatever header was open cannot still be: a signature with no
                // body, `fn show(this): str`, gets no separator before the `}`
                // of the trait around it, and its header must not outlive it.
                self.pending_header = false;
            }
            // A written separator ends the statement, as an inserted one does.
            TokType::Semicolon | TokType::Comma => {
                self.pending_header = false;
                self.pending_entry_body = false;
            }
            // The flags survive the rest of the header — a name, generic
            // parameters, a scrutinee expression — until its `{` claims them.
            t if heads_a_body(t) => {
                self.pending_header = true;
                self.header_depth = self.bracket_depth;
                self.header_brace_depth = self.brace_depth;
                // Of those, only these three hold comma-separated entries.
                if matches!(t, TokType::Struct | TokType::Enum | TokType::Match) {
                    self.pending_entry_body = true;
                }
            }
            _ => {}
        }

        // An attribute runs from the `@` to the name after it, or to the `)`
        // closing that name's arguments. The `(` has to be glued on, as the `[`
        // of the old `#[...]` was: a space ends the attribute at the name and
        // leaves the parenthesis to the parser to complain about.
        if tok.toktype == TokType::At {
            self.in_attribute = true;
            self.attr_bracket_depth = self.bracket_depth;
        } else if self.in_attribute {
            match &tok.toktype {
                // Only the attribute's own name closes it — a name among its
                // arguments is deeper, and `@repr(C)` ends at the `)`.
                TokType::Identifier(_)
                    if self.bracket_depth == self.attr_bracket_depth
                        && self.peek_char() != Some('(') =>
                {
                    self.in_attribute = false;
                }
                TokType::RParen if self.bracket_depth == self.attr_bracket_depth => {
                    self.in_attribute = false;
                }
                _ => {}
            }
        }
        tok
    }

    /// Records what kind of body a `{` opens. There are four:
    ///
    ///   - the body of a header — the first `{` at the bracket depth an `if`,
    ///     `fn`, `match` or other body-heading keyword was seen at. Nothing
    ///     else can be there, because the grammar keeps a struct literal out of
    ///     the top level of a header;
    ///   - a struct literal, when no header claims the brace and a type name
    ///     ends immediately before it: `Point {`, `Vec<i32> {`;
    ///   - a map or set literal — `{1: 2}`, `{1, 2}`, and anything after a
    ///     glued `#`. See `opens_collection`;
    ///   - a block otherwise.
    ///
    /// Bit `n` of `entry_braces` is set when the brace at depth `n` holds
    /// comma-separated entries rather than statements — a struct, enum or match
    /// body, and every literal. Nothing is inserted inside one of those: the
    /// commas are written. Bit `n` of `value_braces` narrows that to the
    /// literals, whose `}` closes a value and so ends no line by itself either.
    ///
    /// A bitmask keeps the snapshot `Copy`, so a `peek` costs no allocation;
    /// past 64 levels of nesting the kind is no longer tracked and a body
    /// reverts to statements, which no real source reaches.
    fn push_brace(&mut self, after_type_name: bool, after_hash: bool, value_only: bool) {
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
        let collection = !literal
            && (after_hash
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
    }

    /// Whether a `{` that no header and no type name claimed opens a map or a
    /// set rather than a block.
    ///
    /// Nothing in front of the brace can say: a literal and a block stand in
    /// the same places. So the lexer looks *inside* instead, and what it finds
    /// usually settles it — statements are separated by `;` and entries by
    /// `,`, and neither separator is legal in the other's body.
    ///
    /// `{}` and `{ x }` contain neither, and there `value_only` decides: where
    /// only a value can stand — after `=`, `(`, `,`, `return`, an operator — it
    /// is a literal, so `{}` is the empty map and `{ x }` a set of one, with no
    /// trailing comma asked for. Where a statement could stand instead — at the
    /// start of one, after a `=>`, inside another block — it is a block, since
    /// that is what braces are there.
    ///
    /// The cost is that a block used as a value has to hold a statement
    /// boundary — a `;`, a line break, or a keyword only a statement starts
    /// with — which every block worth writing does, since a block of one
    /// expression is that expression. `{ f() }` after an `=` is the set of one
    /// that it looks like. The empty map can still be said in either position
    /// by writing the `:` out, `{:}`, as the empty set is `{,}`.
    fn opens_collection(&mut self, value_only: bool) -> bool {
        match self.scan_brace_body() {
            BraceScan::Collection => true,
            BraceScan::Block => false,
            BraceScan::Undecided => value_only,
        }
    }

    /// Reads ahead over the body of the `{` just scanned, stopping at the first
    /// token that tells the two kinds apart, and rewinds.
    ///
    /// Only the brace's own level counts: the `,` of `{ f(a, b) }` is the call's
    /// and the `:` of `{ Point { x: 1 } }` is the literal's, so both are skipped
    /// and the brace is left `Undecided`.
    ///
    /// A line break that would end a statement counts as a `;`, since that is
    /// what it is about to become. It has to: a block written in this language
    /// need contain no separator at all, and `{ f()` / newline / `g() }` is two
    /// statements however it is punctuated. Between entries a newline means
    /// nothing, and the `,` or `:` of a real literal is met before any newline
    /// that could be read this way.
    ///
    /// The scan runs to the end of the body in the worst case, which makes
    /// nested literals quadratic in principle. In practice it stops at the
    /// first separator, a token or two in.
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
            // the same here as it will when the body is really scanned. The
            // rewind below puts it back.
            self.last_ends_operand = ends_an_operand(&tok.toktype);
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

    /// Whether the innermost open brace holds comma-separated entries.
    fn in_entry_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.entry_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    /// Whether the innermost open brace closes a value — a struct, map or set
    /// literal's — rather than a statement.
    fn in_value_body(&self) -> bool {
        self.brace_depth > 0
            && self.brace_depth <= 64
            && self.value_braces & (1u64 << (self.brace_depth - 1)) != 0
    }

    /// Decides whether to synthesize a separator at the current position.
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

    /// Whether what stands at the current position starts a statement rather
    /// than continuing the one before it. Asked at a line break, of the line
    /// below it; end of input is left to the caller.
    ///
    /// `closed_block` says whether the token just read was the `}` of a block,
    /// which narrows what may still continue the line.
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
            Some(c) if starts_continuation(c) => false,
            Some(_) => true,
        }
    }

    /// Reads the word at the current position without consuming it.
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
            None => return Tok { toktype: TokType::EOF, line, col },
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
            '\'' => self.read_char(),
            _ => self.read_operator(),
        }
    }

    /// Consumes `expected` if it is next, reporting whether it did.
    fn eat(&mut self, expected: char) -> bool {
        if self.peek_char() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Reads one operator or delimiter, longest match first.
    fn read_operator(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        let c = match self.advance() {
            Some(c) => c,
            None => return Tok { toktype: TokType::EOF, line, col },
        };

        let toktype = match c {
            '+' => if self.eat('=') { TokType::PlusEquals } else { TokType::Plus },
            // `->` never reaches here; `next_token` consumes it as a line
            // continuation before dispatching.
            '-' => if self.eat('=') { TokType::MinusEquals } else { TokType::Minus },
            '*' => if self.eat('=') { TokType::StarEquals } else { TokType::Star },
            '/' => if self.eat('=') { TokType::SlashEquals } else { TokType::Slash },
            '%' => TokType::Percent,

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

            '(' => TokType::LParen,
            ')' => TokType::RParen,
            '[' => TokType::LBracket,
            ']' => TokType::RBracket,
            '{' => TokType::LCurlyBracket,
            '}' => TokType::RCurlyBracket,
            // `::` reaches into a type — `Color::Red` — where `:` annotates one.
            ':' => if self.eat(':') { TokType::ColonColon } else { TokType::Colon },
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
            '@' => TokType::At,

            _ => TokType::Error(format!("Unexpected character '{}'", c)),
        };

        Tok { toktype, line, col }
    }

    /// Skips whitespace, reporting whether any of it was a line break.
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
                return Tok { toktype: TokType::StringLiteral(s), line, col };
            } else if c == '\\' && !is_backtick {
                match self.read_escape() {
                    Ok(ch) => s.push(ch),
                    Err(e) => return Tok { toktype: TokType::Error(e), line, col },
                }
            } else {
                s.push(c);
            }
        }
        Tok { toktype: TokType::Error("Unterminated string".to_string()), line, col }
    }

    fn read_char(&mut self) -> Tok {
        let line = self.line;
        let col = self.col;
        self.advance(); // opening quote
        let value = match self.advance() {
            Some('\'') => {
                return Tok { toktype: TokType::Error("Empty character literal".to_string()), line, col };
            }
            Some('\\') => match self.read_escape() {
                Ok(c) => c,
                Err(e) => return Tok { toktype: TokType::Error(e), line, col },
            },
            Some(c) => c,
            None => {
                return Tok { toktype: TokType::Error("Unterminated character literal".to_string()), line, col };
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
            };
        }
        self.advance(); // closing quote
        Tok { toktype: TokType::CharLiteral(value), line, col }
    }

    /// Decodes one escape sequence. The leading `\` is already consumed.
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
            } else if c == '.' && !is_float && matches!(self.peek_char_at(1), Some(d) if d.is_ascii_digit()) {
                // Only the first '.' with a digit behind it belongs to the number;
                // `1.foo` stays an int followed by a Dot.
                is_float = true;
                num_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Reject junk glued to the literal: `1.2.3`, `12abc`. A second '.' can
        // only appear here once `is_float` is set, so this catches a repeated
        // decimal point without touching `1..2`, where the dots are a range.
        if let Some(c) = self.peek_char() {
            let bad_dot = c == '.' && matches!(self.peek_char_at(1), Some(d) if d.is_ascii_digit());
            if bad_dot || c.is_alphabetic() {
                self.consume_literal_tail();
                return Tok {
                    toktype: TokType::Error(format!("Malformed number literal '{}'", num_str)),
                    line,
                    col,
                };
            }
        }

        if is_float {
            match num_str.parse::<f64>() {
                Ok(v) => Tok { toktype: TokType::FloatLiteral(v), line, col },
                Err(_) => Tok {
                    toktype: TokType::Error(format!("Invalid float literal '{}'", num_str)),
                    line,
                    col,
                },
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(v) => Tok { toktype: TokType::IntLiteral(v), line, col },
                Err(_) => Tok {
                    toktype: TokType::Error(format!("Integer literal '{}' out of range for i64", num_str)),
                    line,
                    col,
                },
            }
        }
    }

    fn read_radix_int(&mut self, radix: u32, prefix: char, line: usize, col: usize) -> Tok {
        let mut digits = String::new();
        let mut bad = false;
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
            } else if c.is_alphanumeric() || c == '.' {
                // A digit outside this base, or a decimal point: consume it so the
                // error covers the whole malformed literal.
                bad = true;
                self.advance();
            } else {
                break;
            }
        }

        if bad {
            return Tok {
                toktype: TokType::Error(format!("Invalid digit in base-{} literal '0{}{}'", radix, prefix, digits)),
                line,
                col,
            };
        }
        if digits.is_empty() {
            return Tok {
                toktype: TokType::Error(format!("Expected digits after '0{}'", prefix)),
                line,
                col,
            };
        }
        match i64::from_str_radix(&digits, radix) {
            Ok(v) => Tok { toktype: TokType::IntLiteral(v), line, col },
            Err(_) => Tok {
                toktype: TokType::Error(format!("Integer literal '0{}{}' out of range for i64", prefix, digits)),
                line,
                col,
            },
        }
    }

    /// Reads an identifier or a keyword. Assumes the current char is a valid
    /// identifier start (alphabetic or `_`).
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
            };
        }

        let toktype = keyword_of(&word).unwrap_or(TokType::Identifier(word));
        Tok { toktype, line, col }
    }

    /// Swallow the rest of a malformed literal so the next token starts clean.
    /// Stops at `..` so one bad literal doesn't eat the range operator behind it.
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
