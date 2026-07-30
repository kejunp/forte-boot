use crate::lex::tokens::*;

pub struct Lexer {
    input: Vec<char>,
    index: usize,
    line:  usize,
    col:   usize,

    // Automatic semicolon insertion state.
    last_can_end:  bool,
    bracket_depth: usize,

    // Generic argument list state.
    generic_depth: usize,
    last_was_name: bool,
}

/// Whether a token can legally end a statement, making it a candidate for a
/// semicolon to be inserted after it at a newline.
fn can_end_statement(t: &TokType) -> bool {
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
            | TokType::Null
            | TokType::Return
            | TokType::Break
            | TokType::Continue
            | TokType::RParen
            | TokType::RBracket
            | TokType::RCurlyBracket
            // An open range is a complete expression: `let rest = 1..`. `..=`
            // is not — it always needs an upper bound — so it keeps looking.
            | TokType::DotDot
            // A type name can end a field or parameter declaration.
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Void
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
            // Trait bounds, e.g. `<T: Show>`.
            | TokType::Colon
            // Nested arguments and array types, e.g. `<Map<str, i32[]>>`.
            | TokType::LessThan
            | TokType::GreaterThan
            | TokType::LBracket
            | TokType::RBracket
            | TokType::I8 | TokType::I16 | TokType::I32 | TokType::I64
            | TokType::U8 | TokType::U16 | TokType::U32 | TokType::U64
            | TokType::Bool | TokType::Char | TokType::Str | TokType::Void
    )
}

/// Characters that continue the previous line rather than starting a new
/// statement, so no semicolon is inserted before them.
fn starts_continuation(c: char) -> bool {
    matches!(c, '.' | '+' | '-' | '*' | '/' | '%' | '=' | '<' | '>' | '&' | '|' | ',' | ':')
}

/// Keywords that continue the previous statement, e.g. the `else` in
/// `}` / newline / `else {`. No statement begins with one of these, so a line
/// that starts with one is always a continuation — including a cast split
/// across lines, `let n = x` / newline / `as i64`.
fn continues_statement(word: &str) -> bool {
    matches!(word, "else" | "elif" | "as" | "in")
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
        "bool" => TokType::Bool,
        "char" => TokType::Char,
        "str" => TokType::Str,
        "void" => TokType::Void,

        // Declarations
        "fn" => TokType::Fn,
        "let" => TokType::Let,
        "var" => TokType::Var,
        "struct" => TokType::Struct,
        "trait" => TokType::Trait,
        "impl" => TokType::Impl,
        "public" => TokType::Public,
        "private" => TokType::Private,
        "import" => TokType::Import,
        "enum" => TokType::Enum,

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

        // Literals
        "true" => TokType::True,
        "false" => TokType::False,
        "this" => TokType::This,
        "null" => TokType::Null,

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

            last_can_end:  false,
            bracket_depth: 0,

            generic_depth: 0,
            last_was_name: false,
        }
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.index).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.input.get(self.index + offset).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek();
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

    pub fn next_token(&mut self) -> Tok {
        // Position just past the previous token — where an inserted semicolon
        // belongs, at the end of that line rather than the start of the next.
        let line = self.line;
        let col = self.col;

        let mut crossed_newline = self.skip_whitespace();

        // `->` splices the following line onto this one, cancelling any pending
        // insertion: `let x = y ->` / newline / `+ 2` is one statement.
        while self.peek() == Some('-') && self.peek_at(1) == Some('>') {
            self.advance();
            self.advance();
            self.skip_whitespace();
            crossed_newline = false;
        }

        if self.wants_semicolon(crossed_newline) {
            self.last_can_end = false;
            return Tok { toktype: TokType::Semicolon, line, col };
        }

        let tok = self.scan_token();

        // A `>` only closes a generic if one was open; that also makes it the
        // end of a type, and so a place a statement can end: `let v: Vec<i32>`.
        let closed_generic = self.generic_depth > 0 && tok.toktype == TokType::GreaterThan;
        match &tok.toktype {
            // Only a name can be generic, which rules out `1 < 2` and `) < x`.
            TokType::LessThan if self.last_was_name => self.generic_depth += 1,
            TokType::GreaterThan => {
                self.generic_depth = self.generic_depth.saturating_sub(1);
            }
            t if self.generic_depth > 0 && !fits_in_generics(t) => self.generic_depth = 0,
            _ => {}
        }
        self.last_was_name = matches!(tok.toktype, TokType::Identifier(_));

        self.last_can_end = can_end_statement(&tok.toktype) || closed_generic;
        match tok.toktype {
            TokType::LParen | TokType::LBracket => self.bracket_depth += 1,
            TokType::RParen | TokType::RBracket => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
            }
            _ => {}
        }
        tok
    }

    /// Decides whether to synthesize a semicolon at the current position.
    fn wants_semicolon(&self, crossed_newline: bool) -> bool {
        if !self.last_can_end {
            return false;
        }
        // Inside `(...)` or `[...]` a newline is just formatting, so argument
        // lists and indexes can span lines. Braces are blocks, so they count.
        if self.bracket_depth > 0 {
            return false;
        }

        match self.peek() {
            // End of input, with a statement left open.
            None => true,
            Some(_) if !crossed_newline => false,
            Some(c) if starts_continuation(c) => false,
            Some(c) if c.is_alphabetic() || c == '_' => !continues_statement(&self.peek_word()),
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

        let c = match self.peek() {
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
        if self.peek() == Some(expected) {
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

            '&' => {
                if self.eat('&') { TokType::And }
                else if self.eat('=') { TokType::AndEquals }
                else {
                    return Tok { toktype: TokType::Error("Expected '&&' or '&='".to_string()), line, col };
                }
            }
            '|' => {
                if self.eat('|') { TokType::Or }
                else if self.eat('=') { TokType::OrEquals }
                else {
                    return Tok { toktype: TokType::Error("Expected '||' or '|='".to_string()), line, col };
                }
            }

            '(' => TokType::LParen,
            ')' => TokType::RParen,
            '[' => TokType::LBracket,
            ']' => TokType::RBracket,
            '{' => TokType::LCurlyBracket,
            '}' => TokType::RCurlyBracket,
            ':' => TokType::Colon,
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

        Tok { toktype, line, col }
    }

    /// Skips whitespace, reporting whether any of it was a line break.
    fn skip_whitespace(&mut self) -> bool {
        let mut crossed_newline = false;
        while let Some(c) = self.peek() {
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

        if self.peek() != Some('\'') {
            // Skip to the closing quote so one bad literal doesn't cascade.
            while let Some(c) = self.peek() {
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
                    match self.peek() {
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
                    match self.peek() {
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
        if self.peek() == Some('0') {
            if let Some(radix) = self.peek_at(1).and_then(radix_of) {
                let prefix = self.peek_at(1).unwrap();
                self.advance(); // '0'
                self.advance(); // base marker
                return self.read_radix_int(radix, prefix, line, col);
            }
        }

        let mut is_float = false;
        let mut num_str = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.advance();
            } else if c == '.' && !is_float && matches!(self.peek_at(1), Some(d) if d.is_ascii_digit()) {
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
        if let Some(c) = self.peek() {
            let bad_dot = c == '.' && matches!(self.peek_at(1), Some(d) if d.is_ascii_digit());
            if bad_dot || c.is_alphabetic() || c == '_' {
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
        while let Some(c) = self.peek() {
            if c.is_digit(radix) {
                digits.push(c);
                self.advance();
            } else if c == '.' && self.peek_at(1) == Some('.') {
                // `0x10..0x20` — the dots are a range, not part of the literal.
                break;
            } else if c.is_alphanumeric() || c == '_' || c == '.' {
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
        while let Some(c) = self.peek() {
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
        while let Some(c) = self.peek() {
            if c == '.' && self.peek_at(1) == Some('.') {
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
