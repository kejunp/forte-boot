// Strings, characters, names and lifetimes.
//
// What they have in common is that each runs to a delimiter the source wrote
// and each may be cut short by the end of the input, which is the error every
// one of them has to be able to give: an unterminated literal is the mistake a
// reader most needs the opening quote's line for.
//
// The escapes are §6's and are shared between a string and a character, which
// is why `read_escape` is one function and not two.

use crate::lex::tokens::*;

use super::Lexer;

impl Lexer {
    pub(super) fn read_str(&mut self, is_backtick: bool) -> Tok {
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

    pub(super) fn read_char(&mut self) -> Tok {
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
    pub(super) fn read_sigil_name(&mut self, sigil: char) -> Tok {
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
    pub(super) fn finish_sigil_name(&mut self, line: usize, col: usize) -> Tok {
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
    pub(super) fn opens_lifetime(&self) -> bool {
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

    pub(super) fn read_lifetime(&mut self) -> Tok {
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
}
