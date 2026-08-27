// Numbers, and the words stuck to the end of them.
//
// A number in this language carries its type in its spelling where it carries
// one at all -- `1i64`, `2.5f32` -- so reading one is reading a number and
// then reading a word and then deciding whether the word was a suffix or the
// start of something else. A suffix nobody declared is an error worth naming,
// since `1u7` is a typo and not a number followed by a name.
//
// The awkward case is `.`, and it is why `prev_was_dot` exists: `t.0.1` is two
// tuple indexes and `0.1` is a float, and the only difference is what stood in
// front.

use crate::lex::tokens::*;

use super::rules::*;
use super::Lexer;

impl Lexer {
    pub(super) fn read_number(&mut self) -> Tok {
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
    pub(super) fn read_word(&mut self) -> Tok {
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
