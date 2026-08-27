// One token, read off the front.
//
// This is the part of a lexer that looks like a lexer: skip what is between,
// look at the character in front, and dispatch. What it does not do is decide
// what the token *means* -- whether a newline is a separator, whether a `{` is
// a block -- which is `scan.rs` and `layout.rs`.
//
// The operators are the one place it needs help from further back. `&&` is two
// prefix `&` where no operand stands in front of it and one operator where
// one does, so `read_operator` asks what the last token was rather than
// looking only at the two characters in hand.

use crate::lex::tokens::*;

use super::Lexer;

impl Lexer {
    pub(super) fn scan_token(&mut self) -> Tok {
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
    pub(super) fn skip_whitespace(&mut self) -> bool {
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
}
