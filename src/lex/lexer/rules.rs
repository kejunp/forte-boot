// The questions the scanner asks about a token it has already read.
//
// Every one of them is a fact about a `TokType` or a character and about
// nothing else -- no cursor, no state, no lookahead -- which is why they are
// together and why they are free functions rather than methods. A rule that
// cannot see where the scanner is cannot be wrong about where it is.
//
// Most of them are §7's, and §7 is the reason a lexer for this language is
// more than a loop. Whether a newline ends a statement depends on what the
// last token was and what the next one is, so "does this end an operand", "can
// this end a statement" and "does this start one" are asked constantly and
// have to give the same answer every time they are asked.

use crate::lex::tokens::*;


// Whether a token ends an operand — a value or a type — and so stands where an
// infix operator may follow. This tells the two readings of `&&` apart: an
// operand in front makes it the logical operator, none makes it two prefix `&`.
pub(super) fn ends_an_operand(t: &TokType) -> bool {
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
pub(super) fn can_end_statement(t: &TokType) -> bool {
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
pub(super) fn fits_in_generics(t: &TokType) -> bool {
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
pub(super) fn starts_continuation(c: char) -> bool {
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
pub(super) fn continues_after_brace(c: char) -> bool {
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
pub(super) fn heads_a_body(t: &TokType) -> bool {
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
pub(super) fn starts_statement(t: &TokType) -> bool {
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
pub(super) fn continues_statement(word: &str) -> bool {
    // `where` is here so a signature may put its bounds on the next line.
    matches!(word, "else" | "elif" | "as" | "in" | "where")
}

// Base prefixes accepted after a leading `0`, e.g. `0xFF`, `0b1010`.
pub(super) fn radix_of(c: char) -> Option<u32> {
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
pub(super) fn bad(message: String, line: usize, col: usize) -> Tok {
    Tok { toktype: TokType::Error(message), line, col, len: 0 }
}

// A word glued to a number that names no type. Spelled out in full, since the
// twelve are the whole of what may be written there.
pub(super) fn suffix_error(word: &str, literal: &str) -> String {
    format!(
        "Unknown suffix '{}' on number literal '{}'; expected one of i8, i16, i32, i64, \
         i128, u8, u16, u32, u64, u128, f32, f64",
        word, literal
    )
}

// Reserved words. Anything not listed here lexes as an `Identifier`.
pub(super) fn keyword_of(word: &str) -> Option<TokType> {
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
        "once" => TokType::Once,
        "addr" => TokType::Addr,
        "deref" => TokType::Deref,

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
