// What a token knows besides its type: how wide it was written, and where.
// This is what a diagnostic underlines, so `0x10` and `16` must not agree.
//
// And that peeking leaves the scanner where it found it, since every one of
// the layout decisions is taken on a scan the reader never sees.

use super::*;

// A token knows how wide it was written, which its type cannot answer: `0x10`
// and `16` are the same literal, and a string has lost its quotes and escapes.
#[test]
fn a_token_knows_how_wide_it_was_written() {
    // The inserted separator at the end is a place and not a piece: no width.
    assert_eq!(
        lex_spans("let x = 25\n"),
        vec![(1, 3), (5, 1), (7, 1), (9, 2), (11, 0)]
    );
    // Written in a base, and with the separators a reader may put in it.
    assert_eq!(lex_spans("0x10"), vec![(1, 4), (5, 0)]);
    assert_eq!(lex_spans("2_147_483_647"), vec![(1, 13), (14, 0)]);
    // The quotes are the literal's, though its value has none.
    assert_eq!(lex_spans("\"hi\""), vec![(1, 4), (5, 0)]);
    assert_eq!(lex_spans("'\\n'"), vec![(1, 4), (5, 0)]);
    // A `>>` that closes two generic lists is two tokens of one character, not
    // one of two -- the width follows the split.
    assert_eq!(
        lex_spans("Map<str, List<i32>>"),
        vec![
            (1, 3),   // Map
            (4, 1),   // <
            (5, 3),   // str
            (8, 1),   // ,
            (10, 4),  // List
            (14, 1),  // <
            (15, 3),  // i32
            (18, 1),  // the first `>`
            (19, 1),  // the second
            (20, 0),  // the inserted separator
        ]
    );
    // A real shift is still one token, and two characters wide.
    assert_eq!(lex_spans("bits >> 2"), vec![(1, 4), (6, 2), (9, 1), (10, 0)]);
    // A token the lexer gave up inside of covers what it read before it did.
    // An unterminated string runs to the end of the input, so its width counts
    // the newline it ran past; a diagnostic quoting one line stops at the end
    // of that line, which is where a caret can still be seen.
    assert_eq!(lex_spans("let s = \"oops\n"), vec![(1, 3), (5, 1), (7, 1), (9, 6)]);
}

// Peeking must leave the scanner exactly where it was: a peek before every
// `next_token` yields the same stream as no peeks at all, line and column
// included, even where lexing depends on scanner state.
#[test]
fn peek_does_not_consume() {
    let sources = [
        "let x = 25\nlet y = x + 1\n",
        "let m: Map<str, List<i32>> = empty()\n",
        "let n = bits >> 2\n",
        "for i in 0..10 {}\n",
        // Brace kinds are scanner state too, so they must roll back as well —
        // including a pending header, and a literal's brace inside one.
        "struct P {\n    x: i32\n    y: i32\n}\n",
        "match x {\n    1 => {\n        f()\n    }\n    2 => g()\n}\n",
        "let p = Point {\n    x: 1\n    y: 2\n}\n",
        "if (Cfg { on: true }).on {\n    f()\n}\n",
        // A collection literal's brace is decided by a lookahead, which is the
        // scanner run and rewound — so a peek around one nests two of them.
        "let m = {\n    1: {\n        f()\n        g()\n    },\n}\n",
        "let s = #{1, 2}\nlet b = {\n    f()\n    g()\n}\n",
        "for x in {1, 2} {\n    f(x)\n    g(x)\n}\n",
        "match x {\n    1 => a,\n    _ => b,\n}\n",
        "let _ = f()\nfor _ in 0..3 {}\n",
        // `unsafe` decides its brace by looking at the character after it, so
        // both readings have to survive a peek.
        "unsafe {\n    f()\n    g()\n}\n",
        "unsafe p = P {\n    x: 1\n    y: 2\n}\n",
    ];
    for src in sources {
        let mut lexer = Lexer::new(src);
        for expected in lex_types(src) {
            let peeked = lexer.peek();
            assert_eq!(peeked, lexer.peek(), "second peek differed in {:?}", src);
            assert_eq!(peeked, lexer.next_token(), "peek differed from next in {:?}", src);
            assert_eq!(peeked.toktype, expected);
        }
        assert_eq!(lexer.peek().toktype, TokType::EOF);
        assert_eq!(lexer.next_token().toktype, TokType::EOF);
    }
}
