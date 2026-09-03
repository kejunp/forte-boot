// Preprocessing, which runs before the lexer and must not move anything.
//
// Blanking a comment rather than deleting it only pays off if the output lines
// up with the input character for character: that is what lets a diagnostic
// quote the source as written while the parse runs on the stripped copy.

use super::*;

// Blanking rather than deleting only pays off if the output lines up with the
// input character for character, which is what lets a diagnostic quote the
// source as written while the parse runs on the preprocessed copy.
#[test]
fn preprocessing_preserves_length_and_lines() {
    let cases = [
        "let x = 25; // the answer\nlet y = x + 1\n",
        "let x = /* a\nmultiline\ncomment */ 25\n",
        "let x = 1 /* never closed\n",
        "a /**/ b",
        "a /*/ b",
        "a // c",
        "no comments here\n",
        "/*",
        "//",
        "let my_var = 1  // a_b\n",
    ];
    for src in cases {
        let out = preprocess(src);
        assert_eq!(
            src.chars().count(),
            out.chars().count(),
            "length changed for {:?} -> {:?}",
            src,
            out
        );
        assert_eq!(
            src.matches('\n').count(),
            out.matches('\n').count(),
            "newline count changed for {:?} -> {:?}",
            src,
            out
        );
    }
}
