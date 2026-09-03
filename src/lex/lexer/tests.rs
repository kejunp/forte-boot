// What the lexer makes of a source, one decision at a time.
//
// These lived in `main.rs` until now, at the crate root and outside any module
// -- sixty-three tests and the two helpers below, three thousand lines of
// them, a directory away from the pass they are about. Every other phase here
// keeps its tests beside itself, and this is that.
//
// One file per subject, and the subjects are the lexer's own: `layout` is the
// separator insertion of section 7, `words` the reserved words, `numbers` the
// literals and the ranges glued to them. What stays here is the pair of
// helpers every one of them is written in terms of.

use super::*;
use crate::lex::tokens::TokType;
use crate::prep::preprocess;

mod attrs;
mod closures;
mod generics;
mod layout;
mod literals;
mod numbers;
mod prep;
mod refs;
mod spans;
mod types;
mod words;

fn lex_types(source: &str) -> Vec<TokType> {
    let mut lexer = Lexer::new(source);
    let mut out = Vec::new();
    loop {
        let tok = lexer.next_token();
        if tok.toktype == TokType::EOF {
            return out;
        }
        out.push(tok.toktype);
    }
}

// Every token's column and width, which is what a diagnostic underlines.
fn lex_spans(source: &str) -> Vec<(usize, usize)> {
    let mut lexer = Lexer::new(source);
    let mut out = Vec::new();
    loop {
        let tok = lexer.next_token();
        if tok.toktype == TokType::EOF {
            return out;
        }
        out.push((tok.col, tok.len));
    }
}
