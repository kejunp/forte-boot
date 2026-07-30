mod lex;
mod prep;

use lex::lexer::Lexer;
use lex::tokens::TokType;
use prep::comments::strip_comments;
use prep::mangle_prep::prep_mangle;

fn dump(source: &str) {
    println!("source:\n{}\n", source);
    dump_tokens(source);
}

fn dump_tokens(source: &str) {
    let mut lexer = Lexer::new(source);
    loop {
        let tok = lexer.next_token();
        println!("{:>2}:{:<3} {:?}", tok.line, tok.col, tok.toktype);
        if tok.toktype == TokType::EOF {
            break;
        }
    }
    println!();
}

fn dump_strip(source: &str) {
    let stripped = strip_comments(source);
    println!("source:\n{}\n", source);
    println!("stripped:\n{}\n", stripped);

    // Comments are blanked out, not deleted, so line/col stay put.
    dump_tokens(&stripped);
    println!();
}

fn dump_mangle(name: &str) {
    let mangled: String = name.chars().map(prep_mangle).collect();
    println!("mangle: {} -> {}\n", name, mangled);
}

fn main() {
    dump("let x = 25;");

    // Same program with no semicolons at all.
    dump("let x = 25\nlet y = x + 1\n");

    // Line comment: everything after // becomes spaces on the same line.
    dump_strip("let x = 25; // the answer\nlet y = x + 1\n");

    // Block comment: newlines inside it survive so later lines keep their numbers.
    dump_strip("let x = /* a\nmultiline\ncomment */ 25\n");

    // Unterminated block comment runs to end of input.
    dump_strip("let x = 1 /* never closed\n");

    dump_mangle("my_var_name");
    dump_mangle("already_ok");
}

/// Blanking rather than deleting only pays off if the output lines up with the
/// input character for character.
#[test]
fn strip_preserves_length_and_lines() {
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
    ];
    for src in cases {
        let out = strip_comments(src);
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
