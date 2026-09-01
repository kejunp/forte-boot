// The one place that knows what a report looks like: a phase hands over what
// it found, this decides the gutter, the carets and the order.
//
//     error: expected `,`, `[` or `}`, found `;`
//      --> input.ft:2:11
//       |
//     2 |     x: i32;
//       |           ^ while parsing a field
//       |
//       = help: use `,` to separate entries
//
//     note: unclosed `{` opened here
//      --> input.ft:1:10
//       |
//     1 | struct P {
//       |          ^

use super::diagnostic::Diagnostic;
use super::source::Source;
use super::span::Span;

// How many columns a tab stands for. The source is quoted with tabs expanded,
// so a caret counted in characters lands under the character it belongs to.
const TAB_WIDTH: usize = 4;

// One diagnostic, laid out. No trailing newline -- the blank line between two
// of them is the printer's doing.
pub fn diagnostic(d: &Diagnostic, source: &Source) -> String {
    // The widest line number shown, so the bar stands in the same column
    // throughout -- a note must not step out of line with its diagnostic.
    let widest = d
        .secondary
        .iter()
        .map(|l| l.span.line)
        .chain(std::iter::once(d.span.line))
        .max()
        .unwrap_or(d.span.line);
    let gutter = widest.to_string().len();

    let mut out = format!("{}: {}\n", d.severity.word(), d.message);
    out.push_str(&snippet(source, d.span, d.label.as_deref(), gutter));

    for (kind, text) in &d.remarks {
        out.push_str(&format!("{:w$} |\n", "", w = gutter));
        out.push_str(&format!("{:w$} = {}: {}\n", "", kind.word(), text, w = gutter));
    }
    for label in &d.secondary {
        out.push('\n');
        out.push_str(&format!("note: {} here\n", label.text));
        out.push_str(&snippet(source, label.span, None, gutter));
    }
    out.trim_end().to_string()
}

// The `--> where` line, the quoted source, and the caret under it. Shared with
// the secondaries: a secondary is the same three lines, minus the label.
fn snippet(source: &Source, span: Span, label: Option<&str>, gutter: usize) -> String {
    let mut out = format!(
        "{:w$}--> {}:{}:{}\n",
        "",
        source.path(),
        span.line,
        span.col,
        w = gutter
    );

    // A span past the end of the source has nowhere to point; the line above
    // already said where it was.
    let text = match source.line(span.line) {
        Some(text) => text,
        None => return out,
    };

    let (shown, offset) = expand_tabs(&text, span.col);
    // What is left of the line to underline. A token can run past the end of
    // one -- an unterminated string does -- so the caret stops where it shows.
    let rest = shown.chars().count().saturating_sub(offset);
    let width = span.len.clamp(1, rest.max(1));

    let mut caret = String::from("^");
    caret.push_str(&"~".repeat(width - 1));

    out.push_str(&format!("{:w$} |\n", "", w = gutter));
    // Trimmed, so quoting a blank line does not leave whitespace off the bar.
    let quoted = format!("{:>w$} | {}", span.line, shown, w = gutter);
    out.push_str(quoted.trim_end());
    out.push('\n');
    out.push_str(&format!("{:w$} | {:o$}{}", "", "", caret, w = gutter, o = offset));
    match label {
        Some(label) => out.push_str(&format!(" {}\n", label)),
        None => out.push('\n'),
    }
    out
}

// The line as it will be shown, and how far along it a caret for `col` goes.
// A tab is one character to the lexer and several columns on the page, so both
// are worked out together. A column past the end of the line points just after
// it, where the missing thing would have been written.
fn expand_tabs(text: &str, col: usize) -> (String, usize) {
    let mut shown = String::new();
    let mut offset = 0;
    for (i, c) in text.chars().enumerate() {
        if i + 1 == col {
            offset = shown.chars().count();
        }
        if c == '\t' {
            let pad = TAB_WIDTH - (shown.chars().count() % TAB_WIDTH);
            shown.push_str(&" ".repeat(pad));
        } else {
            shown.push(c);
        }
    }
    let count = text.chars().count();
    if col > count {
        offset = shown.chars().count() + (col - count - 1);
    }
    (shown, offset)
}

#[cfg(test)]
mod tests {
    use super::super::{Diagnostic, Span};
    use super::*;

    fn chars(s: &str) -> Vec<char> {
        s.chars().collect()
    }

    // The whole shape: message, where, the line, and a caret as wide as the
    // token.
    #[test]
    fn renders_the_line_and_points_at_it() {
        let text = chars("fn main() {\n    let x = 1\n}\n");
        let d = Diagnostic::error("expected `;`, found `let`".to_string(), Span::new(2, 5, 3))
            .with_label("while parsing a block");
        assert_eq!(
            d.render(&Source::new("input.ft", &text)),
            "\
error: expected `;`, found `let`
 --> input.ft:2:5
  |
2 |     let x = 1
  |     ^~~ while parsing a block"
        );
    }

    // A warning is the same report under a different word.
    #[test]
    fn a_warning_says_so() {
        let text = chars("let unused = 1\n");
        let d = Diagnostic::warning("`unused` is never read".to_string(), Span::new(1, 5, 6));
        assert_eq!(
            d.render(&Source::new("w.ft", &text)),
            "\
warning: `unused` is never read
 --> w.ft:1:5
  |
1 | let unused = 1
  |     ^~~~~~"
        );
    }

    // A secondary is a snippet of its own, and the gutter is wide enough for
    // the largest line number so the pair line up.
    #[test]
    fn a_secondary_is_shown_where_it_happened() {
        let text = chars("fn main() {\n    f(1, 2\n}\n");
        let d = Diagnostic::error("expected `,` or `)`, found `}`".to_string(), Span::new(3, 1, 1))
            .with_secondary(Span::new(2, 6, 1), "unclosed `(` opened");
        assert_eq!(
            d.render(&Source::new("input.ft", &text)),
            "\
error: expected `,` or `)`, found `}`
 --> input.ft:3:1
  |
3 | }
  | ^

note: unclosed `(` opened here
 --> input.ft:2:6
  |
2 |     f(1, 2
  |      ^"
        );
    }

    // Remarks hang off the end in order, each under a bar so they read as part
    // of the same block.
    #[test]
    fn remarks_hang_off_the_end_in_order() {
        let text = chars("struct P {\n    x: i32;\n}\n");
        let d = Diagnostic::error("expected `,`, found `;`".to_string(), Span::new(2, 11, 1))
            .with_help("use `,` to separate entries")
            .with_note("a struct's fields are entries, not statements");
        assert_eq!(
            d.render(&Source::new("p.ft", &text)),
            "\
error: expected `,`, found `;`
 --> p.ft:2:11
  |
2 |     x: i32;
  |           ^
  |
  = help: use `,` to separate entries
  |
  = note: a struct's fields are entries, not statements"
        );
    }

    // More than one place to look, each quoted under its own heading.
    #[test]
    fn every_secondary_gets_a_snippet() {
        let text = chars("fn f() {}\nfn f() {}\nfn f() {}\n");
        let d = Diagnostic::error("`f` is defined three times".to_string(), Span::new(3, 4, 1))
            .with_secondary(Span::new(1, 4, 1), "first defined")
            .with_secondary(Span::new(2, 4, 1), "defined again");
        assert_eq!(
            d.render(&Source::new("d.ft", &text)),
            "\
error: `f` is defined three times
 --> d.ft:3:4
  |
3 | fn f() {}
  |    ^

note: first defined here
 --> d.ft:1:4
  |
1 | fn f() {}
  |    ^

note: defined again here
 --> d.ft:2:4
  |
2 | fn f() {}
  |    ^"
        );
    }

    // The caret sits on the line as shown, so a tab counts for what it takes
    // up on the page.
    #[test]
    fn a_tab_is_as_wide_as_it_looks() {
        let text = chars("fn f() {\n\tlet x = ;\n}\n");
        let d = Diagnostic::error(
            "expected an expression, found `;`".to_string(),
            Span::new(2, 10, 1),
        );
        assert_eq!(
            d.render(&Source::new("t.ft", &text)),
            "\
error: expected an expression, found `;`
 --> t.ft:2:10
  |
2 |     let x = ;
  |             ^"
        );
    }

    // A token running past the end of its line stops where it can still be
    // seen.
    #[test]
    fn a_caret_stops_at_the_end_of_the_line() {
        let text = chars("let s = \"oops\n");
        let d = Diagnostic::error("Unterminated string".to_string(), Span::new(1, 9, 99));
        assert_eq!(
            d.render(&Source::new("s.ft", &text)),
            "\
error: Unterminated string
 --> s.ft:1:9
  |
1 | let s = \"oops
  |         ^~~~~"
        );
    }

    // The end of the file is a place, not a piece: one caret, in the column
    // after the last character written.
    #[test]
    fn the_end_of_the_file_gets_one_caret() {
        let text = chars("fn main() {\n    let x = 1\n");
        let d = Diagnostic::error("expected `}`, found end of file".to_string(), Span::at(3, 1));
        assert_eq!(
            d.render(&Source::new("e.ft", &text)),
            "\
error: expected `}`, found end of file
 --> e.ft:3:1
  |
3 |
  | ^"
        );
    }

    // A span past the last line says where it was and quotes nothing.
    #[test]
    fn a_span_off_the_end_quotes_nothing() {
        let text = chars("fn f() {}\n");
        let d = Diagnostic::error("nowhere".to_string(), Span::at(9, 1));
        assert_eq!(
            d.render(&Source::new("o.ft", &text)),
            "\
error: nowhere
 --> o.ft:9:1"
        );
    }
}
