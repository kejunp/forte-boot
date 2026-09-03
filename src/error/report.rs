// Everything a phase has to say, gathered up.

use super::diagnostic::Diagnostic;
use super::source::Source;

// The diagnostics a phase produced, in order. A phase does not stop at the
// first thing it turns down, so every one of them ends up here.
//
// Beside each one, which file it is about. A `Span` is a line and a column and
// says nothing about where -- which was enough while every phase was handed one
// file, and stopped being enough when `sema::lower` started taking a whole
// suite at once. A diagnostic is quoted against the source it was written
// against and no other, so a report that mixed two files would put a caret
// under whatever line happened to be there.
//
// It is a number and not a name because a report is rendered against a list of
// sources the caller already holds; the number is the place in that list.
// Nothing that only ever reads one file has to say anything: the file is zero
// until somebody says otherwise, and `render` against a single source ignores
// it entirely.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Diagnostics {
    items:   Vec<Diagnostic>,
    whose:   Vec<usize>,
    // What the next one pushed will be about. Kept here rather than passed at
    // every `push` because there are sixty of those and one place that knows
    // which file is being walked.
    current: usize,
}

impl Diagnostics {
    pub fn new() -> Diagnostics {
        Diagnostics { items: Vec::new(), whose: Vec::new(), current: 0 }
    }

    pub fn push(&mut self, diagnostic: Diagnostic) {
        self.items.push(diagnostic);
        self.whose.push(self.current);
    }

    // Everything from here on is about `file`, until this is said again.
    pub fn from_now_on(&mut self, file: usize) {
        self.current = file;
    }

    // Which file each is about, in the order they were reported.
    pub fn whose(&self) -> &[usize] {
        &self.whose
    }

    // Takes on everything another phase reported, leaving it empty: what the
    // lexer found and what the parser found are one report to a reader.
    //
    // What the other phase said each of its diagnostics was about comes with
    // them. A phase that never said keeps saying nothing, its file being zero.
    pub fn absorb(&mut self, other: &mut Diagnostics) {
        self.items.append(&mut other.items);
        self.whose.append(&mut other.whose);
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Diagnostic> {
        self.items.iter()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    // Whether anything here stops the build. Warnings do not, so a report that
    // is not empty is not the same as a compilation that failed.
    pub fn has_errors(&self) -> bool {
        self.items.iter().any(|d| d.is_error())
    }

    // All of them laid out, blank line between, so a run of them does not read
    // as one long message.
    pub fn render(&self, source: &Source) -> String {
        self
            .items
            .iter()
            .map(|d| d.render(source))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    // The same, where the diagnostics are about several files: each is quoted
    // against the one it was reported for. One that names a file nothing was
    // handed for is dropped rather than quoted against the wrong text -- a
    // message with the wrong lines under it is worse than no message, and a
    // number out of range is a mistake in the caller and not in the program
    // being compiled.
    pub fn render_across(&self, sources: &[Source]) -> String {
        self
            .items
            .iter()
            .zip(self.whose.iter())
            .filter_map(|(d, &whose)| sources.get(whose).map(|s| d.render(s)))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    // Whether anything about `file` stops the build, which is what lets a
    // caller carry on with the files that were sound.
    pub fn has_errors_in(&self, file: usize) -> bool {
        self.items
            .iter()
            .zip(self.whose.iter())
            .any(|(d, &whose)| whose == file && d.is_error())
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Diagnostic, Span};
    use super::*;

    #[test]
    fn a_warning_is_not_a_failure() {
        let mut report = Diagnostics::new();
        assert!(!report.has_errors());

        report.push(Diagnostic::warning("never read".to_string(), Span::at(1, 1)));
        assert_eq!(report.len(), 1);
        assert!(!report.is_empty());
        // Something was said, but nothing that stops the build.
        assert!(!report.has_errors());

        report.push(Diagnostic::error("no such name".to_string(), Span::at(2, 1)));
        assert!(report.has_errors());
    }

    // Two phases, one report, in the order they ran.
    #[test]
    fn one_report_takes_on_another() {
        let text: Vec<char> = "let x = 1\nlet y = 2\n".chars().collect();
        let source = Source::new("t.ft", &text);

        let mut first = Diagnostics::new();
        first.push(Diagnostic::error("the first".to_string(), Span::new(1, 5, 1)));
        let mut second = Diagnostics::new();
        second.push(Diagnostic::error("the second".to_string(), Span::new(2, 5, 1)));

        first.absorb(&mut second);
        assert!(second.is_empty());
        assert_eq!(first.len(), 2);
        assert_eq!(
            first.render(&source),
            "\
error: the first
 --> t.ft:1:5
  |
1 | let x = 1
  |     ^

error: the second
 --> t.ft:2:5
  |
2 | let y = 2
  |     ^"
        );
    }
}
