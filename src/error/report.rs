// Everything a phase has to say, gathered up.

use super::diagnostic::Diagnostic;
use super::source::Source;

// The diagnostics a phase produced, in order. A phase does not stop at the
// first thing it turns down, so every one of them ends up here.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Diagnostics {
    items: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn new() -> Diagnostics {
        Diagnostics { items: Vec::new() }
    }

    pub fn push(&mut self, diagnostic: Diagnostic) {
        self.items.push(diagnostic);
    }

    // Takes on everything another phase reported, leaving it empty: what the
    // lexer found and what the parser found are one report to a reader.
    pub fn absorb(&mut self, other: &mut Diagnostics) {
        self.items.append(&mut other.items);
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
