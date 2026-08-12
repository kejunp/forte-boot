// One thing the compiler has to say, whichever part of it is saying so.

use super::render;
use super::source::Source;
use super::span::Span;

// How much a diagnostic matters: the word it leads with, and whether the build
// carries on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    // The word it is announced with.
    pub fn word(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
        }
    }
}

// Somewhere else the reader has to look. `text` says what the place is, not
// where -- the snippet says where -- and is finished with `here`, so it reads
// like "unclosed `(` opened".
#[derive(Debug, Clone, PartialEq)]
pub struct Label {
    pub text: String,
    pub span: Span,
}

// A line hung under a diagnostic, after everything that quotes the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Remark {
    // What to do about it.
    Help,
    // Something a reader has to know that is not advice.
    Note,
}

impl Remark {
    pub fn word(self) -> &'static str {
        match self {
            Remark::Help => "help",
            Remark::Note => "note",
        }
    }
}

// Built by whichever phase found the problem and laid out by `render`: a phase
// says nothing about gutters, carets or ordering. Everything past the message
// and the span is optional, and most are just those two.
#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub severity:  Severity,
    // One line, with no position in it: the position is `span`'s to give.
    pub message:   String,
    // The piece of source the message is against.
    pub span:      Span,
    // A word or two beside the caret, about the same piece of source.
    pub label:     Option<String>,
    // Other places worth showing, each quoted where it stands.
    pub secondary: Vec<Label>,
    // The lines hung underneath, in the order they were added.
    pub remarks:   Vec<(Remark, String)>,
}

impl Diagnostic {
    // A diagnostic of `severity` about `span`. The builders below add the rest,
    // so the usual one is a single expression:
    //
    //     Diagnostic::error("expected `,`, found `;`".to_string(), span)
    //         .with_label("while parsing a field")
    //         .with_help("use `,` to separate entries")
    pub fn new(severity: Severity, message: String, span: Span) -> Diagnostic {
        Diagnostic {
            severity,
            message,
            span,
            label: None,
            secondary: Vec::new(),
            remarks: Vec::new(),
        }
    }

    pub fn error(message: String, span: Span) -> Diagnostic {
        Diagnostic::new(Severity::Error, message, span)
    }

    pub fn warning(message: String, span: Span) -> Diagnostic {
        Diagnostic::new(Severity::Warning, message, span)
    }

    // What to write beside the caret.
    pub fn with_label(mut self, text: impl Into<String>) -> Diagnostic {
        self.label = Some(text.into());
        self
    }

    // Another place to quote, under a heading of its own.
    pub fn with_secondary(mut self, span: Span, text: impl Into<String>) -> Diagnostic {
        self.secondary.push(Label { text: text.into(), span });
        self
    }

    pub fn with_help(mut self, text: impl Into<String>) -> Diagnostic {
        self.remarks.push((Remark::Help, text.into()));
        self
    }

    pub fn with_note(mut self, text: impl Into<String>) -> Diagnostic {
        self.remarks.push((Remark::Note, text.into()));
        self
    }

    // Whether this is something that stops the build.
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    // The message with the source under it. See `render` for the layout.
    pub fn render(&self, source: &Source) -> String {
        render::diagnostic(self, source)
    }
}
