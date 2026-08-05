//! One thing the compiler has to say, whichever part of it is saying so.

use super::render;
use super::source::Source;
use super::span::Span;

/// How much a diagnostic matters.
///
/// What it changes is the word a diagnostic leads with and whether the build
/// carries on: an error means nothing further downstream can be trusted, and a
/// warning means the code is taken as written and is worth a second look.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    /// The word it is announced with.
    pub fn word(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
        }
    }
}

/// Somewhere else the reader has to look, and what it has to do with the
/// diagnostic that names it.
///
/// `text` says what the place is without saying where, because the snippet
/// under it is what says where: it is finished with `here`, so "unclosed `(`
/// opened" is what one has to read like.
#[derive(Debug, Clone, PartialEq)]
pub struct Label {
    pub text: String,
    pub span: Span,
}

/// A line hung under a diagnostic, after everything that quotes the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Remark {
    /// What to do about it, where that is worth spelling out.
    Help,
    /// Something a reader has to know that is not advice.
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

/// One thing the compiler has to say.
///
/// Built by whichever phase found the problem and laid out by `render`. A
/// phase says what went wrong, where, and what else is worth looking at; it
/// says nothing about gutters, carets or the order the parts are printed in,
/// so that everything the compiler reports comes out looking the same.
///
/// Everything past the message and the span is optional, and the plain form --
/// a message and one span -- is what most of them are.
#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub severity:  Severity,
    /// What went wrong, in one line and with no position in it: the position
    /// is `span`'s to give, and a rendering shows it where it belongs.
    pub message:   String,
    /// What the message is about -- the piece of source it is against.
    pub span:      Span,
    /// A word or two written beside the caret. What the message says at
    /// length, this says in the margin, about the same piece of source.
    pub label:     Option<String>,
    /// Other places worth showing, each quoted where it stands. A reader
    /// cannot be pointed at two lines with one caret.
    pub secondary: Vec<Label>,
    /// The lines hung underneath, in the order they were added.
    pub remarks:   Vec<(Remark, String)>,
}

impl Diagnostic {
    /// A diagnostic of `severity` about `span`. The builders below add the
    /// rest, so that the usual one is a single expression:
    ///
    /// ```ignore
    /// Diagnostic::error("expected `,`, found `;`".to_string(), span)
    ///     .with_label("while parsing a field")
    ///     .with_help("use `,` to separate entries")
    /// ```
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

    /// What to write beside the caret.
    pub fn with_label(mut self, text: impl Into<String>) -> Diagnostic {
        self.label = Some(text.into());
        self
    }

    /// Another place to quote, under a heading of its own.
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

    /// Whether this is something that stops the build.
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    /// The message with the source under it, the way a reader wants it. See
    /// `render` for what the layout is.
    pub fn render(&self, source: &Source) -> String {
        render::diagnostic(self, source)
    }
}
