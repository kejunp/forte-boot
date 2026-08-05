//! What the compiler has to say, and how it says it.
//!
//! Every part of the compiler finds things wrong with a source, and none of
//! them should have an opinion about how that is written down. A phase builds
//! a `Diagnostic` -- what went wrong, where, and what else is worth looking at
//! -- and drops it in a `Diagnostics`. What a report looks like is settled in
//! one place, `render`, so that a message from the lexer and a message from
//! the type checker are read the same way.
//!
//! The parts:
//!
//!   - `Span` is a piece of a source, counted in characters from one;
//!   - `Source` is the text to quote from and what to call it;
//!   - `Diagnostic` is one thing to say, with a `Severity` saying how much it
//!     matters, an inline `label` beside the caret, `secondary` places to look
//!     and `Remark` lines hung underneath;
//!   - `Diagnostics` is everything a phase said, and answers whether any of it
//!     stops the build.
//!
//! Reporting something is one expression:
//!
//! ```ignore
//! report.push(
//!     Diagnostic::error(format!("no field `{}` on `{}`", name, ty), span)
//!         .with_label("unknown field")
//!         .with_secondary(decl, "the type is declared")
//!         .with_help("the fields are `x` and `y`"),
//! );
//! ```
//!
//! and printing it is `report.render(&Source::new(path, text))`.
//!
//! Nothing here knows what a token, a rule or a type is. A phase says what it
//! found in words it chose, and this arranges those words on the page: the two
//! are kept apart so that neither has to be changed to alter the other.

// This is the vocabulary the whole compiler reports in, and the parser is so
// far the only phase that has anything to say. What the rest of it will want
// -- a warning, a second place to look, a report handed on from the phase
// before -- is written and tested here rather than added a piece at a time by
// whoever needs it first, which is what would make two phases report
// differently. Every item below is exercised by the tests in this module; the
// allow is for the parts no *phase* has reached yet, and should come off once
// one has.
#![allow(dead_code)]

pub mod diagnostic;
pub mod render;
pub mod report;
pub mod source;
pub mod span;

// The front door: a phase says `use crate::error::{Diagnostic, Span}` and has
// what it needs. `Label`, `Remark` and `Severity` are named here for the same
// reason -- they are part of what a diagnostic is -- though nothing outside
// this module has had to spell one out yet.
#[allow(unused_imports)]
pub use diagnostic::{Diagnostic, Label, Remark, Severity};
pub use report::Diagnostics;
pub use source::Source;
pub use span::Span;
