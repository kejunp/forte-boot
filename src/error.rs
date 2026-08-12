// What the compiler has to say, and how it says it. A phase builds a
// `Diagnostic` and pushes it into a `Diagnostics`; `render` settles what a
// report looks like, so every phase reads the same way.
//
//   - `Span`        a piece of a source, in characters from one
//   - `Source`      the text to quote from and what to call it
//   - `Diagnostic`  one thing to say: `Severity`, inline `label`, `secondary`
//                   places to look, `Remark` lines underneath
//   - `Diagnostics` everything a phase said, and whether it stops the build
//
// Reporting is one expression:
//
//     report.push(
//         Diagnostic::error(format!("no field `{}` on `{}`", name, ty), span)
//             .with_label("unknown field")
//             .with_secondary(decl, "the type is declared")
//             .with_help("the fields are `x` and `y`"),
//     );
//
// and printing it is `report.render(&Source::new(path, text))`.

// The whole vocabulary is written and tested here rather than grown a piece at
// a time, which is what would make two phases report differently. The allow is
// for the parts no phase has reached yet, and comes off once one has.
#![allow(dead_code)]

pub mod diagnostic;
pub mod render;
pub mod report;
pub mod source;
pub mod span;

// The front door: `use crate::error::{Diagnostic, Span}` and a phase has what
// it needs. `Label`, `Remark` and `Severity` are part of what a diagnostic is,
// though nothing outside this module has had to spell one out yet.
#[allow(unused_imports)]
pub use diagnostic::{Diagnostic, Label, Remark, Severity};
pub use report::Diagnostics;
pub use source::Source;
pub use span::Span;
