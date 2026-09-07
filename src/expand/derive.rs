// `%derive(Show)`: the impl a reader would have written, written for them.
//
// It runs here, beside macro expansion and for the same reason: what a derive
// stands for is written in the language and is parsed as the language, so it
// belongs on the AST and nothing below this pass has to know one happened.
// `sema` is handed a file with the impl in it and cannot tell it from one the
// reader typed.
//
// **It is text, parsed.** The impl is generated as source and read by a parser
// of its own, and the tree that comes back is grafted into this one. Building
// the nodes by hand would be the same tree written twice as long, and it would
// be a second place where what the language means by "an impl" is spelled out
// -- the parser being the first, and the one that is right by construction.
// What this file has to get right is a program a reader could have typed, which
// is a thing that can be looked at.
//
// **The set is closed**, as `<attribute>`'s own set is (§1): what may be
// derived is what this file knows how to write, and a name it does not know is
// an error where it is written rather than a trait somebody supplies later.
// Deriving is compiler knowledge -- the body is not something a library can
// hand over -- so a `%derive(Show)` names *this* `Show` and not any other.

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::lex::lexer::Lexer;
use crate::parse::ast_nodes::{ASTNode, ASTNodeId, ASTNodeKind};
use crate::parse::parser::Parser;

use super::children_mut;

// What `%derive` may name.
pub(super) const DERIVABLE: &[&str] = &["Show"];

// Every impl the derives on these items ask for, appended to the list they came
// from by the caller.
//
// A namespace holds items and is walked into, a derive inside one being a
// derive like any other.
pub(super) fn derived(
    parser: &mut Parser,
    errors: &mut Diagnostics,
    items: &[ASTNodeId],
) -> Vec<ASTNodeId> {
    let mut out = Vec::new();
    for &item in items {
        let node = parser.get_node(item).kind.clone();
        if let ASTNodeKind::Namespace { items, .. } = &node {
            let held = derived(parser, errors, &items.clone());
            out.extend(held);
            continue;
        }
        let Some(subject) = subject_of(parser, &node) else { continue };
        for (name, at) in asked(parser, errors, &subject.attrs) {
            match written(parser, errors, &subject, &name, at) {
                Some(held) => out.push(held),
                None => {}
            }
        }
    }
    out
}

// What a derive can be written on, read off the declaration.
struct Subject {
    attrs:    Vec<ASTNodeId>,
    name:     String,
    generics: Vec<ASTNodeId>,
    fields:   Vec<ASTNodeId>,
    // Whether it is a struct. An enum carries a derive as readily and there is
    // nothing here that writes one yet, so the two are told apart to say so.
    is_struct: bool,
}

fn subject_of(parser: &Parser, node: &ASTNodeKind) -> Option<Subject> {
    match node {
        ASTNodeKind::Struct { attrs, name, generics, fields, .. } => Some(Subject {
            attrs:     attrs.clone(),
            name:      name.clone(),
            generics:  generics.clone(),
            fields:    fields.clone(),
            is_struct: true,
        }),
        ASTNodeKind::Enum { attrs, name, generics, .. } => Some(Subject {
            attrs:     attrs.clone(),
            name:      name.clone(),
            generics:  generics.clone(),
            fields:    Vec::new(),
            is_struct: false,
        }),
        _ => {
            let _ = parser;
            None
        }
    }
}

// The names one declaration's `%derive`s asked for, each with where it was
// written. A `%derive` with nothing in it is not a mistake -- it asks for
// nothing and gets nothing -- and every other attribute is somebody else's.
fn asked(
    parser: &Parser,
    errors: &mut Diagnostics,
    attrs: &[ASTNodeId],
) -> Vec<(String, Span)> {
    let mut out = Vec::new();
    for &held in attrs {
        let ASTNodeKind::Attr { name, args } = &parser.get_node(held).kind else { continue };
        if name != "derive" {
            continue;
        }
        for &arg in args {
            let node = parser.get_node(arg);
            let at = Span::at(node.line, node.col);
            // An `<attr_item>` is an `Attr` of its own -- `%repr(C)` and
            // `%derive(Show)` are one shape, a name with arguments it did not
            // write -- so what a derive names arrives as a nested attribute
            // and not as an identifier.
            let name = match &node.kind {
                ASTNodeKind::Attr { name, args } if args.is_empty() => name.clone(),
                _ => {
                    errors.push(
                        Diagnostic::error("`%derive` takes the name of a trait".to_string(), at)
                            .with_label("this is not a name")
                            .with_help(format!("what may be derived is {}", list(DERIVABLE))),
                    );
                    continue;
                }
            };
            out.push((name, at));
        }
    }
    out
}

// One derive: the source of the impl it stands for, parsed and grafted in.
fn written(
    parser: &mut Parser,
    errors: &mut Diagnostics,
    subject: &Subject,
    name: &str,
    at: Span,
) -> Option<ASTNodeId> {
    if !DERIVABLE.contains(&name) {
        errors.push(
            Diagnostic::error(format!("`{}` is not something `%derive` writes", name), at)
                .with_label("nothing here knows how to write this one")
                .with_note(
                    "deriving is the compiler's knowledge and not a library's: the body \
                     is what has to be written, and only what is listed has one",
                )
                .with_help(format!("what may be derived is {}", list(DERIVABLE))),
        );
        return None;
    }
    if !subject.is_struct {
        errors.push(
            Diagnostic::error(format!("`%derive({})` is written on a struct", name), at)
                .with_label("this is an enum")
                .with_note(
                    "what an enum looks like is a `match` over its variants, and that \
                     is a body this does not write yet",
                ),
        );
        return None;
    }
    if !subject.generics.is_empty() {
        errors.push(
            Diagnostic::error(
                format!("`%derive({})` is written on a struct with no parameters", name),
                at,
            )
            .with_label("this one has parameters")
            .with_note(
                "an impl over a parameter has to bound it -- every field of a `T` has \
                 to answer the trait too -- and that is a signature this does not \
                 write yet",
            ),
        );
        return None;
    }

    let source = shows(parser, subject);
    graft(parser, errors, &source, at)
}

// `impl fmt::Show for Point { .. }`, as a reader would have typed it.
//
// Every name in it is spelled through `fmt`, so one `import fmt::Show` is the
// whole of what a file has to write: the module is read because the import
// reads it, and a path into a module that has been read finds what is in it.
//
// The fields' *own* `show` does the work, which is why this is three lines
// however deep the value goes: a field that is a struct with a derive of its
// own answers with its own body, and one that is an `i64` answers with `fmt`'s.
fn shows(parser: &Parser, subject: &Subject) -> String {
    let mut out = format!(
        "impl fmt::Show for {} {{\n    fn show(&self, into: &fmt::Sink) {{\n",
        subject.name
    );
    let names: Vec<String> = subject
        .fields
        .iter()
        .filter_map(|&f| match &parser.get_node(f).kind {
            ASTNodeKind::FieldDecl { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();

    // A struct with no fields is its name and nothing else, which is what the
    // reader wrote and what they will want to read back.
    if names.is_empty() {
        out.push_str(&format!("        fmt::put(into, \"{}\")\n", subject.name));
    } else {
        for (i, field) in names.iter().enumerate() {
            let between = match i {
                0 => format!("{} {{ {}: ", subject.name, field),
                _ => format!(", {}: ", field),
            };
            out.push_str(&format!("        fmt::put(into, \"{}\")\n", between));
            out.push_str(&format!("        self.{}.show(into)\n", field));
        }
        out.push_str("        fmt::put(into, \" }\")\n");
    }
    out.push_str("    }\n}\n");
    out
}

// The source read as a file, and its one item grafted into the tree this pass
// is walking.
//
// Every node takes the position of the `%derive` that asked for it. The lines
// it was parsed out of are nowhere a reader can look, so a message about the
// derived impl points at the word that wrote it, which is the thing they can
// change.
fn graft(
    parser: &mut Parser,
    errors: &mut Diagnostics,
    source: &str,
    at: Span,
) -> Option<ASTNodeId> {
    let mut held = Parser::new(Lexer::new(source));
    let root = held.parse();
    if !held.errors().is_empty() {
        // Nothing a program can do reaches here: what was parsed is written by
        // the file above and not by anybody's source. It is said rather than
        // asserted because a compiler that stops with no message is worse than
        // one that says something odd.
        errors.push(
            Diagnostic::error("this derive could not be written".to_string(), at)
                .with_label("the impl it stands for did not parse")
                .with_note(source.to_string()),
        );
        return None;
    }
    let ASTNodeKind::Program(items) = &root.kind else { return None };
    let &item = items.first()?;
    Some(copy(parser, &held, item, at))
}

// One node and everything under it, into the other arena.
fn copy(into: &mut Parser, from: &Parser, id: ASTNodeId, at: Span) -> ASTNodeId {
    let mut kind = from.get_node(id).kind.clone();
    let old: Vec<ASTNodeId> = children_mut(&mut kind).into_iter().map(|slot| *slot).collect();
    let new: Vec<ASTNodeId> = old.iter().map(|&child| copy(into, from, child, at)).collect();
    for (slot, id) in children_mut(&mut kind).into_iter().zip(&new) {
        *slot = *id;
    }
    into.push_node(ASTNode::new(kind, at.line, at.col))
}

// `Show` for one and `Show or Copy` for two, which is how the rest of this
// compiler spells a closed list in a message.
fn list(names: &[&str]) -> String {
    match names {
        [] => String::new(),
        [one] => format!("`{}`", one),
        [held @ .., last] => {
            let held: Vec<String> = held.iter().map(|n| format!("`{}`", n)).collect();
            format!("{} or `{}`", held.join(", "), last)
        }
    }
}
