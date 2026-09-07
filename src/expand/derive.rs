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
    // A variant apiece, where it is an enum. Empty for a struct, which is what
    // tells the two apart: they are written differently and what is written
    // for them differs, a struct being one shape and an enum a choice among
    // several.
    variants: Vec<ASTNodeId>,
}

fn subject_of(parser: &Parser, node: &ASTNodeKind) -> Option<Subject> {
    match node {
        ASTNodeKind::Struct { attrs, name, generics, fields, .. } => Some(Subject {
            attrs:    attrs.clone(),
            name:     name.clone(),
            generics: generics.clone(),
            fields:   fields.clone(),
            variants: Vec::new(),
        }),
        ASTNodeKind::Enum { attrs, name, generics, variants, .. } => Some(Subject {
            attrs:    attrs.clone(),
            name:     name.clone(),
            generics: generics.clone(),
            fields:   Vec::new(),
            variants: variants.clone(),
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
    let source = match subject.variants.is_empty() {
        true => shows(parser, subject),
        false => chooses(parser, subject),
    };
    graft(parser, errors, &source, at)
}

// The head and foot every `Show` body is written between.
//
// A declaration with parameters gets an impl with the same ones, each bounded
// by the trait: every field of a `T` has to answer `Show` for the body to be
// able to ask it, and there is nothing else the bound could be. So
// `struct Box<T>` gets `impl<T: fmt::Show> fmt::Show for Box<T>`, which holds a
// caller to exactly what the body needs and no more -- a `Box<i64>` shows and a
// `Box<Nothing>` is refused where it is made into one.
fn opens(name: &str, params: &[String]) -> String {
    let (bounds, args) = match params.is_empty() {
        true => (String::new(), String::new()),
        false => {
            let held: Vec<String> =
                params.iter().map(|p| format!("{}: fmt::Show", p)).collect();
            (format!("<{}>", held.join(", ")), format!("<{}>", params.join(", ")))
        }
    };
    format!(
        "impl{} fmt::Show for {}{} {{\n    fn show(&self, into: &fmt::Sink) {{\n",
        bounds, name, args
    )
}

// The names a declaration's `<T, U>` introduces, in order. A lifetime among
// them is not a type and takes no bound, so it is not one of these.
fn param_names(parser: &Parser, generics: &[ASTNodeId]) -> Vec<String> {
    generics
        .iter()
        .filter_map(|&g| match &parser.get_node(g).kind {
            ASTNodeKind::GenericParam { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

// `fmt::put(into, "..")`, indented. What a derived body is mostly made of: the
// type's own name and the punctuation between its parts, which are the pieces
// nothing else can write.
fn says(depth: usize, text: &str) -> String {
    format!("{}fmt::put(into, \"{}\")\n", " ".repeat(depth), text)
}

// The fields of one shape, written out between the punctuation that separates
// them: `{ x: `, the field, `, y: `, the field, ` }`.
//
// Shared by the struct and the named variant because it is the same picture.
// What differs is how a field is *reached*: a struct reaches its own through
// `self`, and a variant's are bound by the pattern that matched it, so `reach`
// is `"self."` for the one and nothing for the other.
fn parts(depth: usize, head: &str, reach: &str, names: &[String]) -> String {
    let pad = " ".repeat(depth);
    if names.is_empty() {
        return says(depth, head);
    }
    let mut out = String::new();
    for (i, field) in names.iter().enumerate() {
        let between = match i {
            0 => format!("{} {{ {}: ", head, field),
            _ => format!(", {}: ", field),
        };
        out.push_str(&says(depth, &between));
        out.push_str(&format!("{}{}{}.show(into)\n", pad, reach, field));
    }
    out.push_str(&says(depth, " }"));
    out
}

// `impl fmt::Show for Point { .. }`, as a reader would have typed it.
//
// Every name in it is spelled through `fmt`, so one `import fmt::Show` is the
// whole of what a file has to write: the module is read because the import
// reads it, and a path into a module that has been read finds what is in it.
//
// The fields' *own* `show` does the work, which is why this is short however
// deep the value goes: a field that is a struct with a derive of its own
// answers with its own body, and one that is an `i64` answers with `fmt`'s.
fn shows(parser: &Parser, subject: &Subject) -> String {
    let names = field_names(parser, &subject.fields);
    let params = param_names(parser, &subject.generics);
    format!(
        "{}{}    }}\n}}\n",
        opens(&subject.name, &params),
        parts(8, &subject.name, "self.", &names)
    )
}

// `impl fmt::Show for E { .. }`, whose body is a `match` over the variants.
//
// A variant is written the way it was declared: one that carries nothing is its
// name, one that names what it carries is a brace, and one that does not is a
// parenthesis. So what comes back reads like the declaration, which is the
// point of a derive -- a reader who wrote the enum can read the line without
// being told a convention.
//
// It is a `match` on `self`, which is a `&E`, so every binding in it is a
// reference into the value and nothing is moved out of the borrow. That is what
// the derive needed and did not have: an enum carrying a struct could be lent
// and not read (§8).
fn chooses(parser: &Parser, subject: &Subject) -> String {
    let mut out = opens(&subject.name, &param_names(parser, &subject.generics));
    out.push_str("        match self {\n");
    for &held in &subject.variants {
        let ASTNodeKind::EnumVariant { name, body, .. } = &parser.get_node(held).kind else {
            continue;
        };
        let full = format!("{}::{}", subject.name, name);
        let body = body.map(|b| parser.get_node(b).kind.clone());
        match body {
            // `E::Two(a, b)`. The bindings are named here and not in the
            // declaration, a positional payload having no names of its own.
            Some(ASTNodeKind::TuplePayload(tys)) if !tys.is_empty() => {
                let held: Vec<String> =
                    (0..tys.len()).map(|i| format!("held{}", i)).collect();
                out.push_str(&format!("            {}({}) => {{\n", full, held.join(", ")));
                for (i, bound) in held.iter().enumerate() {
                    let between = match i {
                        0 => format!("{}(", name),
                        _ => ", ".to_string(),
                    };
                    out.push_str(&says(16, &between));
                    out.push_str(&format!("                {}.show(into)\n", bound));
                }
                out.push_str(&says(16, ")"));
                out.push_str("            },\n");
            }
            // `E::Three { x, y }`, in the shorthand, which binds each field
            // under its own name -- so the body below reads like the struct's.
            Some(ASTNodeKind::NamedPayload(fields)) if !fields.is_empty() => {
                let held = field_names(parser, &fields);
                out.push_str(&format!(
                    "            {} {{ {} }} => {{\n",
                    full,
                    held.join(", ")
                ));
                out.push_str(&parts(16, name, "", &held));
                out.push_str("            },\n");
            }
            // Carrying nothing, or carrying a discriminant, which is a number
            // the compiler keeps and not a value the variant holds.
            _ => out.push_str(&format!("            {} => fmt::put(into, \"{}\"),\n", full, name)),
        }
    }
    out.push_str("        }\n    }\n}\n");
    out
}

// The names a list of `FieldDecl`s declares, in order.
fn field_names(parser: &Parser, fields: &[ASTNodeId]) -> Vec<String> {
    fields
        .iter()
        .filter_map(|&f| match &parser.get_node(f).kind {
            ASTNodeKind::FieldDecl { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect()
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
