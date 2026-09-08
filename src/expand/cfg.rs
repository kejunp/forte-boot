// `%cfg(...)`: a declaration compiled only where the build says so.
//
// It runs beside `%derive` and for the same reason -- before anything reads a
// name -- and it is the other half of that pass's job: one writes a
// declaration and this takes one away. A declaration the configuration turns
// down is *not there*. Its name does not resolve, nothing it named has to
// exist, and no pass below this one is told a choice was made.
//
// **What there is to ask about.** Not a set of flags invented for the
// occasion: the compiler already knows two things about a build that a program
// might reasonably differ on, and it knew them before this file existed.
//
//   - Which machine it is compiling for, spelled as `--target` spells it with
//     a `_` where that spelling has a `-`, since a `-` is not a name. So
//     `x86_64`, `aarch64`, `riscv64`, and `x86_64_v3` and `x86_64_v4` beside
//     them.
//   - Whether it is a `--test` build, which is `test`.
//
// And what the command line supplied: `--cfg name`, however many times. That
// is the one open half, and it is open because a suite that wants a choice
// nobody here anticipated has nowhere else to put one.
//
// **Why `not`, `any` and `all` are here.** A bare name alone is half a
// feature: what a reader wants nine times in ten is "everywhere except", and
// `%cfg(not(test))` is that. The three nest, an `<attr_item>` being a name
// with arguments and the arguments being more of the same, so the grammar
// already admits them and this is the reading.

use crate::error::{Diagnostic, Diagnostics, Span};
use crate::parse::ast_nodes::{ASTNodeId, ASTNodeKind};
use crate::parse::parser::Parser;

// What a build is, as a `%cfg` may ask about it.
//
// Held by name and not by kind: which machine and whether it is a test build
// are two facts the driver already has, and turning them into a list of names
// here is what lets one rule read all three sources.
#[derive(Debug, Clone, Default)]
pub struct Config {
    held: Vec<String>,
}

impl Config {
    // Nothing set, which is what every caller that is not the driver wants:
    // a `%cfg` in a test of another pass is a `%cfg` of nothing.
    pub fn none() -> Config {
        Config { held: Vec::new() }
    }

    // What the driver knows: the machine, whether this is a test build, and
    // whatever `--cfg` was given.
    pub fn of(target: &str, tests: bool, named: &[String]) -> Config {
        // A `-` is not a name, so the two spellings differ by that and by
        // nothing else -- `--target x86-64` is `%cfg(x86_64)`.
        let mut held = vec![target.replace('-', "_")];
        if tests {
            held.push("test".to_string());
        }
        held.extend(named.iter().cloned());
        Config { held }
    }

    fn has(&self, name: &str) -> bool {
        self.held.iter().any(|one| one == name)
    }
}

// Whether every `%cfg` on this declaration holds.
//
// Every one and not any: two written on a declaration are two conditions, the
// way two written in one `all` would be, and a reader who wanted either wrote
// `any`.
pub(super) fn holds(
    parser: &Parser,
    errors: &mut Diagnostics,
    config: &Config,
    attrs: &[ASTNodeId],
) -> bool {
    let mut out = true;
    for held in attrs {
        let ASTNodeKind::Attr { name, args } = &parser.get_node(*held).kind else { continue };
        if name != "cfg" {
            continue;
        }
        let at = span_of(parser, *held);
        let [one] = args[..] else {
            errors.push(
                Diagnostic::error("`%cfg` takes one condition".to_string(), at)
                    .with_label("this is what it was given")
                    .with_help(HELP),
            );
            continue;
        };
        out &= asked(parser, errors, config, one);
    }
    out
}

// One condition. Unknown shapes are refused and read as false, so a mistake
// takes the declaration out rather than leaving it in under a rule nobody
// meant.
fn asked(
    parser: &Parser,
    errors: &mut Diagnostics,
    config: &Config,
    at: ASTNodeId,
) -> bool {
    let node = parser.get_node(at);
    let where_ = Span::at(node.line, node.col);
    let ASTNodeKind::Attr { name, args } = &node.kind else {
        errors.push(
            Diagnostic::error("`%cfg` takes a name".to_string(), where_)
                .with_label("this is not one")
                .with_help(HELP),
        );
        return false;
    };
    match (name.as_str(), args.len()) {
        ("not", 1) => !asked(parser, errors, config, args[0]),
        ("not", _) => {
            errors.push(
                Diagnostic::error("`not` takes one condition".to_string(), where_)
                    .with_label("this is what it was given"),
            );
            false
        }
        ("any", _) => args.iter().any(|&one| asked(parser, errors, config, one)),
        ("all", _) => args.iter().all(|&one| asked(parser, errors, config, one)),
        // A bare name, which is the whole of what a condition is once the
        // three above are spent.
        (held, 0) => config.has(held),
        (held, _) => {
            errors.push(
                Diagnostic::error(format!("`{}` takes no conditions", held), where_)
                    .with_label("a name is asked about on its own")
                    .with_help(HELP),
            );
            false
        }
    }
}

fn span_of(parser: &Parser, at: ASTNodeId) -> Span {
    let node = parser.get_node(at);
    Span::at(node.line, node.col)
}

const HELP: &str = "a condition is a name -- the machine, `test` in a test build, or one \
                    `--cfg` gave -- or `not`, `any` or `all` of them";
