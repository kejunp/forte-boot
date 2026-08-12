// The TIR -- the tree IR: what the source means rather than what it was
// written as, still shaped as a tree. The AST beside it is of what was written.
//
// Where it sits:
//
//     prep -> lex -> parse -> AST -> expand -> lower -> TIR -> sema
//
// Lowering is the last pass that cares how the source was written, and the
// first that does not have to: it drops what the grammar needed and the
// language does not -- the `<..._opt>` that was not written, the ladder of
// precedence rules that built one operand, the four places one declaration can
// be spelled -- and settles every closed question a single declaration answers
// on its own. The attributes are that shape: the set is closed, so `@inline`
// becomes a field here and no pass downstream ever compares a string.
//
// What it does *not* do is decide anything that needs another declaration to be
// in hand. No name is resolved, no type is worked out, no reference is checked.
// That is `sema`'s, and it runs on this rather than beside it -- which is the
// whole reason the TIR exists as a thing of its own rather than as a pass over
// the AST.
//
// The pass that builds it lives here beside the nodes it makes: `lower` is the
// TIR's own front door and has no reader but this module's, where `sema` will
// be the one that comes after.

pub mod lower;
pub mod tir_nodes;
