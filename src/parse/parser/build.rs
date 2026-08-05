//! What each rule of the grammar makes of the children it just took.
//!
//! One arm per rule and nothing to derive them from: the tables say which rule
//! fired, and what that rule *means* is only written across this module. Each
//! arm sits under the production it answers, and the productions are grouped by
//! what they build -- `items`, `exprs`, `types`, `patterns`, `stmts`,
//! `literals` -- one group to a file. Within a group they keep the tables'
//! own order.
//!
//! Grouped that way rather than by rule number because the numbers are not
//! ours: the generator gives them, and adding one rule to docs/grammar.bnf
//! shifts every id after it. A file whose contents were a range of numbers
//! would have to be re-cut on every regeneration; one whose contents are
//! `everything that builds a type` does not.
//!
//! Three shapes cover most of it. A rule with one symbol and nothing of its own
//! to say passes its child up (`pass`). A `<..._list>` gathers handles into a
//! `List`, and an `<..._opt>` that was not written reduces to `Empty`, which is
//! what `list` and `opt` read back. Everything else names an `ASTNodeKind` and
//! fills it from the children. Those readers are `nodes`, and `marks` takes an
//! operator back out of the node the grammar made the writer spell it as.
//!
//! What a rule cannot do is reach leftwards: `<postfix_op>` is reduced before
//! the parse says what it is a suffix of, and an `<array_suffix>` before it
//! says what it is a suffix of either. Those are built with `HOLE` where the
//! base goes, and the rule above fills it in -- `with_base` and
//! `fold_suffixes`. It is the one place a node is finished after it is made.

use super::*;
use ast_nodes::{
    ASTAssignOp, ASTBinOp, ASTBinding, ASTLit, ASTMark, ASTNode, ASTNodeKind, ASTPrimType,
    ASTRangeOp, ASTRefOp, ASTUnaryOp, ASTVariableIntro, ASTVisibility,
};

mod exprs;
mod items;
mod literals;
mod marks;
mod nodes;
mod patterns;
mod stmts;
mod types;
#[cfg(test)]
mod tests;

use marks::*;

/// Where a base belongs in a node built before its base was known. Handle 0 is
/// the arena's nothing-node, so a hole left unfilled is a node standing on
/// nothing rather than on the wrong thing.
const HOLE: ASTNodeId = 0;

impl Parser {
    /// What a rule builds out of the children it just took.
    ///
    /// The arms are grouped by what they build rather than by rule number, one
    /// group to a file, and each group turns down a rule that is not its own.
    /// Trying them in turn costs a handful of jump tables where one would do,
    /// and buys a layout with no rule numbers written into it: the grammar is
    /// regenerated often and every id after an added rule shifts, so an arm
    /// moved between files is a thing a reader can see and a boundary written
    /// in numbers is not.
    pub(super) fn build(&mut self, rule_id: tables::RuleId, children: &[ASTNodeId]) -> ASTNode {
        let c = children;
        if let Some(node) = self.build_items(rule_id, c) {
            return node;
        }
        if let Some(node) = self.build_exprs(rule_id, c) {
            return node;
        }
        if let Some(node) = self.build_types(rule_id, c) {
            return node;
        }
        if let Some(node) = self.build_patterns(rule_id, c) {
            return node;
        }
        if let Some(node) = self.build_stmts(rule_id, c) {
            return node;
        }
        if let Some(node) = self.build_literals(rule_id, c) {
            return node;
        }

        // The tables and these arms are generated from and written against the
        // same grammar, so a rule with no arm is the two having come apart --
        // not a source being wrong.
        panic!("rule {} has no arm in `build`", rule_id)
    }
}
