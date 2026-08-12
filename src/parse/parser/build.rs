// What each rule of the grammar makes of the children it just took. One arm
// per rule, grouped by what they build -- `items`, `exprs`, `types`,
// `patterns`, `stmts`, `literals` -- one group to a file, in the tables' order.
//
// Grouped that way and not by rule number because the numbers are the
// generator's: adding a rule to docs/grammar.bnf shifts every id after it.
//
// Three shapes cover most of it. A rule with one symbol passes its child up
// (`pass`). A `<..._list>` gathers handles into a `List`, and an unwritten
// `<..._opt>` reduces to `Empty` -- `list` and `opt` read those back. The rest
// name an `ASTNodeKind` and fill it from the children, using `nodes`, plus
// `marks` to take an operator back out of the node the grammar spelled it as.
//
// What a rule cannot do is reach leftwards: `<postfix_op>` and `<array_suffix>`
// reduce before the parse says what they are a suffix of. Those get a `HOLE`
// where the base goes and the rule above fills it in -- `with_base` and
// `fold_suffixes`, the one place a node is finished after it is made.

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

// Where a base belongs in a node built before its base was known. Handle 0 is
// the arena's nothing-node, so an unfilled hole stands on nothing rather than
// on the wrong thing.
const HOLE: ASTNodeId = 0;

impl Parser {
    // What a rule builds out of the children it just took. Each group turns
    // down a rule that is not its own; trying them in turn costs a handful of
    // jump tables where one would do, and buys a layout with no rule numbers
    // written into it.
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
