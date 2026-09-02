// Statements, and the block forms that are expressions as well.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_stmts(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Statements ----------------------------------------------
            // <statement> -> <declaration> | <unsafe_stmt> | <expr_stmt>
            353 | 354 | 355 => self.pass(c[0]),
            // <statement_list> -> ε
            356 => self.here(ASTNodeKind::List(Vec::new())),
            // <statement_list> -> <statement_list> <statement>
            357 => self.grew(c[0], c[1]),

            // ---- Blocks --------------------------------------------------
            // <block> -> { <statement_list> <block_tail_opt> }
            56 => self.at(
                ASTNodeKind::Block { stmts: self.list(c[1]), tail: self.opt(c[2]) },
                c[0],
            ),
            // <block_expr> -> <block> | <if_expr> | <while_expr> | <for_expr>
            //              |  <match_expr>
            57 | 58 | 59 | 60 | 61 => self.pass(c[0]),
            // <block_tail_opt> -> ε
            62 => self.here(ASTNodeKind::Empty),
            // <block_tail_opt> -> <unterminated_stmt>
            63 => self.pass(c[0]),

            // ---- Conditionals --------------------------------------------
            // <header_expr> -> <assignment>
            176 => self.pass(c[0]),
            // <if_expr> -> if <header_expr> <block> <elif_list> <else_opt>
            177 => self.at(
                ASTNodeKind::If {
                    cond: c[1],
                    then: c[2],
                    elifs: self.list(c[3]),
                    else_block: self.opt(c[4]),
                },
                c[0],
            ),

            // ---- Loops ---------------------------------------------------
            // <for_expr> -> for <binding_name> in <header_expr> <block>
            155 => self.at(
                ASTNodeKind::For { name: self.binding(c[1]), iter: c[3], body: c[4] },
                c[0],
            ),

            // ---- Loops, continued ----------------------------------------
            // <while_expr> -> while <header_expr> <block>
            433 => self.at(ASTNodeKind::While { cond: c[1], body: c[2] }, c[0]),

            // ---- unsafe --------------------------------------------------
            // <unsafe_stmt> -> unsafe <expr_stmt>
            394 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),
            // <unsafe_stmt> -> unsafe <var_decl>
            395 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            _ => return None,
        })
    }
}
