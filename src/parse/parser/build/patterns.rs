// Patterns, and the match arms they stand in.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_patterns(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Patterns ------------------------------------------------
            // <pattern> -> MACRO_PARAM
            257 => self.pass(c[0]),
            // <pattern> -> _ | <literal_pattern> | <range_pattern>
            //           |  <variant_pattern> | <tuple_pattern> | <const_pattern>
            256 | 258 | 259 | 260 | 261 | 262 => self.pass(c[0]),
            // <pattern_alternatives> -> <pattern>
            263 => self.one(c[0]),
            // <pattern_alternatives> -> <pattern_alternatives> | <pattern>
            264 => self.grew(c[0], c[2]),
            // <pattern_list> -> <pattern>
            265 => self.one(c[0]),
            // <pattern_list> -> <pattern_list> , <pattern>
            266 => self.grew(c[0], c[2]),
            // <pattern_list_opt> -> ε
            267 => self.here(ASTNodeKind::List(Vec::new())),
            // <pattern_list_opt> -> <pattern_list>
            268 => self.pass(c[0]),
            // <payload> -> ( <type_list> )
            269 => self.at(ASTNodeKind::TuplePayload(self.list(c[1])), c[0]),

            // ---- Struct patterns -----------------------------------------
            // <field_pattern> -> IDENTIFIER
            // The shorthand: the name binds itself, which is `pat: None`.
            133 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: None }, c[0])
            }
            // <field_pattern> -> IDENTIFIER : <pattern>
            134 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: Some(c[2]) }, c[0])
            }
            // <field_pattern_list> -> <field_pattern>
            135 => self.one(c[0]),
            // <field_pattern_list> -> <field_pattern_list> , <field_pattern>
            136 => self.grew(c[0], c[2]),
            // <field_pattern_list_opt> -> ε
            137 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_pattern_list_opt> -> <field_pattern_list>
            138 => self.pass(c[0]),
            // <field_pattern_list_opt> -> <field_pattern_list> ,
            139 => self.pass(c[0]),

            // ---- Variant patterns and payloads ---------------------------
            // <variant_pattern> -> <qualified_name> ( <pattern_list_opt> )
            381 => self.at(
                ASTNodeKind::VariantPat { path: self.path(c[0]), elems: self.list(c[2]) },
                c[0],
            ),
            // <variant_pattern> -> <qualified_name> VALUE_LCURLY <field_pattern_list_opt> }
            382 => self.at(
                ASTNodeKind::StructPat { path: self.path(c[0]), fields: self.list(c[2]) },
                c[0],
            ),
            // <variant_tail_opt> -> ε
            383 => self.here(ASTNodeKind::Empty),
            // <variant_tail_opt> -> <payload> | <named_payload> | <discriminant>
            384 | 385 | 386 => self.pass(c[0]),

            // ---- Match ---------------------------------------------------
            // <match_arm> -> <pattern_alternatives> => <expression>
            230 => self.at(ASTNodeKind::MatchArm { pats: self.list(c[0]), body: c[2] }, c[0]),
            // <match_arm_list> -> <match_arm>
            231 => self.one(c[0]),
            // <match_arm_list> -> <match_arm_list> , <match_arm>
            232 => self.grew(c[0], c[2]),
            // <match_arm_list_opt> -> ε
            233 => self.here(ASTNodeKind::List(Vec::new())),
            // <match_arm_list_opt> -> <match_arm_list>
            234 => self.pass(c[0]),
            // <match_arm_list_opt> -> <match_arm_list> ,
            235 => self.pass(c[0]),
            // <match_expr> -> match <header_expr> { <match_arm_list_opt> }
            236 => self.at(
                ASTNodeKind::Match { scrutinee: c[1], arms: self.list(c[3]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
