//! Patterns, and the match arms they stand in.
//!
//! One arm per rule of the grammar, in the tables' own order within each
//! group, each under the production it answers. `None` where the rule belongs
//! to another of these -- `build` tries each in turn. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_patterns(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Patterns ------------------------------------------------
            // <pattern> -> _ | <literal_pattern> | <range_pattern>
            //           |  <variant_pattern> | <tuple_pattern> | <const_pattern>
            237 | 238 | 239 | 240 | 241 | 242 => self.pass(c[0]),
            // <pattern_alternatives> -> <pattern>
            243 => self.one(c[0]),
            // <pattern_alternatives> -> <pattern_alternatives> | <pattern>
            244 => self.grew(c[0], c[2]),
            // <pattern_list> -> <pattern>
            245 => self.one(c[0]),
            // <pattern_list> -> <pattern_list> , <pattern>
            246 => self.grew(c[0], c[2]),
            // <pattern_list_opt> -> ε
            247 => self.here(ASTNodeKind::List(Vec::new())),
            // <pattern_list_opt> -> <pattern_list>
            248 => self.pass(c[0]),
            // <payload> -> ( <type_list> )
            249 => self.at(ASTNodeKind::TuplePayload(self.list(c[1])), c[0]),

            // ---- Struct patterns -----------------------------------------
            // <field_pattern> -> IDENTIFIER
            // The shorthand: the name binds itself, which is `pat: None`.
            130 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: None }, c[0])
            }
            // <field_pattern> -> IDENTIFIER : <pattern>
            131 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: Some(c[2]) }, c[0])
            }
            // <field_pattern_list> -> <field_pattern>
            132 => self.one(c[0]),
            // <field_pattern_list> -> <field_pattern_list> , <field_pattern>
            133 => self.grew(c[0], c[2]),
            // <field_pattern_list_opt> -> ε
            134 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_pattern_list_opt> -> <field_pattern_list>
            135 => self.pass(c[0]),
            // <field_pattern_list_opt> -> <field_pattern_list> ,
            136 => self.pass(c[0]),

            // ---- Variant patterns and payloads ---------------------------
            // <variant_pattern> -> <qualified_name> ( <pattern_list_opt> )
            353 => self.at(
                ASTNodeKind::VariantPat { path: self.path(c[0]), elems: self.list(c[2]) },
                c[0],
            ),
            // <variant_pattern> -> <qualified_name> VALUE_LCURLY <field_pattern_list_opt> }
            354 => self.at(
                ASTNodeKind::StructPat { path: self.path(c[0]), fields: self.list(c[2]) },
                c[0],
            ),
            // <variant_tail_opt> -> ε
            355 => self.here(ASTNodeKind::Empty),
            // <variant_tail_opt> -> <payload> | <named_payload> | <discriminant>
            356 | 357 | 358 => self.pass(c[0]),

            // ---- Match ---------------------------------------------------
            // <match_arm> -> <pattern_alternatives> => <expression>
            211 => self.at(ASTNodeKind::MatchArm { pats: self.list(c[0]), body: c[2] }, c[0]),
            // <match_arm_list> -> <match_arm>
            212 => self.one(c[0]),
            // <match_arm_list> -> <match_arm_list> , <match_arm>
            213 => self.grew(c[0], c[2]),
            // <match_arm_list_opt> -> ε
            214 => self.here(ASTNodeKind::List(Vec::new())),
            // <match_arm_list_opt> -> <match_arm_list>
            215 => self.pass(c[0]),
            // <match_arm_list_opt> -> <match_arm_list> ,
            216 => self.pass(c[0]),
            // <match_expr> -> match <header_expr> { <match_arm_list_opt> }
            217 => self.at(
                ASTNodeKind::Match { scrutinee: c[1], arms: self.list(c[3]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
