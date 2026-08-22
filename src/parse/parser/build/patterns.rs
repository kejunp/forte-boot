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
            270 => self.pass(c[0]),
            // <pattern> -> _ | <literal_pattern> | <range_pattern>
            //           |  <variant_pattern> | <tuple_pattern> | <const_pattern>
            269 | 271 | 272 | 273 | 274 | 275 => self.pass(c[0]),
            // <pattern_alternatives> -> <pattern>
            276 => self.one(c[0]),
            // <pattern_alternatives> -> <pattern_alternatives> | <pattern>
            277 => self.grew(c[0], c[2]),
            // <pattern_list> -> <pattern>
            278 => self.one(c[0]),
            // <pattern_list> -> <pattern_list> , <pattern>
            279 => self.grew(c[0], c[2]),
            // <pattern_list_opt> -> ε
            280 => self.here(ASTNodeKind::List(Vec::new())),
            // <pattern_list_opt> -> <pattern_list>
            281 => self.pass(c[0]),
            // <payload> -> ( <type_list> )
            282 => self.at(ASTNodeKind::TuplePayload(self.list(c[1])), c[0]),

            // ---- Struct patterns -----------------------------------------
            // <field_pattern> -> IDENTIFIER
            // The shorthand: the name binds itself, which is `pat: None`.
            136 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: None }, c[0])
            }
            // <field_pattern> -> IDENTIFIER : <pattern>
            137 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: Some(c[2]) }, c[0])
            }
            // <field_pattern_list> -> <field_pattern>
            138 => self.one(c[0]),
            // <field_pattern_list> -> <field_pattern_list> , <field_pattern>
            139 => self.grew(c[0], c[2]),
            // <field_pattern_list_opt> -> ε
            140 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_pattern_list_opt> -> <field_pattern_list>
            141 => self.pass(c[0]),
            // <field_pattern_list_opt> -> <field_pattern_list> ,
            142 => self.pass(c[0]),

            // ---- Variant patterns and payloads ---------------------------
            // <variant_pattern> -> <qualified_name> ( <pattern_list_opt> )
            409 => self.at(
                ASTNodeKind::VariantPat { path: self.path(c[0]), elems: self.list(c[2]) },
                c[0],
            ),
            // <variant_pattern> -> <qualified_name> VALUE_LCURLY <field_pattern_list_opt> }
            410 => self.at(
                ASTNodeKind::StructPat { path: self.path(c[0]), fields: self.list(c[2]) },
                c[0],
            ),
            // <variant_tail_opt> -> ε
            411 => self.here(ASTNodeKind::Empty),
            // <variant_tail_opt> -> <payload> | <named_payload> | <discriminant>
            412 | 413 | 414 => self.pass(c[0]),

            // ---- Match ---------------------------------------------------
            // <match_arm> -> <pattern_alternatives> => <expression>
            240 => self.at(ASTNodeKind::MatchArm { pats: self.list(c[0]), body: c[2] }, c[0]),
            // <match_arm_list> -> <match_arm>
            241 => self.one(c[0]),
            // <match_arm_list> -> <match_arm_list> , <match_arm>
            242 => self.grew(c[0], c[2]),
            // <match_arm_list_opt> -> ε
            243 => self.here(ASTNodeKind::List(Vec::new())),
            // <match_arm_list_opt> -> <match_arm_list>
            244 => self.pass(c[0]),
            // <match_arm_list_opt> -> <match_arm_list> ,
            245 => self.pass(c[0]),
            // <match_expr> -> match <header_expr> { <match_arm_list_opt> }
            246 => self.at(
                ASTNodeKind::Match { scrutinee: c[1], arms: self.list(c[3]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
