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
            275 => self.pass(c[0]),
            // <pattern> -> _ | <literal_pattern> | <range_pattern>
            //           |  <variant_pattern> | <tuple_pattern> | <const_pattern>
            274 | 276 | 277 | 278 | 279 | 280 => self.pass(c[0]),
            // <pattern_alternatives> -> <pattern>
            281 => self.one(c[0]),
            // <pattern_alternatives> -> <pattern_alternatives> | <pattern>
            282 => self.grew(c[0], c[2]),
            // <pattern_list> -> <pattern>
            283 => self.one(c[0]),
            // <pattern_list> -> <pattern_list> , <pattern>
            284 => self.grew(c[0], c[2]),
            // <pattern_list_opt> -> ε
            285 => self.here(ASTNodeKind::List(Vec::new())),
            // <pattern_list_opt> -> <pattern_list>
            286 => self.pass(c[0]),
            // <payload> -> ( <type_list> )
            287 => self.at(ASTNodeKind::TuplePayload(self.list(c[1])), c[0]),

            // ---- Struct patterns -----------------------------------------
            // <field_pattern> -> IDENTIFIER
            // The shorthand: the name binds itself, which is `pat: None`.
            137 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: None }, c[0])
            }
            // <field_pattern> -> IDENTIFIER : <pattern>
            138 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: Some(c[2]) }, c[0])
            }
            // <field_pattern_list> -> <field_pattern>
            139 => self.one(c[0]),
            // <field_pattern_list> -> <field_pattern_list> , <field_pattern>
            140 => self.grew(c[0], c[2]),
            // <field_pattern_list_opt> -> ε
            141 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_pattern_list_opt> -> <field_pattern_list>
            142 => self.pass(c[0]),
            // <field_pattern_list_opt> -> <field_pattern_list> ,
            143 => self.pass(c[0]),

            // ---- Variant patterns and payloads ---------------------------
            // <variant_pattern> -> <qualified_name> ( <pattern_list_opt> )
            417 => self.at(
                ASTNodeKind::VariantPat { path: self.path(c[0]), elems: self.list(c[2]) },
                c[0],
            ),
            // <variant_pattern> -> <qualified_name> VALUE_LCURLY <field_pattern_list_opt> }
            418 => self.at(
                ASTNodeKind::StructPat { path: self.path(c[0]), fields: self.list(c[2]) },
                c[0],
            ),
            // <variant_tail_opt> -> ε
            419 => self.here(ASTNodeKind::Empty),
            // <variant_tail_opt> -> <payload> | <named_payload> | <discriminant>
            420 | 421 | 422 => self.pass(c[0]),

            // ---- Match ---------------------------------------------------
            // <match_arm> -> <pattern_alternatives> => <expression>
            245 => self.at(ASTNodeKind::MatchArm { pats: self.list(c[0]), body: c[2] }, c[0]),
            // <match_arm_list> -> <match_arm>
            246 => self.one(c[0]),
            // <match_arm_list> -> <match_arm_list> , <match_arm>
            247 => self.grew(c[0], c[2]),
            // <match_arm_list_opt> -> ε
            248 => self.here(ASTNodeKind::List(Vec::new())),
            // <match_arm_list_opt> -> <match_arm_list>
            249 => self.pass(c[0]),
            // <match_arm_list_opt> -> <match_arm_list> ,
            250 => self.pass(c[0]),
            // <match_expr> -> match <header_expr> { <match_arm_list_opt> }
            251 => self.at(
                ASTNodeKind::Match { scrutinee: c[1], arms: self.list(c[3]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
