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
            266 => self.pass(c[0]),
            // <pattern> -> _ | <literal_pattern> | <range_pattern>
            //           |  <variant_pattern> | <tuple_pattern> | <const_pattern>
            265 | 267 | 268 | 269 | 270 | 271 => self.pass(c[0]),
            // <pattern_alternatives> -> <pattern>
            272 => self.one(c[0]),
            // <pattern_alternatives> -> <pattern_alternatives> | <pattern>
            273 => self.grew(c[0], c[2]),
            // <pattern_list> -> <pattern>
            274 => self.one(c[0]),
            // <pattern_list> -> <pattern_list> , <pattern>
            275 => self.grew(c[0], c[2]),
            // <pattern_list_opt> -> ε
            276 => self.here(ASTNodeKind::List(Vec::new())),
            // <pattern_list_opt> -> <pattern_list>
            277 => self.pass(c[0]),
            // <payload> -> ( <type_list> )
            278 => self.at(ASTNodeKind::TuplePayload(self.list(c[1])), c[0]),

            // ---- Struct patterns -----------------------------------------
            // <field_pattern> -> IDENTIFIER
            // The shorthand: the name binds itself, which is `pat: None`.
            135 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: None }, c[0])
            }
            // <field_pattern> -> IDENTIFIER : <pattern>
            136 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldPat { name, pat: Some(c[2]) }, c[0])
            }
            // <field_pattern_list> -> <field_pattern>
            137 => self.one(c[0]),
            // <field_pattern_list> -> <field_pattern_list> , <field_pattern>
            138 => self.grew(c[0], c[2]),
            // <field_pattern_list_opt> -> ε
            139 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_pattern_list_opt> -> <field_pattern_list>
            140 => self.pass(c[0]),
            // <field_pattern_list_opt> -> <field_pattern_list> ,
            141 => self.pass(c[0]),

            // ---- Variant patterns and payloads ---------------------------
            // <variant_pattern> -> <qualified_name> ( <pattern_list_opt> )
            400 => self.at(
                ASTNodeKind::VariantPat { path: self.path(c[0]), elems: self.list(c[2]) },
                c[0],
            ),
            // <variant_pattern> -> <qualified_name> VALUE_LCURLY <field_pattern_list_opt> }
            401 => self.at(
                ASTNodeKind::StructPat { path: self.path(c[0]), fields: self.list(c[2]) },
                c[0],
            ),
            // <variant_tail_opt> -> ε
            402 => self.here(ASTNodeKind::Empty),
            // <variant_tail_opt> -> <payload> | <named_payload> | <discriminant>
            403 | 404 | 405 => self.pass(c[0]),

            // ---- Match ---------------------------------------------------
            // <match_arm> -> <pattern_alternatives> => <expression>
            236 => self.at(ASTNodeKind::MatchArm { pats: self.list(c[0]), body: c[2] }, c[0]),
            // <match_arm_list> -> <match_arm>
            237 => self.one(c[0]),
            // <match_arm_list> -> <match_arm_list> , <match_arm>
            238 => self.grew(c[0], c[2]),
            // <match_arm_list_opt> -> ε
            239 => self.here(ASTNodeKind::List(Vec::new())),
            // <match_arm_list_opt> -> <match_arm_list>
            240 => self.pass(c[0]),
            // <match_arm_list_opt> -> <match_arm_list> ,
            241 => self.pass(c[0]),
            // <match_expr> -> match <header_expr> { <match_arm_list_opt> }
            242 => self.at(
                ASTNodeKind::Match { scrutinee: c[1], arms: self.list(c[3]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
