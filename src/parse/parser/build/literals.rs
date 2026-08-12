// The collection literals: arrays, structs, maps and sets.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_literals(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Array literals ------------------------------------------
            // <array_element_list_opt> -> ε
            10 => self.here(ASTNodeKind::List(Vec::new())),
            // <array_element_list_opt> -> <expression_seq>
            11 => self.pass(c[0]),
            // <array_element_list_opt> -> <expression_seq> ,
            12 => self.pass(c[0]),
            // <array_literal> -> [ <array_element_list_opt> ]
            13 => self.at(ASTNodeKind::ArrayLit(self.list(c[1])), c[0]),

            // ---- Struct literals -----------------------------------------
            // <field_init> -> IDENTIFIER : <expression>
            127 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldInit { name, value: c[2] }, c[0])
            }
            // <field_init_list> -> <field_init>
            128 => self.one(c[0]),
            // <field_init_list> -> <field_init_list> , <field_init>
            129 => self.grew(c[0], c[2]),
            // <field_init_list_opt> -> ε
            130 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_init_list_opt> -> <field_init_list>
            131 => self.pass(c[0]),
            // <field_init_list_opt> -> <field_init_list> ,
            132 => self.pass(c[0]),

            // ---- Maps ----------------------------------------------------
            // <map_entry> -> <expression> : <expression>
            221 => self.at(ASTNodeKind::MapEntry { key: c[0], value: c[2] }, c[0]),
            // <map_entry_list> -> <map_entry>
            222 => self.one(c[0]),
            // <map_entry_list> -> <map_entry_list> , <map_entry>
            223 => self.grew(c[0], c[2]),
            // <map_entry_list_opt> -> ε
            // `{}` is the empty map, and so is `{:}` below: the one spelling
            // that has to be written out is the empty *set*.
            224 => self.here(ASTNodeKind::List(Vec::new())),
            // <map_entry_list_opt> -> :
            225 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <map_entry_list_opt> -> <map_entry_list>
            226 => self.pass(c[0]),
            // <map_entry_list_opt> -> <map_entry_list> ,
            227 => self.pass(c[0]),
            // <map_literal> -> VALUE_LCURLY <map_entry_list_opt> }
            228 => self.at(
                ASTNodeKind::Map { hashed: false, entries: self.list(c[1]) },
                c[0],
            ),
            // <map_literal> -> # VALUE_LCURLY <map_entry_list_opt> }
            229 => self.at(
                ASTNodeKind::Map { hashed: true, entries: self.list(c[2]) },
                c[0],
            ),

            // ---- Sets ----------------------------------------------------
            // <set_element_list> -> ,
            // `{,}` is the empty set, written out because `{}` is the empty map.
            323 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <set_element_list> -> <expression_seq>
            324 => self.pass(c[0]),
            // <set_element_list> -> <expression_seq> ,
            325 => self.pass(c[0]),
            // <set_literal> -> VALUE_LCURLY <set_element_list> }
            326 => self.at(
                ASTNodeKind::Set { hashed: false, elems: self.list(c[1]) },
                c[0],
            ),
            // <set_literal> -> # VALUE_LCURLY <set_element_list> }
            327 => self.at(
                ASTNodeKind::Set { hashed: true, elems: self.list(c[2]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
