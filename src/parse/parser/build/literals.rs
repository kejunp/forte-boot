//! The collection literals: arrays, structs, maps and sets.
//!
//! One arm per rule of the grammar, in the tables' own order within each
//! group, each under the production it answers. `None` where the rule belongs
//! to another of these -- `build` tries each in turn. See build.rs.

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
            124 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldInit { name, value: c[2] }, c[0])
            }
            // <field_init_list> -> <field_init>
            125 => self.one(c[0]),
            // <field_init_list> -> <field_init_list> , <field_init>
            126 => self.grew(c[0], c[2]),
            // <field_init_list_opt> -> ε
            127 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_init_list_opt> -> <field_init_list>
            128 => self.pass(c[0]),
            // <field_init_list_opt> -> <field_init_list> ,
            129 => self.pass(c[0]),

            // ---- Maps ----------------------------------------------------
            // <map_entry> -> <expression> : <expression>
            202 => self.at(ASTNodeKind::MapEntry { key: c[0], value: c[2] }, c[0]),
            // <map_entry_list> -> <map_entry>
            203 => self.one(c[0]),
            // <map_entry_list> -> <map_entry_list> , <map_entry>
            204 => self.grew(c[0], c[2]),
            // <map_entry_list_opt> -> ε
            // `{}` is the empty map, and so is `{:}` below: the one spelling
            // that has to be written out is the empty *set*.
            205 => self.here(ASTNodeKind::List(Vec::new())),
            // <map_entry_list_opt> -> :
            206 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <map_entry_list_opt> -> <map_entry_list>
            207 => self.pass(c[0]),
            // <map_entry_list_opt> -> <map_entry_list> ,
            208 => self.pass(c[0]),
            // <map_literal> -> VALUE_LCURLY <map_entry_list_opt> }
            209 => self.at(
                ASTNodeKind::Map { hashed: false, entries: self.list(c[1]) },
                c[0],
            ),
            // <map_literal> -> # VALUE_LCURLY <map_entry_list_opt> }
            210 => self.at(
                ASTNodeKind::Map { hashed: true, entries: self.list(c[2]) },
                c[0],
            ),

            // ---- Sets ----------------------------------------------------
            // <set_element_list> -> ,
            // `{,}` is the empty set, written out because `{}` is the empty map.
            298 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <set_element_list> -> <expression_seq>
            299 => self.pass(c[0]),
            // <set_element_list> -> <expression_seq> ,
            300 => self.pass(c[0]),
            // <set_literal> -> VALUE_LCURLY <set_element_list> }
            301 => self.at(
                ASTNodeKind::Set { hashed: false, elems: self.list(c[1]) },
                c[0],
            ),
            // <set_literal> -> # VALUE_LCURLY <set_element_list> }
            302 => self.at(
                ASTNodeKind::Set { hashed: true, elems: self.list(c[2]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
