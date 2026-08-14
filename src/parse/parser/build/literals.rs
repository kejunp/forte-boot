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
            129 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::FieldInit { name, value: c[2] }, c[0])
            }
            // <field_init_list> -> <field_init>
            130 => self.one(c[0]),
            // <field_init_list> -> <field_init_list> , <field_init>
            131 => self.grew(c[0], c[2]),
            // <field_init_list_opt> -> ε
            132 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_init_list_opt> -> <field_init_list>
            133 => self.pass(c[0]),
            // <field_init_list_opt> -> <field_init_list> ,
            134 => self.pass(c[0]),

            // ---- Maps ----------------------------------------------------
            // <map_entry> -> <expression> : <expression>
            227 => self.at(ASTNodeKind::MapEntry { key: c[0], value: c[2] }, c[0]),
            // <map_entry_list> -> <map_entry>
            228 => self.one(c[0]),
            // <map_entry_list> -> <map_entry_list> , <map_entry>
            229 => self.grew(c[0], c[2]),
            // <map_entry_list_opt> -> ε
            // `{}` is the empty map, and so is `{:}` below: the one spelling
            // that has to be written out is the empty *set*.
            230 => self.here(ASTNodeKind::List(Vec::new())),
            // <map_entry_list_opt> -> :
            231 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <map_entry_list_opt> -> <map_entry_list>
            232 => self.pass(c[0]),
            // <map_entry_list_opt> -> <map_entry_list> ,
            233 => self.pass(c[0]),
            // <map_literal> -> VALUE_LCURLY <map_entry_list_opt> }
            234 => self.at(
                ASTNodeKind::Map { hashed: false, entries: self.list(c[1]) },
                c[0],
            ),
            // <map_literal> -> # VALUE_LCURLY <map_entry_list_opt> }
            235 => self.at(
                ASTNodeKind::Map { hashed: true, entries: self.list(c[2]) },
                c[0],
            ),

            // ---- Sets ----------------------------------------------------
            // <set_element_list> -> ,
            // `{,}` is the empty set, written out because `{}` is the empty map.
            337 => self.at(ASTNodeKind::List(Vec::new()), c[0]),
            // <set_element_list> -> <expression_seq>
            338 => self.pass(c[0]),
            // <set_element_list> -> <expression_seq> ,
            339 => self.pass(c[0]),
            // <set_literal> -> VALUE_LCURLY <set_element_list> }
            340 => self.at(
                ASTNodeKind::Set { hashed: false, elems: self.list(c[1]) },
                c[0],
            ),
            // <set_literal> -> # VALUE_LCURLY <set_element_list> }
            341 => self.at(
                ASTNodeKind::Set { hashed: true, elems: self.list(c[2]) },
                c[0],
            ),

            _ => return None,
        })
    }
}
