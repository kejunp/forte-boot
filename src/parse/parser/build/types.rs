// Types, which are their own small language.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_types(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Types ---------------------------------------------------
            // <base_type> -> <primitive_type>
            42 => self.pass(c[0]),
            // <base_type> -> <named_type>
            43 => self.pass(c[0]),
            // <base_type> -> <grouped_type>
            44 => self.pass(c[0]),
            // <base_type> -> <tuple_type>
            45 => self.pass(c[0]),
            // <base_type> -> MACRO_PARAM
            46 => self.pass(c[0]),
            // <base_type> -> _
            // The leaf is a pattern's wildcard; in a type the same `_` is a
            // type left to be worked out.
            47 => self.at(ASTNodeKind::Infer, c[0]),

            // ---- Types, continued ----------------------------------------
            // <type> -> <ref_type>
            367 => self.pass(c[0]),
            // <type> -> <ptr_type>
            368 => self.pass(c[0]),
            // <type> -> <base_type> <array_suffix_list>
            369 => self.fold_suffixes(c[0], c[1]),
            // <type_annotation_opt> -> ε
            370 => self.here(ASTNodeKind::Empty),
            // <type_annotation_opt> -> : <type>
            371 => self.pass(c[1]),
            // <type_bound> -> <named_type>
            373 => self.pass(c[0]),
            // <type_bound> -> <lifetime>
            374 => self.pass(c[0]),
            // <type_bounds> -> <type_bound>
            375 => self.one(c[0]),
            // <type_bounds> -> <type_bounds> + <type_bound>
            376 => self.grew(c[0], c[2]),
            // <type_list> -> <type>
            379 => self.one(c[0]),
            // <type_list> -> <type_list> , <type>
            380 => self.grew(c[0], c[2]),

            // ---- Primitive types -----------------------------------------
            // The leaf is already a `Prim`, except for `null`, whose token is
            // the literal: the one value of the type spells the type too.
            // <primitive_type> -> i8 .. never
            303..=317 | 319 => self.pass(c[0]),
            // <primitive_type> -> null
            318 => self.at(ASTNodeKind::Prim(ASTPrimType::Null), c[0]),

            // ---- References ----------------------------------------------
            // <ref_op> -> &
            334 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Imm)), c[0]),
            // <ref_op> -> *
            335 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Mut)), c[0]),
            // <ref_type> -> <ref_op> <lifetime_opt> <type>
            336 => {
                let op = ref_of(self.mark(c[0]));
                let life = self.opt(c[1]);
                self.at(ASTNodeKind::RefType { op, life, inner: c[2] }, c[0])
            }

            // ---- Pointers ------------------------------------------------
            // No <lifetime_opt> to take: a pointer is the one thing here that
            // says nothing about how long what it addresses is good for.
            // <ptr_type> -> ptr <type>
            320 => self.at(ASTNodeKind::PtrType(c[1]), c[0]),

            // ---- Lifetimes -----------------------------------------------
            // The `~` is the lexer's; what reaches here is the name alone.
            // <lifetime> -> LIFETIME
            205 => self.pass(c[0]),
            // <lifetime_opt> -> ε
            206 => self.here(ASTNodeKind::Empty),
            // <lifetime_opt> -> <lifetime>
            207 => self.pass(c[0]),
            // <return_type_opt> -> ε
            337 => self.here(ASTNodeKind::Empty),
            // <return_type_opt> -> : <type>
            338 => self.pass(c[1]),

            // ---- Array and run suffixes ----------------------------------
            // Both are built around a HOLE: what they are a suffix of is not
            // on the stack yet. <type> and <cast_type> fill it in.
            // <array_suffix> -> [ ]
            14 => self.at(ASTNodeKind::Run(HOLE), c[0]),
            // <array_suffix> -> [ <const_expr> ]
            15 => self.at(ASTNodeKind::Array { elem: HOLE, len: c[1] }, c[0]),
            // <array_suffix_list> -> ε
            16 => self.here(ASTNodeKind::List(Vec::new())),
            // <array_suffix_list> -> <array_suffix_list> <array_suffix>
            17 => self.grew(c[0], c[1]),

            // ---- Tuples --------------------------------------------------
            // The three of them are one shape: a member, a comma, and the
            // rest. The comma is what says a tuple was written rather than a
            // parenthesis around one thing, so it is in the rule rather than
            // in a list that could be of one.
            // <tuple_expr> -> ( <expression> , <expression_seq> )
            // <tuple_expr> -> ( <expression> , <expression_seq> , )
            363 | 364 => self.at(ASTNodeKind::TupleLit(self.members(c[1], c[3])), c[0]),
            // <tuple_pattern> -> ( <pattern> , <pattern_list> )
            365 => self.at(ASTNodeKind::TuplePat(self.members(c[1], c[3])), c[0]),
            // <tuple_type> -> ( <type> , <type_list> )
            366 => self.at(ASTNodeKind::TupleType(self.members(c[1], c[3])), c[0]),

            _ => return None,
        })
    }
}
