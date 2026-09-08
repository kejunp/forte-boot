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
            // <type> -> <fn_type>
            375 => self.pass(c[0]),
            // <fn_type> -> <fn_uses> fn ( <type_list_opt> ) <return_type_opt>
            // "the shape a `<fn_decl>` has, with the name and the parameter
            // names gone": what a caller hands over is types. What stands in
            // front says what calling it does to what the closure captured.
            152 => {
                let uses = match self.kind(c[0]) {
                    ASTNodeKind::Mark(ASTMark::Uses(uses)) => *uses,
                    _ => ASTFnUses::Reads,
                };
                self.at(
                    ASTNodeKind::FnType { uses, params: self.list(c[3]), ret: self.opt(c[5]) },
                    c[1],
                )
            }
            // <fn_uses> -> ε
            153 => self.here(ASTNodeKind::Empty),
            // <fn_uses> -> var
            154 => self.at(ASTNodeKind::Mark(ASTMark::Uses(ASTFnUses::Writes)), c[0]),
            // <fn_uses> -> once
            155 => self.at(ASTNodeKind::Mark(ASTMark::Uses(ASTFnUses::Takes)), c[0]),
            // <type_list_opt> -> ε
            390 => self.here(ASTNodeKind::List(Vec::new())),
            // <type_list_opt> -> <type_list>
            391 => self.pass(c[0]),
            // <type> -> <ref_type>
            373 => self.pass(c[0]),
            // <type> -> <ptr_type>
            374 => self.pass(c[0]),
            // <type> -> <base_type> <array_suffix_list>
            378 => self.fold_suffixes(c[0], c[1]),
            // <type_annotation_opt> -> ε
            379 => self.here(ASTNodeKind::Empty),
            // <type_annotation_opt> -> : <type>
            380 => self.pass(c[1]),
            // <type_bound> -> <named_type>
            382 => self.pass(c[0]),
            // <type_bound> -> <lifetime>
            383 => self.pass(c[0]),
            // <type_bounds> -> <type_bound>
            384 => self.one(c[0]),
            // <type_bounds> -> <type_bounds> + <type_bound>
            385 => self.grew(c[0], c[2]),
            // <type_list> -> <type>
            388 => self.one(c[0]),
            // <type_list> -> <type_list> , <type>
            389 => self.grew(c[0], c[2]),

            // ---- Primitive types -----------------------------------------
            // The leaf is already a `Prim`, except for `null`, whose token is
            // the literal: the one value of the type spells the type too.
            // <primitive_type> -> i8 .. never
            310 | 311 | 312 | 313 | 314 | 315 | 316 | 317 | 318 | 319 | 320 | 321 | 322 | 323 | 324 | 326 => self.pass(c[0]),
            // <primitive_type> -> null
            325 => self.at(ASTNodeKind::Prim(ASTPrimType::Null), c[0]),

            // ---- References ----------------------------------------------
            // <ref_op> -> &
            340 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Imm)), c[0]),
            // <ref_op> -> *
            341 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Mut)), c[0]),
            // <ref_type> -> <ref_op> <lifetime_opt> <type>
            342 => {
                let op = ref_of(self.mark(c[0]));
                let life = self.opt(c[1]);
                self.at(ASTNodeKind::RefType { op, life, inner: c[2] }, c[0])
            }

            // ---- Pointers ------------------------------------------------
            // No <lifetime_opt> to take: a pointer is the one thing here that
            // says nothing about how long what it addresses is good for.
            // <ptr_type> -> ptr <type>
            327 => self.at(ASTNodeKind::PtrType(c[1]), c[0]),

            // ---- Collected values ----------------------------------------
            // The same word a binding writes, said where a type is wanted.
            // <gc_type> -> gc <type>
            160 => self.at(ASTNodeKind::GcType(c[1]), c[0]),
            // <type> -> <gc_type>
            377 => self.pass(c[0]),

            // ---- Trait objects -------------------------------------------
            // The word and then the trait's name. No <lifetime_opt> either: a
            // `dyn Shape` is not a reference and cannot stand alone, so what
            // says how long it is good for is the `&` in front of it.
            // <dyn_type> -> dyn <named_type>
            102 => self.at(ASTNodeKind::DynType(c[1]), c[0]),
            // <type> -> <dyn_type>
            376 => self.pass(c[0]),

            // ---- Lifetimes -----------------------------------------------
            // The `~` is the lexer's; what reaches here is the name alone.
            // <lifetime> -> LIFETIME
            212 => self.pass(c[0]),
            // <lifetime_opt> -> ε
            213 => self.here(ASTNodeKind::Empty),
            // <lifetime_opt> -> <lifetime>
            214 => self.pass(c[0]),
            // <return_type_opt> -> ε
            343 => self.here(ASTNodeKind::Empty),
            // <return_type_opt> -> : <type>
            344 => self.pass(c[1]),

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
            369 | 370 => self.at(ASTNodeKind::TupleLit(self.members(c[1], c[3])), c[0]),
            // <tuple_pattern> -> ( <pattern> , <pattern_list> )
            371 => self.at(ASTNodeKind::TuplePat(self.members(c[1], c[3])), c[0]),
            // <tuple_type> -> ( <type> , <type_list> )
            372 => self.at(ASTNodeKind::TupleType(self.members(c[1], c[3])), c[0]),

            _ => return None,
        })
    }
}
