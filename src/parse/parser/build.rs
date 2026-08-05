//! What each rule of the grammar makes of the children it just took.
//!
//! One arm per rule and nothing to derive them from: the tables say which rule
//! fired, and what that rule *means* is only written here. The arms are in the
//! tables' own order, each under the production it answers, so that a rule
//! added to docs/grammar.bnf can be found here by the number the generator
//! gave it.
//!
//! Three shapes cover most of it. A rule with one symbol and nothing of its own
//! to say passes its child up (`pass`). A `<..._list>` gathers handles into a
//! `List`, and an `<..._opt>` that was not written reduces to `Empty`, which is
//! what `list` and `opt` read back. Everything else names an `ASTNodeKind` and
//! fills it from the children.
//!
//! What a rule cannot do is reach leftwards: `<postfix_op>` is reduced before
//! the parse says what it is a suffix of, and an `<array_suffix>` before it
//! says what it is a suffix of either. Those are built with `HOLE` where the
//! base goes, and the rule above fills it in -- `with_base` and
//! `fold_suffixes`. It is the one place a node is finished after it is made.

use super::*;
use ast_nodes::{
    ASTAssignOp, ASTBinOp, ASTBinding, ASTLit, ASTMark, ASTNode, ASTNodeKind, ASTPrimType,
    ASTRangeOp, ASTRefOp, ASTUnaryOp, ASTVariableIntro, ASTVisibility,
};

mod marks;
mod nodes;
#[cfg(test)]
mod tests;

use marks::*;

/// Where a base belongs in a node built before its base was known. Handle 0 is
/// the arena's nothing-node, so a hole left unfilled is a node standing on
/// nothing rather than on the wrong thing.
const HOLE: ASTNodeId = 0;

impl Parser {
    /// What a rule builds out of the children it just took.
    pub(super) fn build(&mut self, rule_id: tables::RuleId, children: &[ASTNodeId]) -> ASTNode {
        let c = children;
        match rule_id {
            // ---- The file ------------------------------------------------
            // <start> -> <program>
            0 => self.pass(c[0]),
            // <program> -> <item_list>
            1 => self.at(ASTNodeKind::Program(self.list(c[0])), c[0]),

            // ---- Arithmetic ----------------------------------------------
            // <additive> -> <multiplicative>
            2 => self.pass(c[0]),
            // <additive> -> <additive> <additive_op> <multiplicative>
            3 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <additive_op> -> +
            4 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Add)), c[0]),
            // <additive_op> -> -
            5 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Sub)), c[0]),

            // ---- Call arguments ------------------------------------------
            // <arg_list> -> <expression_seq>
            6 => self.pass(c[0]),
            // <arg_list> -> <expression_seq> ,
            7 => self.pass(c[0]),
            // <arg_list_opt> -> ε
            8 => self.here(ASTNodeKind::List(Vec::new())),
            // <arg_list_opt> -> <arg_list>
            9 => self.pass(c[0]),

            // ---- Array literals ------------------------------------------
            // <array_element_list_opt> -> ε
            10 => self.here(ASTNodeKind::List(Vec::new())),
            // <array_element_list_opt> -> <expression_seq>
            11 => self.pass(c[0]),
            // <array_element_list_opt> -> <expression_seq> ,
            12 => self.pass(c[0]),
            // <array_literal> -> [ <array_element_list_opt> ]
            13 => self.at(ASTNodeKind::ArrayLit(self.list(c[1])), c[0]),

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

            // ---- Assignment ----------------------------------------------
            // <assign_op> -> =
            18 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Set)), c[0]),
            // <assign_op> -> +=
            19 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Add)), c[0]),
            // <assign_op> -> -=
            20 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Sub)), c[0]),
            // <assign_op> -> *=
            21 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Mul)), c[0]),
            // <assign_op> -> /=
            22 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Div)), c[0]),
            // <assign_op> -> &=
            23 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::And)), c[0]),
            // <assign_op> -> |=
            24 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Or)), c[0]),
            // <assign_op> -> ^=
            25 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Xor)), c[0]),
            // <assign_op> -> <<=
            26 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Shl)), c[0]),
            // <assign_op> -> >>=
            27 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Shr)), c[0]),
            // <assignment> -> <range_expr>
            28 => self.pass(c[0]),
            // <assignment> -> <range_expr> <assign_op> <value_expr>
            29 => {
                let op = assign_of(self.mark(c[1]));
                self.at(ASTNodeKind::Assign { op, target: c[0], value: c[2] }, c[0])
            }

            // ---- Attributes ----------------------------------------------
            // <attr_arg> -> <literal>
            30 => self.pass(c[0]),
            // <attr_arg> -> <attr_item>
            31 => self.pass(c[0]),
            // <attr_arg_list> -> <attr_arg>
            32 => self.one(c[0]),
            // <attr_arg_list> -> <attr_arg_list> , <attr_arg>
            33 => self.grew(c[0], c[2]),
            // <attr_arg_list_opt> -> ε
            34 => self.here(ASTNodeKind::List(Vec::new())),
            // <attr_arg_list_opt> -> <attr_arg_list>
            35 => self.pass(c[0]),
            // <attr_item> -> IDENTIFIER
            36 => self.at(ASTNodeKind::Attr { name: self.text(c[0]), args: Vec::new() }, c[0]),
            // <attr_item> -> IDENTIFIER ( <attr_arg_list_opt> )
            37 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::Attr { name, args: self.list(c[2]) }, c[0])
            }
            // <attribute> -> @ <attr_item>
            // The attribute begins at the `@`, which is what a message about a
            // declaration carrying one should point at.
            38 => self.at(self.kind(c[1]).clone(), c[0]),
            // <attribute_list> -> ε
            39 => self.here(ASTNodeKind::List(Vec::new())),
            // <attribute_list> -> <attribute_list> <attribute>
            40 => self.grew(c[0], c[1]),

            // ---- Types ---------------------------------------------------
            // <base_type> -> <primitive_type>
            41 => self.pass(c[0]),
            // <base_type> -> <named_type>
            42 => self.pass(c[0]),
            // <base_type> -> <grouped_type>
            43 => self.pass(c[0]),
            // <base_type> -> <tuple_type>
            44 => self.pass(c[0]),
            // <base_type> -> _
            // The leaf is a pattern's wildcard; in a type the same `_` is a
            // type left to be worked out.
            45 => self.at(ASTNodeKind::Infer, c[0]),

            // ---- Bindings ------------------------------------------------
            // <binding_name> -> IDENTIFIER
            46 => self.pass(c[0]),
            // <binding_name> -> _
            47 => self.pass(c[0]),

            // ---- Bitwise -------------------------------------------------
            // The operator is the rule rather than a mark of its own: there is
            // one spelling apiece, so there is nothing for a `<..._op>` rule to
            // tell the arm that the arm does not already know.
            // <bit_and> -> <shift>
            48 => self.pass(c[0]),
            // <bit_and> -> <bit_and> & <shift>
            49 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitAnd, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <bit_or> -> <bit_xor>
            50 => self.pass(c[0]),
            // <bit_or> -> <bit_or> | <bit_xor>
            51 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitOr, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <bit_xor> -> <bit_and>
            52 => self.pass(c[0]),
            // <bit_xor> -> <bit_xor> ^ <bit_and>
            53 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitXor, lhs: c[0], rhs: c[2] },
                c[0],
            ),

            // ---- Blocks --------------------------------------------------
            // <block> -> { <statement_list> <block_tail_opt> }
            54 => self.at(
                ASTNodeKind::Block { stmts: self.list(c[1]), tail: self.opt(c[2]) },
                c[0],
            ),
            // <block_expr> -> <block> | <if_expr> | <while_expr> | <for_expr>
            //              |  <match_expr>
            55 | 56 | 57 | 58 | 59 => self.pass(c[0]),
            // <block_tail_opt> -> ε
            60 => self.here(ASTNodeKind::Empty),
            // <block_tail_opt> -> <unterminated_stmt>
            61 => self.pass(c[0]),

            // ---- Casts ---------------------------------------------------
            // <cast> -> <unary>
            62 => self.pass(c[0]),
            // <cast> -> <cast> as <cast_type>
            63 => self.at(ASTNodeKind::Cast { value: c[0], ty: c[2] }, c[0]),
            // <cast_base> -> <primitive_type>
            64 => self.pass(c[0]),
            // <cast_base> -> <qualified_name>
            // A name in a cast is a type, and a type names itself with `Named`
            // rather than with the `Name` an expression would have built.
            65 => self.at(ASTNodeKind::Named { path: self.path(c[0]), args: Vec::new() }, c[0]),
            // <cast_base> -> <grouped_type>
            66 => self.pass(c[0]),
            // <cast_base> -> <tuple_type>
            67 => self.pass(c[0]),
            // <cast_base> -> _
            68 => self.at(ASTNodeKind::Infer, c[0]),
            // <cast_type> -> <ref_op> <cast_type>
            69 => {
                let op = ref_of(self.mark(c[0]));
                self.at(ASTNodeKind::RefType { op, inner: c[1] }, c[0])
            }
            // <cast_type> -> <cast_base> <array_suffix_list>
            70 => self.fold_suffixes(c[0], c[1]),

            // ---- Closures ------------------------------------------------
            // <closure_expr> -> <move_opt> | <closure_param_list_opt> | <value_expr>
            71 => {
                let is_move = matches!(self.kind(c[0]), ASTNodeKind::Mark(ASTMark::Move));
                // Where `move` was not written the closure begins at its first
                // `|`, the ε node having nowhere of its own to stand.
                let anchor = if is_move { c[0] } else { c[1] };
                self.at(
                    ASTNodeKind::Closure { is_move, params: self.list(c[2]), body: c[4] },
                    anchor,
                )
            }
            // <closure_param> -> <binding_name> <type_annotation_opt>
            72 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <closure_param_list> -> <closure_param>
            73 => self.one(c[0]),
            // <closure_param_list> -> <closure_param_list> , <closure_param>
            74 => self.grew(c[0], c[2]),
            // <closure_param_list_opt> -> ε
            75 => self.here(ASTNodeKind::List(Vec::new())),
            // <closure_param_list_opt> -> <closure_param_list>
            76 => self.pass(c[0]),

            // ---- Comparison ----------------------------------------------
            // <comparison> -> <bit_or>
            77 => self.pass(c[0]),
            // <comparison> -> <comparison> <comparison_op> <bit_or>
            78 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <comparison_op> -> <
            79 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Lt)), c[0]),
            // <comparison_op> -> >
            80 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Gt)), c[0]),
            // <comparison_op> -> <=
            81 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Le)), c[0]),
            // <comparison_op> -> >=
            82 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Ge)), c[0]),

            // ---- Constants -----------------------------------------------
            // <const_decl> -> <const_head> ;
            83 => self.pass(c[0]),
            // <const_expr> -> <expression>
            84 => self.pass(c[0]),
            // <const_head> -> const IDENTIFIER : <type> = <const_expr>
            85 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Const {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        ty: c[3],
                        value: c[5],
                    },
                    c[0],
                )
            }
            // <const_pattern> -> <qualified_name>
            86 => self.pass(c[0]),

            // ---- Declarations --------------------------------------------
            // <declaration> -> <fn_decl> | <struct_decl> | <enum_decl>
            //               |  <trait_decl> | <impl_decl> | <namespace_decl>
            //               |  <var_decl> | <const_decl>
            87 | 88 | 89 | 90 | 91 | 92 | 93 | 94 => self.pass(c[0]),

            // ---- Enums ---------------------------------------------------
            // <discriminant> -> = <expression>
            95 => self.at(ASTNodeKind::Discriminant(c[1]), c[0]),
            // <elif_list> -> ε
            96 => self.here(ASTNodeKind::List(Vec::new())),
            // <elif_list> -> <elif_list> elif <header_expr> <block>
            // The `elif` becomes a node of its own here: the list holds them,
            // and nothing above this rule sees the three symbols again.
            97 => {
                let elif = self.at(ASTNodeKind::Elif { cond: c[2], block: c[3] }, c[1]);
                let id = self.push_node(elif);
                self.grew(c[0], id)
            }
            // <else_opt> -> ε
            98 => self.here(ASTNodeKind::Empty),
            // <else_opt> -> else <block>
            99 => self.pass(c[1]),
            // <enum_decl> -> enum IDENTIFIER <generic_params_opt> { <enum_variant_list_opt> } <semi_opt>
            100 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Enum {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        generics: self.list(c[2]),
                        variants: self.list(c[4]),
                    },
                    c[0],
                )
            }
            // <enum_variant> -> <attribute_list> IDENTIFIER <variant_tail_opt>
            101 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[1] } else { c[0] };
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::EnumVariant { attrs, name, body: self.opt(c[2]) },
                    anchor,
                )
            }
            // <enum_variant_list> -> <enum_variant>
            102 => self.one(c[0]),
            // <enum_variant_list> -> <enum_variant_list> , <enum_variant>
            103 => self.grew(c[0], c[2]),
            // <enum_variant_list_opt> -> ε
            104 => self.here(ASTNodeKind::List(Vec::new())),
            // <enum_variant_list_opt> -> <enum_variant_list>
            105 => self.pass(c[0]),
            // <enum_variant_list_opt> -> <enum_variant_list> ,
            106 => self.pass(c[0]),

            // ---- Equality ------------------------------------------------
            // <equality> -> <comparison>
            107 => self.pass(c[0]),
            // <equality> -> <equality> <equality_op> <comparison>
            108 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <equality_op> -> ==
            109 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Eq)), c[0]),
            // <equality_op> -> !=
            110 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Ne)), c[0]),

            // ---- Expressions and statements ------------------------------
            // <expr_stmt> -> <expression> ;
            111 => self.at(ASTNodeKind::ExprStmt(c[0]), c[0]),
            // <expression> -> <value_expr> | <jump_expr>
            112 | 113 => self.pass(c[0]),
            // <expression_opt> -> ε
            114 => self.here(ASTNodeKind::Empty),
            // <expression_opt> -> <expression>
            115 => self.pass(c[0]),
            // <expression_seq> -> <expression>
            116 => self.one(c[0]),
            // <expression_seq> -> <expression_seq> , <expression>
            117 => self.grew(c[0], c[2]),

            // ---- Struct fields -------------------------------------------
            // <field_decl> -> <attribute_list> <visibility_opt> IDENTIFIER : <type>
            118 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[2] } else { c[0] };
                let name = self.text(c[2]);
                self.at(
                    ASTNodeKind::FieldDecl { attrs, vis: self.visibility(c[1]), name, ty: c[4] },
                    anchor,
                )
            }
            // <field_decl_list> -> <field_decl>
            119 => self.one(c[0]),
            // <field_decl_list> -> <field_decl_list> , <field_decl>
            120 => self.grew(c[0], c[2]),
            // <field_decl_list_opt> -> ε
            121 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_decl_list_opt> -> <field_decl_list>
            122 => self.pass(c[0]),
            // <field_decl_list_opt> -> <field_decl_list> ,
            123 => self.pass(c[0]),

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

            // ---- Functions -----------------------------------------------
            // <fn_body> -> <block> <semi_opt>
            137 => self.pass(c[0]),
            // <fn_body> -> ;
            // A signature and no body, which `Fn::body` spells `None`.
            138 => self.at(ASTNodeKind::Empty, c[0]),
            // <fn_decl> -> <fn_sig> <fn_body>
            139 => {
                let mut node = self.pass(c[0]);
                match &mut node.kind {
                    ASTNodeKind::Fn { body, .. } => *body = self.opt(c[1]),
                    other => panic!("a body was written on {:?}", other),
                }
                node
            }
            // <fn_head> -> fn IDENTIFIER <generic_params_opt> ( <param_list_opt> ) <return_type_opt> <where_clause_opt>
            140 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Fn {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        is_const: false,
                        is_unsafe: false,
                        name,
                        generics: self.list(c[2]),
                        params: self.list(c[4]),
                        ret: self.opt(c[6]),
                        wheres: self.list(c[7]),
                        body: None,
                    },
                    c[0],
                )
            }
            // <fn_sig> -> <fn_head>
            141 => self.pass(c[0]),
            // <fn_sig> -> const <fn_head>
            142 => self.with_modifier(c[1], c[0], true, false),
            // <fn_sig> -> unsafe <fn_head>
            143 => self.with_modifier(c[1], c[0], false, true),
            // <fn_sig> -> const unsafe <fn_head>
            144 => self.with_modifier(c[2], c[0], true, true),

            // ---- Loops ---------------------------------------------------
            // <for_expr> -> for <binding_name> in <header_expr> <block>
            145 => self.at(
                ASTNodeKind::For { name: self.binding(c[1]), iter: c[3], body: c[4] },
                c[0],
            ),

            // ---- Generics ------------------------------------------------
            // <generic_args> -> < <type_list> >
            146 => self.pass(c[1]),
            // <generic_args_opt> -> ε
            147 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_args_opt> -> <generic_args>
            148 => self.pass(c[0]),
            // <generic_param> -> IDENTIFIER
            149 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> IDENTIFIER : <type_bounds>
            150 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // <generic_param_list> -> <generic_param>
            151 => self.one(c[0]),
            // <generic_param_list> -> <generic_param_list> , <generic_param>
            152 => self.grew(c[0], c[2]),
            // <generic_params> -> < <generic_param_list> >
            153 => self.pass(c[1]),
            // <generic_params_opt> -> ε
            154 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_params_opt> -> <generic_params>
            155 => self.pass(c[0]),

            // ---- Grouping ------------------------------------------------
            // Parentheses are gone from the tree: what they said about
            // precedence the shape now says.
            // <grouped_type> -> ( <type> )
            156 => self.pass(c[1]),
            // <grouping> -> ( <expression> )
            157 => self.pass(c[1]),

            // ---- Conditionals --------------------------------------------
            // <header_expr> -> <assignment>
            158 => self.pass(c[0]),
            // <if_expr> -> if <header_expr> <block> <elif_list> <else_opt>
            159 => self.at(
                ASTNodeKind::If {
                    cond: c[1],
                    then: c[2],
                    elifs: self.list(c[3]),
                    else_block: self.opt(c[4]),
                },
                c[0],
            ),

            // ---- Impls ---------------------------------------------------
            // <impl_decl> -> impl <generic_params_opt> <type> <impl_for_opt> <where_clause_opt> { <impl_member_list> <impl_tail_opt> } <semi_opt>
            160 => self.at(
                ASTNodeKind::Impl {
                    attrs: Vec::new(),
                    vis: ASTVisibility::Unwritten,
                    generics: self.list(c[1]),
                    ty: c[2],
                    for_ty: self.opt(c[3]),
                    wheres: self.list(c[4]),
                    members: self.with_tail(c[6], c[7]),
                },
                c[0],
            ),
            // <impl_for_opt> -> ε
            161 => self.here(ASTNodeKind::Empty),
            // <impl_for_opt> -> for <type>
            162 => self.pass(c[1]),
            // <impl_member> -> <attribute_list> <visibility_opt> <fn_decl>
            163 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <impl_member_list> -> ε
            164 => self.here(ASTNodeKind::List(Vec::new())),
            // <impl_member_list> -> <impl_member_list> <impl_member>
            165 => self.grew(c[0], c[1]),
            // <impl_tail_opt> -> ε
            166 => self.here(ASTNodeKind::Empty),
            // <impl_tail_opt> -> <attribute_list> <visibility_opt> <fn_sig>
            167 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Imports -------------------------------------------------
            // <import_alias_opt> -> ε
            168 => self.here(ASTNodeKind::Empty),
            // <import_alias_opt> -> as IDENTIFIER
            169 => self.pass(c[1]),
            // <import_decl> -> <import_head> ;
            170 => self.pass(c[0]),
            // <import_head> -> import <import_path> <import_alias_opt>
            171 => {
                let alias = self.opt(c[2]).map(|id| self.text(id));
                self.at(ASTNodeKind::Import { path: self.path(c[1]), alias }, c[0])
            }
            // <import_path> -> IDENTIFIER
            172 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <import_path> -> <import_path> :: IDENTIFIER
            173 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }

            // ---- Indexing and initializers -------------------------------
            // <index> -> <expression>
            174 => self.pass(c[0]),
            // <initializer_opt> -> ε
            175 => self.here(ASTNodeKind::Empty),
            // <initializer_opt> -> = <expression>
            176 => self.pass(c[1]),

            // ---- Items ---------------------------------------------------
            // <item> -> <import_decl>
            177 => self.pass(c[0]),
            // <item> -> <attribute_list> <visibility_opt> <declaration>
            178 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <item_list> -> ε
            179 => self.here(ASTNodeKind::List(Vec::new())),
            // <item_list> -> <item_list> <item>
            180 => self.grew(c[0], c[1]),
            // <item_tail_opt> -> ε
            181 => self.here(ASTNodeKind::Empty),
            // <item_tail_opt> -> <import_head>
            182 => self.pass(c[0]),
            // <item_tail_opt> -> <attribute_list> <visibility_opt> <unterminated_decl>
            183 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Jumps ---------------------------------------------------
            // <jump_expr> -> return <expression_opt>
            184 => self.at(ASTNodeKind::Return(self.opt(c[1])), c[0]),
            // <jump_expr> -> break <expression_opt>
            185 => self.at(ASTNodeKind::Break(self.opt(c[1])), c[0]),
            // <jump_expr> -> continue
            186 => self.at(ASTNodeKind::Continue, c[0]),

            // ---- Literals ------------------------------------------------
            // The leaf a shift built already holds the value: <literal> only
            // says that one may stand where an expression may.
            // <literal> -> INT_LITERAL | FLOAT_LITERAL | STRING_LITERAL
            //           |  CHAR_LITERAL | true | false | null
            187 | 188 | 189 | 190 | 191 | 192 | 193 => self.pass(c[0]),
            // <literal_pattern> -> <literal>
            194 => self.at(ASTNodeKind::LitPat { negated: false, value: self.lit(c[0]) }, c[0]),
            // <literal_pattern> -> - <literal>
            195 => self.at(ASTNodeKind::LitPat { negated: true, value: self.lit(c[1]) }, c[0]),

            // ---- Logic ---------------------------------------------------
            // <logical_and> -> <equality>
            196 => self.pass(c[0]),
            // <logical_and> -> <logical_and> && <equality>
            197 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::And, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <logical_or> -> <logical_xor>
            198 => self.pass(c[0]),
            // <logical_or> -> <logical_or> || <logical_xor>
            199 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::Or, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <logical_xor> -> <logical_and>
            200 => self.pass(c[0]),
            // <logical_xor> -> <logical_xor> ^^ <logical_and>
            201 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::Xor, lhs: c[0], rhs: c[2] },
                c[0],
            ),

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

            // ---- Closures, continued -------------------------------------
            // <move_opt> -> ε
            218 => self.here(ASTNodeKind::Empty),
            // <move_opt> -> move
            219 => self.at(ASTNodeKind::Mark(ASTMark::Move), c[0]),

            // ---- Multiplication ------------------------------------------
            // <multiplicative> -> <cast>
            220 => self.pass(c[0]),
            // <multiplicative> -> <multiplicative> <multiplicative_op> <cast>
            221 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <multiplicative_op> -> *
            222 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Mul)), c[0]),
            // <multiplicative_op> -> /
            223 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Div)), c[0]),
            // <multiplicative_op> -> %
            224 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Rem)), c[0]),

            // ---- Named payloads and named types --------------------------
            // <named_payload> -> VALUE_LCURLY <field_decl_list_opt> }
            225 => self.at(ASTNodeKind::NamedPayload(self.list(c[1])), c[0]),
            // <named_type> -> <qualified_name> <generic_args_opt>
            226 => self.at(
                ASTNodeKind::Named { path: self.path(c[0]), args: self.list(c[1]) },
                c[0],
            ),

            // ---- Namespaces ----------------------------------------------
            // <namespace_decl> -> namespace IDENTIFIER { <item_list> <item_tail_opt> } <semi_opt>
            227 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Namespace {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        items: self.with_tail(c[3], c[4]),
                    },
                    c[0],
                )
            }

            // ---- Parameters ----------------------------------------------
            // <param> -> <param_name> <type_annotation_opt>
            228 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <param_list> -> <param_seq>
            229 => self.pass(c[0]),
            // <param_list> -> <param_seq> ,
            230 => self.pass(c[0]),
            // <param_list_opt> -> ε
            231 => self.here(ASTNodeKind::List(Vec::new())),
            // <param_list_opt> -> <param_list>
            232 => self.pass(c[0]),
            // <param_name> -> this
            233 => self.pass(c[0]),
            // <param_name> -> <binding_name>
            234 => self.pass(c[0]),
            // <param_seq> -> <param>
            235 => self.one(c[0]),
            // <param_seq> -> <param_seq> , <param>
            236 => self.grew(c[0], c[2]),

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

            // ---- Postfix -------------------------------------------------
            // Each suffix was built around a HOLE; this is where it is given
            // the expression it was written after.
            // <postfix> -> <primary>
            250 => self.pass(c[0]),
            // <postfix> -> <postfix> <postfix_op>
            251 => self.with_base(c[1], c[0]),
            // <postfix_op> -> . IDENTIFIER
            252 => {
                let name = self.text(c[1]);
                self.at(ASTNodeKind::Field { base: HOLE, name }, c[0])
            }
            // <postfix_op> -> . INT_LITERAL
            // The same `.`, reaching into a tuple: a member there is counted
            // and not named, so what follows the dot is the number.
            253 => self.at(
                ASTNodeKind::TupleIndex { base: HOLE, index: self.index(c[1]) },
                c[0],
            ),
            // <postfix_op> -> :: IDENTIFIER
            254 => {
                let name = self.text(c[1]);
                self.at(ASTNodeKind::Path { base: HOLE, name }, c[0])
            }
            // <postfix_op> -> ( <arg_list_opt> )
            255 => self.at(
                ASTNodeKind::Call { callee: HOLE, args: self.list(c[1]) },
                c[0],
            ),
            // <postfix_op> -> [ <index> ]
            256 => self.at(ASTNodeKind::Index { base: HOLE, index: c[1] }, c[0]),
            // <postfix_op> -> <struct_literal_tail>
            257 => self.pass(c[0]),

            // ---- Primaries -----------------------------------------------
            // <primary> -> <literal> | this | IDENTIFIER | <array_literal>
            //           |  <map_literal> | <set_literal> | <grouping>
            //           |  <tuple_expr>
            258 | 259 | 260 | 261 | 262 | 263 | 264 | 265 => self.pass(c[0]),

            // ---- Primitive types -----------------------------------------
            // The leaf is already a `Prim`, except for `null`, whose token is
            // the literal: the one value of the type spells the type too.
            // <primitive_type> -> i8 .. never
            266..=278 | 280 => self.pass(c[0]),
            // <primitive_type> -> null
            279 => self.at(ASTNodeKind::Prim(ASTPrimType::Null), c[0]),

            // ---- Names ---------------------------------------------------
            // <qualified_name> -> IDENTIFIER
            281 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <qualified_name> -> <qualified_name> :: IDENTIFIER
            282 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }

            // ---- Ranges --------------------------------------------------
            // Either end may be missing, and the four rules below are the four
            // ways to write that.
            // <range_expr> -> <logical_or>
            283 => self.pass(c[0]),
            // <range_expr> -> <logical_or> <range_op>
            284 => {
                let op = range_of(self.mark(c[1]));
                self.at(ASTNodeKind::Range { op, start: Some(c[0]), end: None }, c[0])
            }
            // <range_expr> -> <logical_or> <range_op> <logical_or>
            285 => {
                let op = range_of(self.mark(c[1]));
                self.at(
                    ASTNodeKind::Range { op, start: Some(c[0]), end: Some(c[2]) },
                    c[0],
                )
            }
            // <range_expr> -> <range_op>
            286 => {
                let op = range_of(self.mark(c[0]));
                self.at(ASTNodeKind::Range { op, start: None, end: None }, c[0])
            }
            // <range_expr> -> <range_op> <logical_or>
            287 => {
                let op = range_of(self.mark(c[0]));
                self.at(ASTNodeKind::Range { op, start: None, end: Some(c[1]) }, c[0])
            }
            // <range_op> -> ..
            288 => self.at(ASTNodeKind::Mark(ASTMark::Range(ASTRangeOp::Exclusive)), c[0]),
            // <range_op> -> ..=
            289 => self.at(ASTNodeKind::Mark(ASTMark::Range(ASTRangeOp::Inclusive)), c[0]),
            // <range_pattern> -> <literal_pattern> <range_op> <literal_pattern>
            290 => {
                let op = range_of(self.mark(c[1]));
                self.at(ASTNodeKind::RangePat { op, lo: c[0], hi: c[2] }, c[0])
            }

            // ---- References ----------------------------------------------
            // <ref_op> -> &
            291 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Imm)), c[0]),
            // <ref_op> -> *
            292 => self.at(ASTNodeKind::Mark(ASTMark::Ref(ASTRefOp::Mut)), c[0]),
            // <ref_type> -> <ref_op> <type>
            293 => {
                let op = ref_of(self.mark(c[0]));
                self.at(ASTNodeKind::RefType { op, inner: c[1] }, c[0])
            }
            // <return_type_opt> -> ε
            294 => self.here(ASTNodeKind::Empty),
            // <return_type_opt> -> : <type>
            295 => self.pass(c[1]),

            // ---- The optional semicolon ----------------------------------
            // Nothing above reads it: it is written for the grammar, which has
            // to say that it may be there.
            // <semi_opt> -> ε
            296 => self.here(ASTNodeKind::Empty),
            // <semi_opt> -> ;
            297 => self.at(ASTNodeKind::Empty, c[0]),

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

            // ---- Shifts --------------------------------------------------
            // <shift> -> <additive>
            303 => self.pass(c[0]),
            // <shift> -> <shift> <shift_op> <additive>
            304 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <shift_op> -> <<
            305 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Shl)), c[0]),
            // <shift_op> -> >>
            306 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Shr)), c[0]),

            // ---- Statements ----------------------------------------------
            // <statement> -> <declaration> | <unsafe_stmt> | <expr_stmt>
            307 | 308 | 309 => self.pass(c[0]),
            // <statement_list> -> ε
            310 => self.here(ASTNodeKind::List(Vec::new())),
            // <statement_list> -> <statement_list> <statement>
            311 => self.grew(c[0], c[1]),

            // ---- Structs -------------------------------------------------
            // <struct_decl> -> struct IDENTIFIER <generic_params_opt> { <field_decl_list_opt> } <semi_opt>
            312 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Struct {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        generics: self.list(c[2]),
                        fields: self.list(c[4]),
                    },
                    c[0],
                )
            }
            // <struct_literal_tail> -> VALUE_LCURLY <field_init_list_opt> }
            // A suffix like any other: what it is a literal *of* stands to its
            // left and is not on the stack yet.
            313 => self.at(
                ASTNodeKind::StructLit { base: HOLE, fields: self.list(c[1]) },
                c[0],
            ),

            // ---- Traits --------------------------------------------------
            // <trait_decl> -> trait IDENTIFIER <generic_params_opt> { <trait_member_list> <trait_tail_opt> } <semi_opt>
            314 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::Trait {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        generics: self.list(c[2]),
                        members: self.with_tail(c[4], c[5]),
                    },
                    c[0],
                )
            }
            // <trait_member> -> <attribute_list> <fn_decl>
            // A trait's members carry no visibility of their own: the trait's
            // is theirs.
            315 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),
            // <trait_member_list> -> ε
            316 => self.here(ASTNodeKind::List(Vec::new())),
            // <trait_member_list> -> <trait_member_list> <trait_member>
            317 => self.grew(c[0], c[1]),
            // <trait_tail_opt> -> ε
            318 => self.here(ASTNodeKind::Empty),
            // <trait_tail_opt> -> <attribute_list> <fn_sig>
            319 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),

            // ---- Tuples --------------------------------------------------
            // The three of them are one shape: a member, a comma, and the
            // rest. The comma is what says a tuple was written rather than a
            // parenthesis around one thing, so it is in the rule rather than
            // in a list that could be of one.
            // <tuple_expr> -> ( <expression> , <expression_seq> )
            // <tuple_expr> -> ( <expression> , <expression_seq> , )
            320 | 321 => self.at(ASTNodeKind::TupleLit(self.members(c[1], c[3])), c[0]),
            // <tuple_pattern> -> ( <pattern> , <pattern_list> )
            322 => self.at(ASTNodeKind::TuplePat(self.members(c[1], c[3])), c[0]),
            // <tuple_type> -> ( <type> , <type_list> )
            323 => self.at(ASTNodeKind::TupleType(self.members(c[1], c[3])), c[0]),

            // ---- Types, continued ----------------------------------------
            // <type> -> <ref_type>
            324 => self.pass(c[0]),
            // <type> -> <base_type> <array_suffix_list>
            325 => self.fold_suffixes(c[0], c[1]),
            // <type_annotation_opt> -> ε
            326 => self.here(ASTNodeKind::Empty),
            // <type_annotation_opt> -> : <type>
            327 => self.pass(c[1]),
            // <type_bounds> -> <named_type>
            328 => self.one(c[0]),
            // <type_bounds> -> <type_bounds> + <named_type>
            329 => self.grew(c[0], c[2]),
            // <type_list> -> <type>
            330 => self.one(c[0]),
            // <type_list> -> <type_list> , <type>
            331 => self.grew(c[0], c[2]),

            // ---- Unary ---------------------------------------------------
            // <unary> -> <unary_op> <unary>
            332 => {
                let op = unary_of(self.mark(c[0]));
                self.at(ASTNodeKind::Unary { op, operand: c[1] }, c[0])
            }
            // <unary> -> <postfix>
            333 => self.pass(c[0]),
            // <unary_op> -> !
            334 => self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Not)), c[0]),
            // <unary_op> -> -
            335 => self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Neg)), c[0]),
            // <unary_op> -> <ref_op>
            // `&x` and `*x` take a reference; neither dereferences, so the
            // same two spellings mean here what they mean in a type.
            336 => {
                let op = ref_of(self.mark(c[0]));
                self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Ref(op))), c[0])
            }

            // ---- unsafe --------------------------------------------------
            // <unsafe_stmt> -> unsafe <expr_stmt>
            337 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),
            // <unsafe_stmt> -> unsafe <var_decl>
            338 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            // ---- What a `;` may be left off ------------------------------
            // <unterminated_decl> -> <var_head> | <const_head> | <fn_sig>
            339 | 340 | 341 => self.pass(c[0]),
            // <unterminated_stmt> -> <expression> | <var_head> | <const_head>
            342 | 343 | 344 => self.pass(c[0]),
            // <unterminated_stmt> -> unsafe <unterminated_stmt>
            345 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            // ---- Values --------------------------------------------------
            // <value_expr> -> <assignment> | <closure_expr> | <block_expr>
            346 | 347 | 348 => self.pass(c[0]),

            // ---- Variables -----------------------------------------------
            // <var_decl> -> <var_head> ;
            349 => self.pass(c[0]),
            // <var_head> -> <var_intro> <binding_name> <type_annotation_opt> <initializer_opt>
            350 => {
                let intro = intro_of(self.mark(c[0]));
                self.at(
                    ASTNodeKind::Variable {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        intro,
                        name: self.binding(c[1]),
                        ty: self.opt(c[2]),
                        init: self.opt(c[3]),
                    },
                    c[0],
                )
            }
            // <var_intro> -> let
            351 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Let)), c[0]),
            // <var_intro> -> var
            352 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Var)), c[0]),

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

            // ---- ASTVisibility ----------------------------------------------
            // <visibility> -> public
            359 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Public)), c[0]),
            // <visibility> -> private
            360 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Private)), c[0]),
            // <visibility_opt> -> ε
            361 => self.here(ASTNodeKind::Empty),
            // <visibility_opt> -> <visibility>
            362 => self.pass(c[0]),

            // ---- where ---------------------------------------------------
            // <where_clause_opt> -> ε
            363 => self.here(ASTNodeKind::List(Vec::new())),
            // <where_clause_opt> -> where <where_pred_list>
            364 => self.pass(c[1]),
            // <where_pred> -> <type> : <type_bounds>
            365 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred_list> -> <where_pred>
            366 => self.one(c[0]),
            // <where_pred_list> -> <where_pred_list> , <where_pred>
            367 => self.grew(c[0], c[2]),

            // ---- Loops, continued ----------------------------------------
            // <while_expr> -> while <header_expr> <block>
            368 => self.at(ASTNodeKind::While { cond: c[1], body: c[2] }, c[0]),

            // The tables and these arms are generated from and written against
            // the same grammar, so a rule with no arm is the two having come
            // apart -- not a source being wrong.
            other => panic!("rule {} has no arm in `build`", other),
        }
    }
}
