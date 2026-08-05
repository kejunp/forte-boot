//! Declarations and the pieces they are made of.
//!
//! One arm per rule of the grammar, in the tables' own order within each
//! group, each under the production it answers. `None` where the rule belongs
//! to another of these -- `build` tries each in turn. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_items(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- The file ------------------------------------------------
            // <start> -> <program>
            0 => self.pass(c[0]),
            // <program> -> <item_list>
            1 => self.at(ASTNodeKind::Program(self.list(c[0])), c[0]),

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

            // ---- Declarations --------------------------------------------
            // <declaration> -> <fn_decl> | <struct_decl> | <enum_decl>
            //               |  <trait_decl> | <impl_decl> | <namespace_decl>
            //               |  <var_decl> | <const_decl>
            87 | 88 | 89 | 90 | 91 | 92 | 93 | 94 => self.pass(c[0]),

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

            // ---- ASTVisibility ----------------------------------------------
            // <visibility> -> public
            359 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Public)), c[0]),
            // <visibility> -> private
            360 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Private)), c[0]),
            // <visibility_opt> -> ε
            361 => self.here(ASTNodeKind::Empty),
            // <visibility_opt> -> <visibility>
            362 => self.pass(c[0]),

            // ---- Bindings ------------------------------------------------
            // <binding_name> -> IDENTIFIER
            46 => self.pass(c[0]),
            // <binding_name> -> _
            47 => self.pass(c[0]),

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

            // ---- Named payloads and named types --------------------------
            // <named_payload> -> VALUE_LCURLY <field_decl_list_opt> }
            225 => self.at(ASTNodeKind::NamedPayload(self.list(c[1])), c[0]),
            // <named_type> -> <qualified_name> <generic_args_opt>
            226 => self.at(
                ASTNodeKind::Named { path: self.path(c[0]), args: self.list(c[1]) },
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

            // ---- The optional semicolon ----------------------------------
            // Nothing above reads it: it is written for the grammar, which has
            // to say that it may be there.
            // <semi_opt> -> ε
            296 => self.here(ASTNodeKind::Empty),
            // <semi_opt> -> ;
            297 => self.at(ASTNodeKind::Empty, c[0]),

            // ---- What a `;` may be left off ------------------------------
            // <unterminated_decl> -> <var_head> | <const_head> | <fn_sig>
            339 | 340 | 341 => self.pass(c[0]),
            // <unterminated_stmt> -> <expression> | <var_head> | <const_head>
            342 | 343 | 344 => self.pass(c[0]),
            // <unterminated_stmt> -> unsafe <unterminated_stmt>
            345 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            _ => return None,
        })
    }
}
