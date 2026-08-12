// Declarations and the pieces they are made of.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

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
            186 => self.pass(c[0]),
            // <item> -> <attribute_list> <visibility_opt> <declaration>
            187 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <item_list> -> ε
            188 => self.here(ASTNodeKind::List(Vec::new())),
            // <item_list> -> <item_list> <item>
            189 => self.grew(c[0], c[1]),
            // <item_tail_opt> -> ε
            190 => self.here(ASTNodeKind::Empty),
            // <item_tail_opt> -> <import_head>
            191 => self.pass(c[0]),
            // <item_tail_opt> -> <attribute_list> <visibility_opt> <unterminated_decl>
            192 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Declarations --------------------------------------------
            // <declaration> -> <fn_decl> | <struct_decl> | <enum_decl>
            //               |  <trait_decl> | <impl_decl> | <namespace_decl>
            //               |  <var_decl> | <const_decl>
            //               |  <macro_decl>
            89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 => self.pass(c[0]),

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
            // `%repr` is one token, so the name arrives with the sigil already
            // spent and the node begins where the `%` was -- which is what a
            // message about a declaration carrying one should point at.
            // <attribute> -> ATTR_NAME
            38 => self.at(ASTNodeKind::Attr { name: self.text(c[0]), args: Vec::new() }, c[0]),
            // <attribute> -> ATTR_NAME ( <attr_arg_list_opt> )
            39 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::Attr { name, args: self.list(c[2]) }, c[0])
            }
            // <attribute_list> -> ε
            40 => self.here(ASTNodeKind::List(Vec::new())),
            // <attribute_list> -> <attribute_list> <attribute>
            41 => self.grew(c[0], c[1]),

            // ---- ASTVisibility ----------------------------------------------
            // <visibility> -> public
            385 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Public)), c[0]),
            // <visibility> -> private
            386 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Private)), c[0]),
            // <visibility_opt> -> ε
            387 => self.here(ASTNodeKind::Empty),
            // <visibility_opt> -> <visibility>
            388 => self.pass(c[0]),

            // ---- Bindings ------------------------------------------------
            // <binding_name> -> IDENTIFIER
            48 => self.pass(c[0]),
            // <binding_name> -> _
            49 => self.pass(c[0]),

            // ---- Functions -----------------------------------------------
            // <fn_body> -> <block> <semi_opt>
            140 => self.pass(c[0]),
            // <fn_body> -> ;
            // A signature and no body, which `Fn::body` spells `None`.
            141 => self.at(ASTNodeKind::Empty, c[0]),
            // <fn_decl> -> <fn_sig> <fn_body>
            142 => {
                let mut node = self.pass(c[0]);
                match &mut node.kind {
                    ASTNodeKind::Fn { body, .. } => *body = self.opt(c[1]),
                    other => panic!("a body was written on {:?}", other),
                }
                node
            }
            // <fn_head> -> fn IDENTIFIER <generic_params_opt> ( <param_list_opt> ) <return_type_opt> <where_clause_opt>
            143 => {
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
            144 => self.pass(c[0]),
            // <fn_sig> -> const <fn_head>
            145 => self.with_modifier(c[1], c[0], true, false),
            // <fn_sig> -> unsafe <fn_head>
            146 => self.with_modifier(c[1], c[0], false, true),
            // <fn_sig> -> const unsafe <fn_head>
            147 => self.with_modifier(c[2], c[0], true, true),

            // ---- Macros --------------------------------------------------
            // <macro_decl> -> macro IDENTIFIER ( <macro_param_list_opt> ) <block> <semi_opt>
            215 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::MacroDecl {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        params: self.list(c[3]),
                        body: c[5],
                    },
                    c[0],
                )
            }
            // <macro_param> -> MACRO_PARAM : IDENTIFIER
            216 => {
                let name = self.mvar(c[0]);
                self.at(ASTNodeKind::MacroParam { name, fragment: self.text(c[2]) }, c[0])
            }
            // <macro_param_list> -> <macro_param>
            217 => self.one(c[0]),
            // <macro_param_list> -> <macro_param_list> , <macro_param>
            218 => self.grew(c[0], c[2]),
            // <macro_param_list_opt> -> ε
            219 => self.here(ASTNodeKind::List(Vec::new())),
            // <macro_param_list_opt> -> <macro_param_list>
            220 => self.pass(c[0]),

            // ---- Parameters ----------------------------------------------
            // <param> -> <param_name> <type_annotation_opt>
            247 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <param_list> -> <param_seq>
            248 => self.pass(c[0]),
            // <param_list> -> <param_seq> ,
            249 => self.pass(c[0]),
            // <param_list_opt> -> ε
            250 => self.here(ASTNodeKind::List(Vec::new())),
            // <param_list_opt> -> <param_list>
            251 => self.pass(c[0]),
            // <param_name> -> this
            252 => self.pass(c[0]),
            // <param_name> -> <binding_name>
            253 => self.pass(c[0]),
            // <param_seq> -> <param>
            254 => self.one(c[0]),
            // <param_seq> -> <param_seq> , <param>
            255 => self.grew(c[0], c[2]),

            // ---- Generics ------------------------------------------------
            // <generic_args> -> < <generic_arg_list> >
            153 => self.pass(c[1]),
            // A type argument list holds types and lifetimes both, so the two
            // pass up as they are and the list is of whatever was written.
            // <generic_arg> -> <type>
            149 => self.pass(c[0]),
            // <generic_arg> -> <lifetime>
            150 => self.pass(c[0]),
            // <generic_arg_list> -> <generic_arg>
            151 => self.one(c[0]),
            // <generic_arg_list> -> <generic_arg_list> , <generic_arg>
            152 => self.grew(c[0], c[2]),
            // <generic_args_opt> -> ε
            154 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_args_opt> -> <generic_args>
            155 => self.pass(c[0]),
            // <generic_param> -> IDENTIFIER
            156 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> IDENTIFIER : <type_bounds>
            157 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // A lifetime parameter stands among the type parameters, and the
            // name reaching here is the one the `~` was stripped from.
            // <generic_param> -> <lifetime>
            158 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> <lifetime> : <type_bounds>
            159 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // <generic_param_list> -> <generic_param>
            160 => self.one(c[0]),
            // <generic_param_list> -> <generic_param_list> , <generic_param>
            161 => self.grew(c[0], c[2]),
            // <generic_params> -> < <generic_param_list> >
            162 => self.pass(c[1]),
            // <generic_params_opt> -> ε
            163 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_params_opt> -> <generic_params>
            164 => self.pass(c[0]),

            // ---- where ---------------------------------------------------
            // <where_clause_opt> -> ε
            389 => self.here(ASTNodeKind::List(Vec::new())),
            // <where_clause_opt> -> where <where_pred_list>
            390 => self.pass(c[1]),
            // <where_pred> -> <type> : <type_bounds>
            391 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred> -> <lifetime> : <type_bounds>
            // The same node: a lifetime is what `ty` holds, and which of the
            // two was written is the node it points at.
            392 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred_list> -> <where_pred>
            393 => self.one(c[0]),
            // <where_pred_list> -> <where_pred_list> , <where_pred>
            394 => self.grew(c[0], c[2]),

            // ---- Structs -------------------------------------------------
            // <struct_decl> -> struct IDENTIFIER <generic_params_opt> { <field_decl_list_opt> } <semi_opt>
            336 => {
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
            337 => self.at(
                ASTNodeKind::StructLit { base: HOLE, fields: self.list(c[1]) },
                c[0],
            ),

            // ---- Struct fields -------------------------------------------
            // <field_decl> -> <attribute_list> <visibility_opt> IDENTIFIER : <type>
            121 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[2] } else { c[0] };
                let name = self.text(c[2]);
                self.at(
                    ASTNodeKind::FieldDecl { attrs, vis: self.visibility(c[1]), name, ty: c[4] },
                    anchor,
                )
            }
            // <field_decl_list> -> <field_decl>
            122 => self.one(c[0]),
            // <field_decl_list> -> <field_decl_list> , <field_decl>
            123 => self.grew(c[0], c[2]),
            // <field_decl_list_opt> -> ε
            124 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_decl_list_opt> -> <field_decl_list>
            125 => self.pass(c[0]),
            // <field_decl_list_opt> -> <field_decl_list> ,
            126 => self.pass(c[0]),

            // ---- Enums ---------------------------------------------------
            // <discriminant> -> = <expression>
            98 => self.at(ASTNodeKind::Discriminant(c[1]), c[0]),
            // <elif_list> -> ε
            99 => self.here(ASTNodeKind::List(Vec::new())),
            // <elif_list> -> <elif_list> elif <header_expr> <block>
            // The `elif` becomes a node of its own here: the list holds them,
            // and nothing above this rule sees the three symbols again.
            100 => {
                let elif = self.at(ASTNodeKind::Elif { cond: c[2], block: c[3] }, c[1]);
                let id = self.push_node(elif);
                self.grew(c[0], id)
            }
            // <else_opt> -> ε
            101 => self.here(ASTNodeKind::Empty),
            // <else_opt> -> else <block>
            102 => self.pass(c[1]),
            // <enum_decl> -> enum IDENTIFIER <generic_params_opt> { <enum_variant_list_opt> } <semi_opt>
            103 => {
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
            104 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[1] } else { c[0] };
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::EnumVariant { attrs, name, body: self.opt(c[2]) },
                    anchor,
                )
            }
            // <enum_variant_list> -> <enum_variant>
            105 => self.one(c[0]),
            // <enum_variant_list> -> <enum_variant_list> , <enum_variant>
            106 => self.grew(c[0], c[2]),
            // <enum_variant_list_opt> -> ε
            107 => self.here(ASTNodeKind::List(Vec::new())),
            // <enum_variant_list_opt> -> <enum_variant_list>
            108 => self.pass(c[0]),
            // <enum_variant_list_opt> -> <enum_variant_list> ,
            109 => self.pass(c[0]),

            // ---- Named payloads and named types --------------------------
            // <named_payload> -> VALUE_LCURLY <field_decl_list_opt> }
            244 => self.at(ASTNodeKind::NamedPayload(self.list(c[1])), c[0]),
            // <named_type> -> <qualified_name> <generic_args_opt>
            245 => self.at(
                ASTNodeKind::Named { path: self.path(c[0]), args: self.list(c[1]) },
                c[0],
            ),

            // ---- Traits --------------------------------------------------
            // <trait_decl> -> trait IDENTIFIER <generic_params_opt> { <trait_member_list> <trait_tail_opt> } <semi_opt>
            338 => {
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
            339 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),
            // <trait_member_list> -> ε
            340 => self.here(ASTNodeKind::List(Vec::new())),
            // <trait_member_list> -> <trait_member_list> <trait_member>
            341 => self.grew(c[0], c[1]),
            // <trait_tail_opt> -> ε
            342 => self.here(ASTNodeKind::Empty),
            // <trait_tail_opt> -> <attribute_list> <fn_sig>
            343 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),

            // ---- Impls ---------------------------------------------------
            // <impl_decl> -> impl <generic_params_opt> <type> <impl_for_opt> <where_clause_opt> { <impl_member_list> <impl_tail_opt> } <semi_opt>
            169 => self.at(
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
            170 => self.here(ASTNodeKind::Empty),
            // <impl_for_opt> -> for <type>
            171 => self.pass(c[1]),
            // <impl_member> -> <attribute_list> <visibility_opt> <fn_decl>
            172 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <impl_member_list> -> ε
            173 => self.here(ASTNodeKind::List(Vec::new())),
            // <impl_member_list> -> <impl_member_list> <impl_member>
            174 => self.grew(c[0], c[1]),
            // <impl_tail_opt> -> ε
            175 => self.here(ASTNodeKind::Empty),
            // <impl_tail_opt> -> <attribute_list> <visibility_opt> <fn_sig>
            176 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Namespaces ----------------------------------------------
            // <namespace_decl> -> namespace IDENTIFIER { <item_list> <item_tail_opt> } <semi_opt>
            246 => {
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
            177 => self.here(ASTNodeKind::Empty),
            // <import_alias_opt> -> as IDENTIFIER
            178 => self.pass(c[1]),
            // <import_decl> -> <import_head> ;
            179 => self.pass(c[0]),
            // <import_head> -> import <import_path> <import_alias_opt>
            180 => {
                let alias = self.opt(c[2]).map(|id| self.text(id));
                self.at(ASTNodeKind::Import { path: self.path(c[1]), alias }, c[0])
            }
            // <import_path> -> IDENTIFIER
            181 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <import_path> -> <import_path> :: IDENTIFIER
            182 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }

            // ---- Constants -----------------------------------------------
            // <const_decl> -> <const_head> ;
            85 => self.pass(c[0]),
            // <const_expr> -> <expression>
            86 => self.pass(c[0]),
            // <const_head> -> const IDENTIFIER : <type> = <const_expr>
            87 => {
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
            88 => self.pass(c[0]),

            // ---- Variables -----------------------------------------------
            // <var_decl> -> <var_head> ;
            375 => self.pass(c[0]),
            // <var_head> -> <var_intro> <binding_name> <type_annotation_opt> <initializer_opt>
            376 => {
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
            377 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Let)), c[0]),
            // <var_intro> -> var
            378 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Var)), c[0]),

            // ---- The optional semicolon ----------------------------------
            // Nothing above reads it: it is written for the grammar, which has
            // to say that it may be there.
            // <semi_opt> -> ε
            320 => self.here(ASTNodeKind::Empty),
            // <semi_opt> -> ;
            321 => self.at(ASTNodeKind::Empty, c[0]),

            // ---- What a `;` may be left off ------------------------------
            // <unterminated_decl> -> <var_head> | <const_head> | <fn_sig>
            365 | 366 | 367 => self.pass(c[0]),
            // <unterminated_stmt> -> <expression> | <var_head> | <const_head>
            368 | 369 | 370 => self.pass(c[0]),
            // <unterminated_stmt> -> unsafe <unterminated_stmt>
            371 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            _ => return None,
        })
    }
}
