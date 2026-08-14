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
            // <item> -> <attribute_list> <visibility_opt> <declaration>
            194 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <item_list> -> ε
            195 => self.here(ASTNodeKind::List(Vec::new())),
            // <item_list> -> <item_list> <item>
            196 => self.grew(c[0], c[1]),
            // <item_tail_opt> -> ε
            197 => self.here(ASTNodeKind::Empty),
            // <item_tail_opt> -> <attribute_list> <visibility_opt> <unterminated_decl>
            198 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Declarations --------------------------------------------
            // <declaration> -> <import_decl> | <fn_decl> | <type_decl>
            //               |  <macro_decl> | <struct_decl> | <enum_decl>
            //               |  <trait_decl> | <impl_decl> | <namespace_decl>
            //               |  <var_decl> | <const_decl>
            89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 => self.pass(c[0]),

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
            // <visibility> -> pub
            406 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Pub)), c[0]),
            // <visibility> -> priv
            407 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Priv)), c[0]),
            // <visibility> -> pub ( suite )
            408 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Suite)), c[0]),
            // <visibility_opt> -> ε
            409 => self.here(ASTNodeKind::Empty),
            // <visibility_opt> -> <visibility>
            410 => self.pass(c[0]),

            // ---- Bindings ------------------------------------------------
            // <binding_name> -> IDENTIFIER
            48 => self.pass(c[0]),
            // <binding_name> -> _
            49 => self.pass(c[0]),

            // ---- Functions -----------------------------------------------
            // <fn_body> -> <block> <semi_opt>
            142 => self.pass(c[0]),
            // <fn_body> -> ;
            // A signature and no body, which `Fn::body` spells `None`.
            143 => self.at(ASTNodeKind::Empty, c[0]),
            // <fn_decl> -> <fn_sig> <fn_body>
            144 => {
                let mut node = self.pass(c[0]);
                match &mut node.kind {
                    ASTNodeKind::Fn { body, .. } => *body = self.opt(c[1]),
                    other => panic!("a body was written on {:?}", other),
                }
                node
            }
            // <fn_head> -> fn IDENTIFIER <generic_params_opt> ( <param_list_opt> ) <return_type_opt> <where_clause_opt>
            145 => {
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
            146 => self.pass(c[0]),
            // <fn_sig> -> const <fn_head>
            147 => self.with_modifier(c[1], c[0], true, false),
            // <fn_sig> -> unsafe <fn_head>
            148 => self.with_modifier(c[1], c[0], false, true),
            // <fn_sig> -> const unsafe <fn_head>
            149 => self.with_modifier(c[2], c[0], true, true),

            // ---- Type aliases --------------------------------------------
            // <type_decl> -> <type_head> ;
            372 => self.pass(c[0]),
            // <type_head> -> type IDENTIFIER <generic_params_opt> = <type>
            373 => {
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::TypeAlias {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        name,
                        generics: self.list(c[2]),
                        ty: c[4],
                    },
                    c[0],
                )
            }

            // ---- Macros --------------------------------------------------
            // <macro_decl> -> macro IDENTIFIER ( <macro_param_list_opt> ) <block> <semi_opt>
            221 => {
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
            222 => {
                let name = self.mvar(c[0]);
                self.at(ASTNodeKind::MacroParam { name, fragment: self.text(c[2]) }, c[0])
            }
            // <macro_param_list> -> <macro_param>
            223 => self.one(c[0]),
            // <macro_param_list> -> <macro_param_list> , <macro_param>
            224 => self.grew(c[0], c[2]),
            // <macro_param_list_opt> -> ε
            225 => self.here(ASTNodeKind::List(Vec::new())),
            // <macro_param_list_opt> -> <macro_param_list>
            226 => self.pass(c[0]),

            // ---- Parameters ----------------------------------------------
            // <param> -> <binding_name> <type_annotation_opt>
            253 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <param> -> <receiver>
            // A receiver has no annotation to carry: its type is the one the
            // impl names, and how it is held was written on the `self`.
            254 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: None },
                c[0],
            ),
            // <param_list> -> <param_seq>
            255 => self.pass(c[0]),
            // <param_list> -> <param_seq> ,
            256 => self.pass(c[0]),
            // <param_list_opt> -> ε
            257 => self.here(ASTNodeKind::List(Vec::new())),
            // <param_list_opt> -> <param_list>
            258 => self.pass(c[0]),
            // <receiver> -> self
            // How the receiver is held is the whole of what these three say, so
            // the rule is the answer and there is no child to ask.
            327 => self.at(ASTNodeKind::SelfRecv(ASTSelf::Value), c[0]),
            // <receiver> -> & self
            328 => self.at(ASTNodeKind::SelfRecv(ASTSelf::Ref), c[0]),
            // <receiver> -> * self
            329 => self.at(ASTNodeKind::SelfRecv(ASTSelf::Mut), c[0]),
            // <param_seq> -> <param>
            259 => self.one(c[0]),
            // <param_seq> -> <param_seq> , <param>
            260 => self.grew(c[0], c[2]),

            // ---- Generics ------------------------------------------------
            // <generic_args> -> < <generic_arg_list> >
            155 => self.pass(c[1]),
            // A type argument list holds types and lifetimes both, so the two
            // pass up as they are and the list is of whatever was written.
            // <generic_arg> -> <type>
            151 => self.pass(c[0]),
            // <generic_arg> -> <lifetime>
            152 => self.pass(c[0]),
            // <generic_arg_list> -> <generic_arg>
            153 => self.one(c[0]),
            // <generic_arg_list> -> <generic_arg_list> , <generic_arg>
            154 => self.grew(c[0], c[2]),
            // <generic_args_opt> -> ε
            156 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_args_opt> -> <generic_args>
            157 => self.pass(c[0]),
            // <generic_param> -> IDENTIFIER
            158 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> IDENTIFIER : <type_bounds>
            159 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // A lifetime parameter stands among the type parameters, and the
            // name reaching here is the one the `~` was stripped from.
            // <generic_param> -> <lifetime>
            160 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> <lifetime> : <type_bounds>
            161 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // <generic_param_list> -> <generic_param>
            162 => self.one(c[0]),
            // <generic_param_list> -> <generic_param_list> , <generic_param>
            163 => self.grew(c[0], c[2]),
            // <generic_params> -> < <generic_param_list> >
            164 => self.pass(c[1]),
            // <generic_params_opt> -> ε
            165 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_params_opt> -> <generic_params>
            166 => self.pass(c[0]),

            // ---- where ---------------------------------------------------
            // <where_clause_opt> -> ε
            411 => self.here(ASTNodeKind::List(Vec::new())),
            // <where_clause_opt> -> where <where_pred_list>
            412 => self.pass(c[1]),
            // <where_pred> -> <type> : <type_bounds>
            413 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred> -> <lifetime> : <type_bounds>
            // The same node: a lifetime is what `ty` holds, and which of the
            // two was written is the node it points at.
            414 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred_list> -> <where_pred>
            415 => self.one(c[0]),
            // <where_pred_list> -> <where_pred_list> , <where_pred>
            416 => self.grew(c[0], c[2]),

            // ---- Structs -------------------------------------------------
            // <struct_decl> -> struct IDENTIFIER <generic_params_opt> { <field_decl_list_opt> } <semi_opt>
            351 => {
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
            352 => self.at(
                ASTNodeKind::StructLit { base: HOLE, fields: self.list(c[1]) },
                c[0],
            ),

            // ---- Struct fields -------------------------------------------
            // <field_decl> -> <attribute_list> <visibility_opt> IDENTIFIER : <type>
            123 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[2] } else { c[0] };
                let name = self.text(c[2]);
                self.at(
                    ASTNodeKind::FieldDecl { attrs, vis: self.visibility(c[1]), name, ty: c[4] },
                    anchor,
                )
            }
            // <field_decl_list> -> <field_decl>
            124 => self.one(c[0]),
            // <field_decl_list> -> <field_decl_list> , <field_decl>
            125 => self.grew(c[0], c[2]),
            // <field_decl_list_opt> -> ε
            126 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_decl_list_opt> -> <field_decl_list>
            127 => self.pass(c[0]),
            // <field_decl_list_opt> -> <field_decl_list> ,
            128 => self.pass(c[0]),

            // ---- Enums ---------------------------------------------------
            // <discriminant> -> = <expression>
            100 => self.at(ASTNodeKind::Discriminant(c[1]), c[0]),
            // <elif_list> -> ε
            101 => self.here(ASTNodeKind::List(Vec::new())),
            // <elif_list> -> <elif_list> elif <header_expr> <block>
            // The `elif` becomes a node of its own here: the list holds them,
            // and nothing above this rule sees the three symbols again.
            102 => {
                let elif = self.at(ASTNodeKind::Elif { cond: c[2], block: c[3] }, c[1]);
                let id = self.push_node(elif);
                self.grew(c[0], id)
            }
            // <else_opt> -> ε
            103 => self.here(ASTNodeKind::Empty),
            // <else_opt> -> else <block>
            104 => self.pass(c[1]),
            // <enum_decl> -> enum IDENTIFIER <generic_params_opt> { <enum_variant_list_opt> } <semi_opt>
            105 => {
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
            106 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[1] } else { c[0] };
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::EnumVariant { attrs, name, body: self.opt(c[2]) },
                    anchor,
                )
            }
            // <enum_variant_list> -> <enum_variant>
            107 => self.one(c[0]),
            // <enum_variant_list> -> <enum_variant_list> , <enum_variant>
            108 => self.grew(c[0], c[2]),
            // <enum_variant_list_opt> -> ε
            109 => self.here(ASTNodeKind::List(Vec::new())),
            // <enum_variant_list_opt> -> <enum_variant_list>
            110 => self.pass(c[0]),
            // <enum_variant_list_opt> -> <enum_variant_list> ,
            111 => self.pass(c[0]),

            // ---- Named payloads and named types --------------------------
            // <named_payload> -> VALUE_LCURLY <field_decl_list_opt> }
            250 => self.at(ASTNodeKind::NamedPayload(self.list(c[1])), c[0]),
            // <named_type> -> <qualified_name> <generic_args_opt>
            251 => self.at(
                ASTNodeKind::Named { path: self.path(c[0]), args: self.list(c[1]) },
                c[0],
            ),

            // ---- Traits --------------------------------------------------
            // <trait_decl> -> trait IDENTIFIER <generic_params_opt> { <trait_member_list> <trait_tail_opt> } <semi_opt>
            353 => {
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
            354 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),
            // <trait_member_list> -> ε
            355 => self.here(ASTNodeKind::List(Vec::new())),
            // <trait_member_list> -> <trait_member_list> <trait_member>
            356 => self.grew(c[0], c[1]),
            // <trait_tail_opt> -> ε
            357 => self.here(ASTNodeKind::Empty),
            // <trait_tail_opt> -> <attribute_list> <fn_sig>
            358 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),

            // ---- Impls ---------------------------------------------------
            // <impl_decl> -> impl <generic_params_opt> <type> <impl_for_opt> <where_clause_opt> { <impl_member_list> <impl_tail_opt> } <semi_opt>
            171 => self.at(
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
            172 => self.here(ASTNodeKind::Empty),
            // <impl_for_opt> -> for <type>
            173 => self.pass(c[1]),
            // <impl_member> -> <attribute_list> <visibility_opt> <fn_decl>
            174 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <impl_member_list> -> ε
            175 => self.here(ASTNodeKind::List(Vec::new())),
            // <impl_member_list> -> <impl_member_list> <impl_member>
            176 => self.grew(c[0], c[1]),
            // <impl_tail_opt> -> ε
            177 => self.here(ASTNodeKind::Empty),
            // <impl_tail_opt> -> <attribute_list> <visibility_opt> <fn_sig>
            178 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Namespaces ----------------------------------------------
            // <namespace_decl> -> namespace IDENTIFIER { <item_list> <item_tail_opt> } <semi_opt>
            252 => {
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
            // A tree is flattened as it reduces, so what reaches `Import` is the
            // list of leaves it named and never a shape of its own. A group
            // hands its leaves up and the path in front of it is written onto
            // each: `a::{b, c::*}` is `a::b` and `a::c::*` by the time the
            // `import` is reduced.
            // <import_decl> -> <import_head> ;
            179 => self.pass(c[0]),
            // <import_head> -> import <import_tree>
            180 => self.at(
                ASTNodeKind::Import {
                    attrs:  Vec::new(),
                    vis:    ASTVisibility::Unwritten,
                    leaves: self.leaves(c[1]),
                },
                c[0],
            ),
            // <import_list> -> <import_seq> | <import_seq> ,
            181 | 182 => self.pass(c[0]),
            // <import_path> -> <path_seg>
            183 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <import_path> -> <import_path> :: <path_seg>
            184 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }
            // <import_seq> -> <import_tree>
            185 => self.pass(c[0]),
            // <import_seq> -> <import_seq> , <import_tree>
            186 => {
                let mut leaves = self.leaves(c[0]);
                leaves.extend(self.leaves(c[2]));
                self.at(ASTNodeKind::ImportTree(leaves), c[0])
            }
            // <import_tree> -> <import_path>
            187 => {
                let leaf = ASTImportLeaf { path: self.path(c[0]), alias: None, glob: false };
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> as IDENTIFIER
            188 => {
                let leaf = ASTImportLeaf {
                    path:  self.path(c[0]),
                    alias: Some(self.text(c[2])),
                    glob:  false,
                };
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> ::*
            189 => {
                let leaf = ASTImportLeaf { path: self.path(c[0]), alias: None, glob: true };
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> :: VALUE_LCURLY <import_list> }
            190 => {
                let prefix = self.path(c[0]);
                let mut leaves = self.leaves(c[3]);
                for leaf in &mut leaves {
                    let mut path = prefix.clone();
                    path.append(&mut leaf.path);
                    leaf.path = path;
                }
                self.at(ASTNodeKind::ImportTree(leaves), c[0])
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
            396 => self.pass(c[0]),
            // <var_head> -> <var_intro> <binding_name> <type_annotation_opt> <initializer_opt>
            397 => {
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
            398 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Let)), c[0]),
            // <var_intro> -> var
            399 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Var)), c[0]),

            // ---- The optional semicolon ----------------------------------
            // Nothing above reads it: it is written for the grammar, which has
            // to say that it may be there.
            // <semi_opt> -> ε
            335 => self.here(ASTNodeKind::Empty),
            // <semi_opt> -> ;
            336 => self.at(ASTNodeKind::Empty, c[0]),

            // ---- What a `;` may be left off ------------------------------
            // <unterminated_decl> -> <var_head> | <const_head> | <type_head>
            //                     |  <import_head> | <fn_sig>
            383 | 384 | 385 | 386 | 387 => self.pass(c[0]),
            // <unterminated_stmt> -> <expression> | <var_head> | <const_head>
            //                     |  <type_head>
            388 | 389 | 390 | 391 => self.pass(c[0]),
            // <unterminated_stmt> -> unsafe <unterminated_stmt>
            392 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            _ => return None,
        })
    }
}
