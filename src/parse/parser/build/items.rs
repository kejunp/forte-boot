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
            201 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <item_list> -> ε
            202 => self.here(ASTNodeKind::List(Vec::new())),
            // <item_list> -> <item_list> <item>
            203 => self.grew(c[0], c[1]),
            // <item_tail_opt> -> ε
            204 => self.here(ASTNodeKind::Empty),
            // <item_tail_opt> -> <attribute_list> <visibility_opt> <unterminated_decl>
            205 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Declarations --------------------------------------------
            // <declaration> -> <import_decl> | <fn_decl> | <type_decl>
            //               |  <macro_decl> | <struct_decl> | <enum_decl>
            //               |  <trait_decl> | <impl_decl> | <namespace_decl>
            //               |  <var_decl> | <const_decl>
            90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 | 100 => self.pass(c[0]),

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
            418 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Pub)), c[0]),
            // <visibility> -> priv
            419 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Priv)), c[0]),
            // <visibility> -> pub ( suite )
            420 => self.at(ASTNodeKind::Mark(ASTMark::Vis(ASTVisibility::Suite)), c[0]),
            // <visibility_opt> -> ε
            421 => self.here(ASTNodeKind::Empty),
            // <visibility_opt> -> <visibility>
            422 => self.pass(c[0]),

            // ---- Bindings ------------------------------------------------
            // <binding_name> -> IDENTIFIER
            48 => self.pass(c[0]),
            // <binding_name> -> _
            49 => self.pass(c[0]),

            // ---- Functions -----------------------------------------------
            // <fn_body> -> <block> <semi_opt>
            143 => self.pass(c[0]),
            // <fn_body> -> ;
            // A signature and no body, which `Fn::body` spells `None`.
            144 => self.at(ASTNodeKind::Empty, c[0]),
            // <fn_decl> -> <fn_sig> <fn_body>
            145 => {
                let mut node = self.pass(c[0]);
                match &mut node.kind {
                    ASTNodeKind::Fn { body, .. } => *body = self.opt(c[1]),
                    other => panic!("a body was written on {:?}", other),
                }
                node
            }
            // <fn_head> -> fn IDENTIFIER <generic_params_opt> ( <param_list_opt> ) <return_type_opt> <where_clause_opt>
            146 => {
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
            147 => self.pass(c[0]),
            // <fn_sig> -> const <fn_head>
            148 => self.with_modifier(c[1], c[0], true, false),
            // <fn_sig> -> unsafe <fn_head>
            149 => self.with_modifier(c[1], c[0], false, true),
            // <fn_sig> -> const unsafe <fn_head>
            150 => self.with_modifier(c[2], c[0], true, true),

            // ---- Type aliases --------------------------------------------
            // <type_decl> -> <type_head> ;
            381 => self.pass(c[0]),
            // <type_head> -> type IDENTIFIER <generic_params_opt> = <type>
            382 => {
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
            228 => {
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
            229 => {
                let name = self.mvar(c[0]);
                self.at(ASTNodeKind::MacroParam { name, fragment: self.text(c[2]) }, c[0])
            }
            // <macro_param_list> -> <macro_param>
            230 => self.one(c[0]),
            // <macro_param_list> -> <macro_param_list> , <macro_param>
            231 => self.grew(c[0], c[2]),
            // <macro_param_list_opt> -> ε
            232 => self.here(ASTNodeKind::List(Vec::new())),
            // <macro_param_list_opt> -> <macro_param_list>
            233 => self.pass(c[0]),

            // ---- Parameters ----------------------------------------------
            // <param> -> <binding_name> <type_annotation_opt>
            260 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <param> -> <receiver>
            // A receiver has no annotation to carry: its type is the one the
            // impl names, and how it is held was written on the `self`.
            261 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: None },
                c[0],
            ),
            // <param_list> -> <param_seq>
            262 => self.pass(c[0]),
            // <param_list> -> <param_seq> ,
            263 => self.pass(c[0]),
            // <param_list_opt> -> ε
            264 => self.here(ASTNodeKind::List(Vec::new())),
            // <param_list_opt> -> <param_list>
            265 => self.pass(c[0]),
            // <receiver> -> self
            // Nothing is written in front, so nothing is taken: a bare `self`
            // is the value whole and has no region to name.
            335 => self.at(ASTNodeKind::SelfRecv(ASTSelf::Value, None), c[0]),
            // <receiver> -> <ref_op> <lifetime_opt> self
            // The same three pieces `<ref_type>` is made of, in front of the
            // word instead of in front of a type.
            336 => {
                let how = match ref_of(self.mark(c[0])) {
                    ASTRefOp::Imm => ASTSelf::Ref,
                    ASTRefOp::Mut => ASTSelf::Mut,
                };
                let life = self.opt(c[1]).map(|l| match self.kind(l) {
                    ASTNodeKind::Lifetime(name) => name.clone(),
                    other => panic!("a lifetime built from {:?}", other),
                });
                self.at(ASTNodeKind::SelfRecv(how, life), c[0])
            }
            // <param_seq> -> <param>
            266 => self.one(c[0]),
            // <param_seq> -> <param_seq> , <param>
            267 => self.grew(c[0], c[2]),

            // ---- Generics ------------------------------------------------
            // <generic_args> -> < <generic_arg_list> >
            162 => self.pass(c[1]),
            // A type argument list holds types and lifetimes both, so the two
            // pass up as they are and the list is of whatever was written.
            // <generic_arg> -> <type>
            158 => self.pass(c[0]),
            // <generic_arg> -> <lifetime>
            159 => self.pass(c[0]),
            // <generic_arg_list> -> <generic_arg>
            160 => self.one(c[0]),
            // <generic_arg_list> -> <generic_arg_list> , <generic_arg>
            161 => self.grew(c[0], c[2]),
            // <generic_args_opt> -> ε
            163 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_args_opt> -> <generic_args>
            164 => self.pass(c[0]),
            // <generic_param> -> IDENTIFIER
            165 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> IDENTIFIER : <type_bounds>
            166 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::GenericParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // A lifetime parameter stands among the type parameters, and the
            // name reaching here is the one the `~` was stripped from.
            // <generic_param> -> <lifetime>
            167 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: Vec::new() }, c[0])
            }
            // <generic_param> -> <lifetime> : <type_bounds>
            168 => {
                let name = self.life(c[0]);
                self.at(ASTNodeKind::LifetimeParam { name, bounds: self.list(c[2]) }, c[0])
            }
            // <generic_param_list> -> <generic_param>
            169 => self.one(c[0]),
            // <generic_param_list> -> <generic_param_list> , <generic_param>
            170 => self.grew(c[0], c[2]),
            // <generic_params> -> < <generic_param_list> >
            171 => self.pass(c[1]),
            // <generic_params_opt> -> ε
            172 => self.here(ASTNodeKind::List(Vec::new())),
            // <generic_params_opt> -> <generic_params>
            173 => self.pass(c[0]),

            // ---- where ---------------------------------------------------
            // <where_clause_opt> -> ε
            423 => self.here(ASTNodeKind::List(Vec::new())),
            // <where_clause_opt> -> where <where_pred_list>
            424 => self.pass(c[1]),
            // <where_pred> -> <where_subject> : <type_bounds>
            425 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // A `<where_subject>` is a `<type>` with one branch left out, and
            // what it builds is a type: the branch it leaves out is a grammar's
            // trouble with a colon and nothing this tree has to keep.
            // <where_subject> -> <ref_op> <lifetime_opt> <where_subject>
            429 => {
                let op = ref_of(self.mark(c[0]));
                let life = self.opt(c[1]);
                self.at(ASTNodeKind::RefType { op, life, inner: c[2] }, c[0])
            }
            // <where_subject> -> ptr <where_subject>
            430 => self.at(ASTNodeKind::PtrType(c[1]), c[0]),
            // <where_subject> -> <base_type> <array_suffix_list>
            431 => self.fold_suffixes(c[0], c[1]),
            // <where_pred> -> <lifetime> : <type_bounds>
            // The same node: a lifetime is what `ty` holds, and which of the
            // two was written is the node it points at.
            426 => self.at(ASTNodeKind::WherePred { ty: c[0], bounds: self.list(c[2]) }, c[0]),
            // <where_pred_list> -> <where_pred>
            427 => self.one(c[0]),
            // <where_pred_list> -> <where_pred_list> , <where_pred>
            428 => self.grew(c[0], c[2]),

            // ---- Structs -------------------------------------------------
            // <struct_decl> -> struct IDENTIFIER <generic_params_opt> { <field_decl_list_opt> } <semi_opt>
            358 => {
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
            359 => self.at(
                ASTNodeKind::StructLit { base: HOLE, fields: self.list(c[1]) },
                c[0],
            ),

            // ---- Struct fields -------------------------------------------
            // <field_decl> -> <attribute_list> <visibility_opt> IDENTIFIER : <type>
            124 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[2] } else { c[0] };
                let name = self.text(c[2]);
                self.at(
                    ASTNodeKind::FieldDecl { attrs, vis: self.visibility(c[1]), name, ty: c[4] },
                    anchor,
                )
            }
            // <field_decl_list> -> <field_decl>
            125 => self.one(c[0]),
            // <field_decl_list> -> <field_decl_list> , <field_decl>
            126 => self.grew(c[0], c[2]),
            // <field_decl_list_opt> -> ε
            127 => self.here(ASTNodeKind::List(Vec::new())),
            // <field_decl_list_opt> -> <field_decl_list>
            128 => self.pass(c[0]),
            // <field_decl_list_opt> -> <field_decl_list> ,
            129 => self.pass(c[0]),

            // ---- Enums ---------------------------------------------------
            // <discriminant> -> = <expression>
            101 => self.at(ASTNodeKind::Discriminant(c[1]), c[0]),
            // <elif_list> -> ε
            102 => self.here(ASTNodeKind::List(Vec::new())),
            // <elif_list> -> <elif_list> elif <header_expr> <block>
            // The `elif` becomes a node of its own here: the list holds them,
            // and nothing above this rule sees the three symbols again.
            103 => {
                let elif = self.at(ASTNodeKind::Elif { cond: c[2], block: c[3] }, c[1]);
                let id = self.push_node(elif);
                self.grew(c[0], id)
            }
            // <else_opt> -> ε
            104 => self.here(ASTNodeKind::Empty),
            // <else_opt> -> else <block>
            105 => self.pass(c[1]),
            // <enum_decl> -> enum IDENTIFIER <generic_params_opt> { <enum_variant_list_opt> } <semi_opt>
            106 => {
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
            107 => {
                let attrs = self.list(c[0]);
                let anchor = if attrs.is_empty() { c[1] } else { c[0] };
                let name = self.text(c[1]);
                self.at(
                    ASTNodeKind::EnumVariant { attrs, name, body: self.opt(c[2]) },
                    anchor,
                )
            }
            // <enum_variant_list> -> <enum_variant>
            108 => self.one(c[0]),
            // <enum_variant_list> -> <enum_variant_list> , <enum_variant>
            109 => self.grew(c[0], c[2]),
            // <enum_variant_list_opt> -> ε
            110 => self.here(ASTNodeKind::List(Vec::new())),
            // <enum_variant_list_opt> -> <enum_variant_list>
            111 => self.pass(c[0]),
            // <enum_variant_list_opt> -> <enum_variant_list> ,
            112 => self.pass(c[0]),

            // ---- Named payloads and named types --------------------------
            // <named_payload> -> VALUE_LCURLY <field_decl_list_opt> }
            257 => self.at(ASTNodeKind::NamedPayload(self.list(c[1])), c[0]),
            // <named_type> -> <qualified_name> <generic_args_opt>
            258 => self.at(
                ASTNodeKind::Named { path: self.path(c[0]), args: self.list(c[1]) },
                c[0],
            ),

            // ---- Traits --------------------------------------------------
            // <trait_decl> -> trait IDENTIFIER <generic_params_opt> { <trait_member_list> <trait_tail_opt> } <semi_opt>
            360 => {
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
            361 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),
            // <trait_member_list> -> ε
            362 => self.here(ASTNodeKind::List(Vec::new())),
            // <trait_member_list> -> <trait_member_list> <trait_member>
            363 => self.grew(c[0], c[1]),
            // <trait_tail_opt> -> ε
            364 => self.here(ASTNodeKind::Empty),
            // <trait_tail_opt> -> <attribute_list> <fn_sig>
            365 => self.with_attrs(c[1], c[0], ASTVisibility::Unwritten),

            // ---- Impls ---------------------------------------------------
            // <impl_decl> -> impl <generic_params_opt> <type> <impl_for_opt> <where_clause_opt> { <impl_member_list> <impl_tail_opt> } <semi_opt>
            178 => self.at(
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
            179 => self.here(ASTNodeKind::Empty),
            // <impl_for_opt> -> for <type>
            180 => self.pass(c[1]),
            // <impl_member> -> <attribute_list> <visibility_opt> <fn_decl>
            181 => self.with_attrs(c[2], c[0], self.visibility(c[1])),
            // <impl_member_list> -> ε
            182 => self.here(ASTNodeKind::List(Vec::new())),
            // <impl_member_list> -> <impl_member_list> <impl_member>
            183 => self.grew(c[0], c[1]),
            // <impl_tail_opt> -> ε
            184 => self.here(ASTNodeKind::Empty),
            // <impl_tail_opt> -> <attribute_list> <visibility_opt> <fn_sig>
            185 => self.with_attrs(c[2], c[0], self.visibility(c[1])),

            // ---- Namespaces ----------------------------------------------
            // <namespace_decl> -> namespace IDENTIFIER { <item_list> <item_tail_opt> } <semi_opt>
            259 => {
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
            186 => self.pass(c[0]),
            // <import_head> -> import <import_tree>
            187 => self.at(
                ASTNodeKind::Import {
                    attrs:  Vec::new(),
                    vis:    ASTVisibility::Unwritten,
                    leaves: self.leaves(c[1]),
                },
                c[0],
            ),
            // <import_list> -> <import_seq> | <import_seq> ,
            188 | 189 => self.pass(c[0]),
            // <import_path> -> <path_seg>
            190 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <import_path> -> <import_path> :: <path_seg>
            191 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }
            // <import_seq> -> <import_tree>
            192 => self.pass(c[0]),
            // <import_seq> -> <import_seq> , <import_tree>
            193 => {
                let mut leaves = self.leaves(c[0]);
                leaves.extend(self.leaves(c[2]));
                self.at(ASTNodeKind::ImportTree(leaves), c[0])
            }
            // <import_tree> -> <import_path>
            194 => {
                let leaf = self.leaf(c[0], None, false);
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> as IDENTIFIER
            195 => {
                let leaf = self.leaf(c[0], Some(self.text(c[2])), false);
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> ::*
            196 => {
                let leaf = self.leaf(c[0], None, true);
                self.at(ASTNodeKind::ImportTree(vec![leaf]), c[0])
            }
            // <import_tree> -> <import_path> :: VALUE_LCURLY <import_list> }
            197 => {
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
            86 => self.pass(c[0]),
            // <const_expr> -> <expression>
            87 => self.pass(c[0]),
            // <const_head> -> const IDENTIFIER : <type> = <const_expr>
            88 => {
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
            89 => self.pass(c[0]),

            // ---- Variables -----------------------------------------------
            // <var_decl> -> <var_head> ;
            408 => self.pass(c[0]),
            // <var_head> -> <var_intro> <gc_opt> <binding_name> <type_annotation_opt> <initializer_opt>
            409 => {
                let intro = intro_of(self.mark(c[0]));
                // The word itself is spent here: what is left of it is the flag,
                // and where it may stand is `tir::lower`'s to say.
                let gc = self.opt(c[1]).is_some();
                self.at(
                    ASTNodeKind::Variable {
                        attrs: Vec::new(),
                        vis: ASTVisibility::Unwritten,
                        intro,
                        gc,
                        name: self.binding(c[2]),
                        ty: self.opt(c[3]),
                        init: self.opt(c[4]),
                    },
                    c[0],
                )
            }
            // <var_intro> -> let
            410 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Let)), c[0]),
            // <var_intro> -> var
            411 => self.at(ASTNodeKind::Mark(ASTMark::Intro(ASTVariableIntro::Var)), c[0]),

            // ---- gc ------------------------------------------------------
            // Read by `<var_head>` above through `opt`, which is why the word
            // reduces to a mark and its absence to an `Empty`.
            // <gc_opt> -> ε
            156 => self.here(ASTNodeKind::Empty),
            // <gc_opt> -> gc
            157 => self.at(ASTNodeKind::Mark(ASTMark::Gc), c[0]),

            // ---- The optional semicolon ----------------------------------
            // Nothing above reads it: it is written for the grammar, which has
            // to say that it may be there.
            // <semi_opt> -> ε
            342 => self.here(ASTNodeKind::Empty),
            // <semi_opt> -> ;
            343 => self.at(ASTNodeKind::Empty, c[0]),

            // ---- What a `;` may be left off ------------------------------
            // <unterminated_decl> -> <var_head> | <const_head> | <type_head>
            //                     |  <import_head> | <fn_sig>
            395 | 396 | 397 | 398 | 399 => self.pass(c[0]),
            // <unterminated_stmt> -> <expression> | <var_head> | <const_head>
            //                     |  <type_head>
            400 | 401 | 402 | 403 => self.pass(c[0]),
            // <unterminated_stmt> -> unsafe <unterminated_stmt>
            404 => self.at(ASTNodeKind::Unsafe(c[1]), c[0]),

            _ => return None,
        })
    }
}
