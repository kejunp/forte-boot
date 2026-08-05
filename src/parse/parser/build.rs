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

/// Where a base belongs in a node built before its base was known. Handle 0 is
/// the arena's nothing-node, so a hole left unfilled is a node standing on
/// nothing rather than on the wrong thing.
const HOLE: ASTNodeId = 0;

/// The operator an `ASTMark` carried, and the same for the rest of the words.
/// Each panics where the mark is not the one the rule above it asked for: the
/// grammar settles which mark reaches which rule, so anything else is these
/// arms disagreeing with the tables, not a source being wrong.
fn bin_of(mark: ASTMark) -> ASTBinOp {
    match mark {
        ASTMark::Bin(op) => op,
        other => panic!("a binary rule was given {:?}", other),
    }
}

fn assign_of(mark: ASTMark) -> ASTAssignOp {
    match mark {
        ASTMark::Assign(op) => op,
        other => panic!("an assignment was given {:?}", other),
    }
}

fn unary_of(mark: ASTMark) -> ASTUnaryOp {
    match mark {
        ASTMark::Unary(op) => op,
        other => panic!("a unary rule was given {:?}", other),
    }
}

fn range_of(mark: ASTMark) -> ASTRangeOp {
    match mark {
        ASTMark::Range(op) => op,
        other => panic!("a range was given {:?}", other),
    }
}

fn ref_of(mark: ASTMark) -> ASTRefOp {
    match mark {
        ASTMark::Ref(op) => op,
        other => panic!("a reference was given {:?}", other),
    }
}

fn intro_of(mark: ASTMark) -> ASTVariableIntro {
    match mark {
        ASTMark::Intro(intro) => intro,
        other => panic!("a variable was introduced by {:?}", other),
    }
}

impl Parser {
    // ---- Reading what the children hold ----------------------------------

    /// What a handle names, for a rule that has to look before it builds.
    fn kind(&self, id: ASTNodeId) -> &ASTNodeKind {
        &self.get_node(id).kind
    }

    /// A node of `kind` standing where the child `anchor` stands. A node's
    /// position belongs to its leftmost child, not to the token in hand, which
    /// by now is the lookahead that ended the rule rather than anything in it.
    fn at(&self, kind: ASTNodeKind, anchor: ASTNodeId) -> ASTNode {
        let anchored = self.get_node(anchor);
        ASTNode::new(kind, anchored.line, anchored.col)
    }

    /// A node of `kind` at the token in hand -- an ε rule's only choice, having
    /// no child to take a position from. Nothing built this way is ever pointed
    /// at: it is an empty list or an option that was not written, and a
    /// diagnostic reaching one would have nothing to say about it.
    fn here(&self, kind: ASTNodeKind) -> ASTNode {
        ASTNode::at(kind, self.peek())
    }

    /// A child passed straight up, which is the whole of what a rule with one
    /// symbol and no meaning of its own does.
    fn pass(&self, id: ASTNodeId) -> ASTNode {
        self.get_node(id).clone()
    }

    /// The handles a `List` gathered. An `Empty` is a list that was never
    /// written, which is the same list as one written empty.
    fn list(&self, id: ASTNodeId) -> Vec<ASTNodeId> {
        match self.kind(id) {
            ASTNodeKind::List(ids) => ids.clone(),
            ASTNodeKind::Empty => Vec::new(),
            other => panic!("a list rule built {:?}", other),
        }
    }

    /// `id`, unless it stands for an `<..._opt>` that was not written.
    fn opt(&self, id: ASTNodeId) -> Option<ASTNodeId> {
        match self.kind(id) {
            ASTNodeKind::Empty => None,
            _ => Some(id),
        }
    }

    /// A list of one, standing where that one does.
    fn one(&self, item: ASTNodeId) -> ASTNode {
        self.at(ASTNodeKind::List(vec![item]), item)
    }

    /// A list with one more on the end. An empty list has nowhere of its own to
    /// stand, so the first item lends it a position.
    fn grew(&self, list: ASTNodeId, item: ASTNodeId) -> ASTNode {
        let mut ids = self.list(list);
        let anchor = if ids.is_empty() { item } else { list };
        ids.push(item);
        self.at(ASTNodeKind::List(ids), anchor)
    }

    /// The spelling an `Ident` leaf carried.
    fn text(&self, id: ASTNodeId) -> String {
        match self.kind(id) {
            ASTNodeKind::Ident(name) => name.clone(),
            other => panic!("a rule wanted a name and was given {:?}", other),
        }
    }

    /// The segments a `Name` gathered.
    fn path(&self, id: ASTNodeId) -> Vec<String> {
        match self.kind(id) {
            ASTNodeKind::Name(segments) => segments.clone(),
            other => panic!("a rule wanted a path and was given {:?}", other),
        }
    }

    /// The value a `Literal` leaf carried, for a pattern, which keeps its
    /// literals by value rather than by handle.
    fn lit(&self, id: ASTNodeId) -> ASTLit {
        match self.kind(id) {
            ASTNodeKind::Literal(value) => value.clone(),
            ASTNodeKind::LitPat { value, .. } => value.clone(),
            other => panic!("a rule wanted a literal and was given {:?}", other),
        }
    }

    /// The number an `INT_LITERAL` leaf carried, for the `.0` of a tuple. No
    /// negative one can reach here: the `-` in front of a literal is an
    /// operator of its own, and no rule puts one after a `.`.
    fn index(&self, id: ASTNodeId) -> u64 {
        match self.kind(id) {
            ASTNodeKind::Literal(ASTLit::Int(n)) => *n as u64,
            other => panic!("a rule wanted an index and was given {:?}", other),
        }
    }

    /// The members of a tuple: the one in front of the comma, and the rest.
    /// A tuple is spelled that way so that `(x)` stays a grouping -- see
    /// <tuple_expr> -- and the tree keeps the one list they read as.
    fn members(&self, first: ASTNodeId, rest: ASTNodeId) -> Vec<ASTNodeId> {
        let mut elems = vec![first];
        elems.extend(self.list(rest));
        elems
    }

    /// What a `<binding_name>` or a `<param_name>` binds.
    fn binding(&self, id: ASTNodeId) -> ASTBinding {
        match self.kind(id) {
            ASTNodeKind::Ident(name) => ASTBinding::Name(name.clone()),
            ASTNodeKind::Wildcard => ASTBinding::Discard,
            ASTNodeKind::This => ASTBinding::This,
            other => panic!("a rule wanted a binding and was given {:?}", other),
        }
    }

    /// The word an `ASTMark` carried up.
    fn mark(&self, id: ASTNodeId) -> ASTMark {
        match self.kind(id) {
            ASTNodeKind::Mark(mark) => *mark,
            other => panic!("a rule wanted a word and was given {:?}", other),
        }
    }

    /// What a `<visibility_opt>` said, which where it said nothing is not
    /// `Private`: unwritten is its own answer, and whose it is to settle is not
    /// the parser's. See section 9 of docs/prose.txt.
    fn visibility(&self, id: ASTNodeId) -> ASTVisibility {
        match self.kind(id) {
            ASTNodeKind::Empty => ASTVisibility::Unwritten,
            _ => match self.mark(id) {
                ASTMark::Vis(vis) => vis,
                other => panic!("a visibility rule built {:?}", other),
            },
        }
    }

    // ---- Filling the holes -----------------------------------------------

    /// A postfix with the expression it was written after put underneath it.
    ///
    /// The suffix was reduced first and knows nothing of its base, so it was
    /// built with `HOLE`; this is where `a.b`, `f(x)` and `a[i]` become whole.
    /// The node begins where the base does -- `shapes.Point { x: 1 }` starts at
    /// `shapes`, not at the brace.
    fn with_base(&self, suffix: ASTNodeId, base: ASTNodeId) -> ASTNode {
        let mut node = self.at(self.kind(suffix).clone(), base);
        match &mut node.kind {
            ASTNodeKind::Field { base: under, .. } => *under = base,
            ASTNodeKind::TupleIndex { base: under, .. } => *under = base,
            ASTNodeKind::Path { base: under, .. } => *under = base,
            ASTNodeKind::Call { callee, .. } => *callee = base,
            ASTNodeKind::Index { base: under, .. } => *under = base,
            ASTNodeKind::StructLit { base: under, .. } => *under = base,
            other => panic!("a postfix rule built {:?}", other),
        }
        node
    }

    /// `T[8][]` and the rest: each suffix in turn takes what is built so far as
    /// its element, so the one written first is the one bound tightest.
    ///
    /// The intermediates go in the arena as they are made, because the next
    /// suffix names its element by handle. The last is given back rather than
    /// pushed -- `reduce` pushes what `build` returns.
    fn fold_suffixes(&mut self, base: ASTNodeId, suffixes: ASTNodeId) -> ASTNode {
        let mut built = self.pass(base);
        let mut elem = base;
        for suffix in self.list(suffixes) {
            let mut node = self.at(self.kind(suffix).clone(), base);
            match &mut node.kind {
                ASTNodeKind::Array { elem: under, .. } => *under = elem,
                ASTNodeKind::Run(under) => *under = elem,
                other => panic!("an array suffix rule built {:?}", other),
            }
            elem = self.push_node(node.clone());
            built = node;
        }
        built
    }

    /// A declaration with the attributes and the visibility written in front of
    /// it put on it.
    ///
    /// The grammar lets those be written in four places and reduces the
    /// declaration before it has them; every declaration holds both, so this is
    /// one arm rather than eight. The node moves back to the first attribute
    /// when there is one, because that is where the declaration begins to a
    /// reader.
    fn with_attrs(&self, decl: ASTNodeId, attrs: ASTNodeId, vis: ASTVisibility) -> ASTNode {
        let written = self.list(attrs);
        let mut node = self.pass(decl);
        if !written.is_empty() {
            let first = self.get_node(attrs);
            node.line = first.line;
            node.col = first.col;
        }
        match &mut node.kind {
            ASTNodeKind::Fn { attrs: on, vis: seen, .. }
            | ASTNodeKind::Struct { attrs: on, vis: seen, .. }
            | ASTNodeKind::Enum { attrs: on, vis: seen, .. }
            | ASTNodeKind::Trait { attrs: on, vis: seen, .. }
            | ASTNodeKind::Impl { attrs: on, vis: seen, .. }
            | ASTNodeKind::Namespace { attrs: on, vis: seen, .. }
            | ASTNodeKind::Variable { attrs: on, vis: seen, .. }
            | ASTNodeKind::Const { attrs: on, vis: seen, .. } => {
                *on = written;
                *seen = vis;
            }
            other => panic!("attributes were written in front of {:?}", other),
        }
        node
    }

    /// A function signature with a modifier written in front of it. `const` and
    /// `unsafe` are the fn's own, not the head's, and the head is reduced
    /// before either is in hand.
    fn with_modifier(&self, head: ASTNodeId, at: ASTNodeId, is_const: bool, is_unsafe: bool) -> ASTNode {
        let mut node = self.at(self.kind(head).clone(), at);
        match &mut node.kind {
            ASTNodeKind::Fn { is_const: c, is_unsafe: u, .. } => {
                *c = *c || is_const;
                *u = *u || is_unsafe;
            }
            other => panic!("a modifier was written in front of {:?}", other),
        }
        node
    }

    /// A list with what a `<..._tail_opt>` held on the end of it. A body's last
    /// member may be written without the `;` that ends the others, and the
    /// grammar has to spell that as a rule of its own; the tree does not.
    fn with_tail(&self, list: ASTNodeId, tail: ASTNodeId) -> Vec<ASTNodeId> {
        let mut members = self.list(list);
        if let Some(last) = self.opt(tail) {
            members.push(last);
        }
        members
    }

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

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses `source` and gives back the parser -- which is the arena -- and
    /// the root. A tree is the two together: a node names its children by
    /// handle, so neither half says anything alone.
    fn tree(source: &str) -> (Parser, ASTNode) {
        let mut p = Parser::new(lexer::Lexer::new(source));
        let root = p.parse();
        assert!(p.errors().is_empty(), "{}\n{:#?}", source, p.errors());
        (p, root)
    }

    /// The one item of a file that has one.
    fn only_item(source: &str) -> (Parser, ASTNode) {
        let (p, root) = tree(source);
        let items = match &root.kind {
            ASTNodeKind::Program(items) => items.clone(),
            other => panic!("a file built {:?}", other),
        };
        assert_eq!(items.len(), 1, "{}", source);
        let item = p.get_node(items[0]).clone();
        (p, item)
    }

    /// The statements of `fn main`'s body, for a test about statements rather
    /// than about what has to be written around them.
    fn statements(body: &str) -> (Parser, Vec<ASTNodeId>) {
        let source = format!("fn main() {{\n{}\n}}\n", body);
        let (p, item) = only_item(&source);
        let block = match &item.kind {
            ASTNodeKind::Fn { body: Some(id), .. } => *id,
            other => panic!("a function built {:?}", other),
        };
        let stmts = match &p.get_node(block).kind {
            ASTNodeKind::Block { stmts, .. } => stmts.clone(),
            other => panic!("a body built {:?}", other),
        };
        (p, stmts)
    }

    #[test]
    fn a_file_is_its_items_in_order() {
        let (p, root) = tree("import a::b;\nstruct P {\n    x: i32,\n}\nfn f() {}\n");
        let items = match &root.kind {
            ASTNodeKind::Program(items) => items.clone(),
            other => panic!("a file built {:?}", other),
        };
        assert_eq!(items.len(), 3);
        assert!(matches!(p.get_node(items[0]).kind, ASTNodeKind::Import { .. }));
        assert!(matches!(p.get_node(items[1]).kind, ASTNodeKind::Struct { .. }));
        assert!(matches!(p.get_node(items[2]).kind, ASTNodeKind::Fn { .. }));
    }

    #[test]
    fn an_import_keeps_its_path_and_its_alias() {
        let (_, item) = only_item("import shapes::circle as c;\n");
        match &item.kind {
            ASTNodeKind::Import { path, alias } => {
                assert_eq!(path, &["shapes", "circle"]);
                assert_eq!(alias.as_deref(), Some("c"));
            }
            other => panic!("{:?}", other),
        }
        let (_, bare) = only_item("import shapes;\n");
        match &bare.kind {
            ASTNodeKind::Import { path, alias } => {
                assert_eq!(path, &["shapes"]);
                assert_eq!(alias, &None);
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn precedence_is_spent_on_the_shape() {
        // `1 + 2 * 3` is an add whose right side is the multiply.
        let (p, stmts) = statements("    1 + 2 * 3;");
        let expr = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{:?}", other),
        };
        match &p.get_node(expr).kind {
            ASTNodeKind::Binary { op, lhs, rhs } => {
                assert_eq!(*op, ASTBinOp::Add);
                assert_eq!(p.get_node(*lhs).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
                match &p.get_node(*rhs).kind {
                    ASTNodeKind::Binary { op, .. } => assert_eq!(*op, ASTBinOp::Mul),
                    other => panic!("{:?}", other),
                }
            }
            other => panic!("{:?}", other),
        }
    }

    /// The bitwise pair, and where they sit among the rest: tighter than a
    /// comparison and looser than a shift, so the reading everyone means is
    /// the one the tree has.
    #[test]
    fn the_bitwise_operators_bind_between_a_shift_and_a_comparison() {
        let binary = |p: &Parser, id: ASTNodeId| match &p.get_node(id).kind {
            ASTNodeKind::Binary { op, lhs, rhs } => (*op, *lhs, *rhs),
            other => panic!("{:?}", other),
        };
        let expr = |p: &Parser, stmts: &[ASTNodeId]| match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{:?}", other),
        };

        // `a & b` is one operator and not two references, and `a | b` is
        // neither a closure nor a pattern's alternatives.
        let (p, stmts) = statements("    a & b;");
        let (op, lhs, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::BitAnd);
        assert_eq!(p.get_node(lhs).kind, ASTNodeKind::Ident("a".to_string()));
        assert_eq!(p.get_node(rhs).kind, ASTNodeKind::Ident("b".to_string()));

        let (p, stmts) = statements("    a | b;");
        assert_eq!(binary(&p, expr(&p, &stmts)).0, ASTBinOp::BitOr);

        let (p, stmts) = statements("    a ^ b;");
        assert_eq!(binary(&p, expr(&p, &stmts)).0, ASTBinOp::BitXor);

        // `&` binds tighter than `^`, and `^` tighter than `|`, so
        // `a | b ^ c & d` nests the whole ladder to the right.
        let (p, stmts) = statements("    a | b ^ c & d;");
        let (op, _, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::BitOr);
        let (op, _, rhs) = binary(&p, rhs);
        assert_eq!(op, ASTBinOp::BitXor);
        assert_eq!(binary(&p, rhs).0, ASTBinOp::BitAnd);

        // Tighter than a comparison, which is the whole point of putting them
        // here: `a & mask == 0` is `(a & mask) == 0`, not C's reading.
        let (p, stmts) = statements("    a & mask == 0;");
        let (op, lhs, _) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::Eq);
        assert_eq!(binary(&p, lhs).0, ASTBinOp::BitAnd);

        // Looser than a shift: `a | b << c` is `a | (b << c)`.
        let (p, stmts) = statements("    a | b << c;");
        let (op, _, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::BitOr);
        assert_eq!(binary(&p, rhs).0, ASTBinOp::Shl);

        // Looser than the logical pair is `&&`'s side of it: `a && b | c` is
        // `a && (b | c)`.
        let (p, stmts) = statements("    a && b | c;");
        let (op, _, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::And);
        assert_eq!(binary(&p, rhs).0, ASTBinOp::BitOr);

        // The logical three are the same ladder over booleans: `&&` tightest,
        // then `^^`, then `||`. `a || b ^^ c && d` nests the same way.
        let (p, stmts) = statements("    a || b ^^ c && d;");
        let (op, _, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::Or);
        let (op, _, rhs) = binary(&p, rhs);
        assert_eq!(op, ASTBinOp::Xor);
        assert_eq!(binary(&p, rhs).0, ASTBinOp::And);

        // `^^` is looser than every bitwise one, `^` included: the bits are
        // worked out before the booleans are.
        let (p, stmts) = statements("    a ^^ b ^ c;");
        let (op, _, rhs) = binary(&p, expr(&p, &stmts));
        assert_eq!(op, ASTBinOp::Xor);
        assert_eq!(binary(&p, rhs).0, ASTBinOp::BitXor);

        // Left-associative, as every other binary here is.
        for (source, op) in [
            ("    a & b & c;", ASTBinOp::BitAnd),
            ("    a | b | c;", ASTBinOp::BitOr),
            ("    a ^ b ^ c;", ASTBinOp::BitXor),
            ("    a ^^ b ^^ c;", ASTBinOp::Xor),
        ] {
            let (p, stmts) = statements(source);
            let (found, lhs, _) = binary(&p, expr(&p, &stmts));
            assert_eq!(found, op, "{}", source);
            assert_eq!(binary(&p, lhs).0, op, "{}", source);
        }
    }

    /// Every compound assignment reaches the tree as the operator it names.
    /// `^=` is the newest of them and the one the grammar was missing.
    #[test]
    fn a_compound_assignment_carries_its_operator() {
        for (source, op) in [
            ("    a = b;", ASTAssignOp::Set),
            ("    a += b;", ASTAssignOp::Add),
            ("    a &= b;", ASTAssignOp::And),
            ("    a |= b;", ASTAssignOp::Or),
            ("    a ^= b;", ASTAssignOp::Xor),
            ("    a <<= b;", ASTAssignOp::Shl),
            ("    a >>= b;", ASTAssignOp::Shr),
        ] {
            let (p, stmts) = statements(source);
            let expr = match &p.get_node(stmts[0]).kind {
                ASTNodeKind::ExprStmt(id) => *id,
                other => panic!("{}: {:?}", source, other),
            };
            match &p.get_node(expr).kind {
                ASTNodeKind::Assign { op: found, .. } => assert_eq!(*found, op, "{}", source),
                other => panic!("{}: {:?}", source, other),
            }
        }
    }

    #[test]
    fn a_postfix_takes_everything_to_its_left() {
        // `a.b(c)` is a call of a field, not a field of a call.
        let (p, stmts) = statements("    a.b(c);");
        let expr = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{:?}", other),
        };
        let callee = match &p.get_node(expr).kind {
            ASTNodeKind::Call { callee, args } => {
                assert_eq!(args.len(), 1);
                *callee
            }
            other => panic!("{:?}", other),
        };
        match &p.get_node(callee).kind {
            ASTNodeKind::Field { base, name } => {
                assert_eq!(name, "b");
                assert_eq!(p.get_node(*base).kind, ASTNodeKind::Ident("a".to_string()));
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_declaration_carries_what_was_written_in_front_of_it() {
        let (p, item) = only_item("@repr(C)\npublic const unsafe fn f(x: i32): i32 {\n    x\n}\n");
        match &item.kind {
            ASTNodeKind::Fn { attrs, vis, is_const, is_unsafe, name, params, ret, .. } => {
                assert_eq!(attrs.len(), 1);
                assert_eq!(*vis, ASTVisibility::Public);
                assert!(*is_const && *is_unsafe);
                assert_eq!(name, "f");
                assert_eq!(params.len(), 1);
                assert!(ret.is_some());
                match &p.get_node(attrs[0]).kind {
                    ASTNodeKind::Attr { name, args } => {
                        assert_eq!(name, "repr");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("{:?}", other),
                }
            }
            other => panic!("{:?}", other),
        }
        // The declaration begins at its first attribute, not at `public`.
        assert_eq!((item.line, item.col), (1, 1));
    }

    #[test]
    fn a_signature_without_a_body_has_none() {
        let (p, item) = only_item("trait Show {\n    fn show(this): str;\n}\n");
        let members = match &item.kind {
            ASTNodeKind::Trait { members, .. } => members.clone(),
            other => panic!("{:?}", other),
        };
        assert_eq!(members.len(), 1);
        match &p.get_node(members[0]).kind {
            ASTNodeKind::Fn { body, params, .. } => {
                assert!(body.is_none());
                assert_eq!(params.len(), 1);
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_type_is_read_from_the_inside_out() {
        // `x: i32[8][]` is a run of arrays of 8.
        let (p, stmts) = statements("    let x: i32[8][] = y;");
        let ty = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::Variable { ty: Some(id), intro, .. } => {
                assert_eq!(*intro, ASTVariableIntro::Let);
                *id
            }
            other => panic!("{:?}", other),
        };
        let elem = match &p.get_node(ty).kind {
            ASTNodeKind::Run(elem) => *elem,
            other => panic!("{:?}", other),
        };
        match &p.get_node(elem).kind {
            ASTNodeKind::Array { elem, .. } => {
                assert_eq!(p.get_node(*elem).kind, ASTNodeKind::Prim(ASTPrimType::I32));
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_tuple_keeps_its_members_in_order() {
        // The type, the literal and the `.0` that reaches into one. Each holds
        // the members the comma separated, and the first of them is no
        // different from the rest for having stood in front of it.
        let (p, item) = only_item("fn pair(): (i32, str) {\n    (1, \"a\").0\n}\n");
        let (ret, body) = match &item.kind {
            ASTNodeKind::Fn { ret: Some(ret), body: Some(body), .. } => (*ret, *body),
            other => panic!("{:?}", other),
        };
        match &p.get_node(ret).kind {
            ASTNodeKind::TupleType(members) => {
                assert_eq!(members.len(), 2);
                assert_eq!(p.get_node(members[0]).kind, ASTNodeKind::Prim(ASTPrimType::I32));
                assert_eq!(p.get_node(members[1]).kind, ASTNodeKind::Prim(ASTPrimType::Str));
            }
            other => panic!("{:?}", other),
        }
        let tail = match &p.get_node(body).kind {
            ASTNodeKind::Block { tail: Some(id), .. } => *id,
            other => panic!("{:?}", other),
        };
        let base = match &p.get_node(tail).kind {
            ASTNodeKind::TupleIndex { base, index } => {
                assert_eq!(*index, 0);
                *base
            }
            other => panic!("{:?}", other),
        };
        match &p.get_node(base).kind {
            ASTNodeKind::TupleLit(members) => {
                assert_eq!(members.len(), 2);
                assert_eq!(p.get_node(members[0]).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
            }
            other => panic!("{:?}", other),
        }
        // A group of one is still a group: the parentheses leave no node.
        let (p, stmts) = statements("    let x = (1);");
        match &p.get_node(stmts[0]).kind {
            ASTNodeKind::Variable { init: Some(id), .. } => {
                assert_eq!(p.get_node(*id).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_tuple_pattern_is_a_variant_pattern_with_no_name() {
        let (p, stmts) = statements("    match p {\n        (0, y) => y,\n        _ => 0,\n    };");
        let expr = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{:?}", other),
        };
        let arms = match &p.get_node(expr).kind {
            ASTNodeKind::Match { arms, .. } => arms.clone(),
            other => panic!("{:?}", other),
        };
        let pats = match &p.get_node(arms[0]).kind {
            ASTNodeKind::MatchArm { pats, .. } => pats.clone(),
            other => panic!("{:?}", other),
        };
        match &p.get_node(pats[0]).kind {
            ASTNodeKind::TuplePat(elems) => {
                assert_eq!(elems.len(), 2);
                match &p.get_node(elems[0]).kind {
                    ASTNodeKind::LitPat { negated, value } => {
                        assert!(!negated);
                        assert_eq!(*value, ASTLit::Int(0));
                    }
                    other => panic!("{:?}", other),
                }
                // A bare name is a `Name`: whether it binds is not the
                // parser's to say.
                assert_eq!(p.get_node(elems[1]).kind, ASTNodeKind::Name(vec!["y".to_string()]));
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_block_tells_its_tail_from_its_statements() {
        let (p, item) = only_item("fn f(): i32 {\n    g();\n    1\n}\n");
        let block = match &item.kind {
            ASTNodeKind::Fn { body: Some(id), .. } => *id,
            other => panic!("{:?}", other),
        };
        match &p.get_node(block).kind {
            ASTNodeKind::Block { stmts, tail } => {
                assert_eq!(stmts.len(), 1);
                let tail = tail.expect("the last expression is the block's value");
                assert_eq!(p.get_node(tail).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_match_keeps_its_arms_and_their_alternatives() {
        let (p, stmts) = statements("    match x {\n        1 | 2 => a,\n        _ => b,\n    };");
        let expr = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{:?}", other),
        };
        let arms = match &p.get_node(expr).kind {
            ASTNodeKind::Match { arms, .. } => arms.clone(),
            other => panic!("{:?}", other),
        };
        assert_eq!(arms.len(), 2);
        match &p.get_node(arms[0]).kind {
            ASTNodeKind::MatchArm { pats, .. } => assert_eq!(pats.len(), 2),
            other => panic!("{:?}", other),
        }
        match &p.get_node(arms[1]).kind {
            ASTNodeKind::MatchArm { pats, .. } => {
                assert_eq!(p.get_node(pats[0]).kind, ASTNodeKind::Wildcard);
            }
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn a_node_stands_where_it_was_written() {
        let (p, stmts) = statements("    let x = 1;\n    y = 2;");
        // Line 1 is the `fn`, so the statements are on 2 and 3.
        assert_eq!(p.get_node(stmts[0]).line, 2);
        assert_eq!(p.get_node(stmts[0]).col, 5);
        assert_eq!(p.get_node(stmts[1]).line, 3);
    }

    #[test]
    fn nothing_a_finished_tree_holds_is_scaffolding() {
        // Every node the root can reach is a node of the language: no `ASTMark`
        // survived the rule that took its word, and no hole was left unfilled.
        let source = "import a::b as c;\n\
                      @attr(1)\n\
                      public fn f<T: Ord>(this, x: *i32[2]): (bool, i32) {\n\
                          let y = -x.a as i64 .. 3;\n\
                          let t: (i32, str) = (1, \"a\");\n\
                          let u = t.1;\n\
                          if y { g(#{1: 2}, {,}, [1]) } else { move |z| z + 1 };\n\
                          while y { continue }\n\
                          for i in 0..=9 { break }\n\
                          match x {\n\
                              1..=2 => a,\n\
                              -3 => b,\n\
                              P::Q(m) => m,\n\
                              (m, _) => m,\n\
                              P { n: o } => o,\n\
                              _ => return,\n\
                          }\n\
                      }\n\
                      namespace n {\n\
                          const K: i32 = 1;\n\
                          enum E { A, B(i32), C { x: i32 }, D = 4 }\n\
                          struct S<T> { private v: T[] }\n\
                          trait W { fn w<T>(this, t: T): str where T: Ord; }\n\
                          impl W for S<i32> { private fn w(this): str { P { r: 1 } } }\n\
                      }\n";
        let (p, root) = tree(source);
        let mut seen = vec![false; p.nodes.len()];
        let mut stack = vec![0usize];
        // The root itself is not in the arena under a handle of its own --
        // `parse` gives back a copy -- so it is walked from here.
        let mut walk = vec![root.kind.clone()];
        while let Some(kind) = walk.pop() {
            assert!(
                !matches!(kind, ASTNodeKind::Mark(_)),
                "a mark reached the tree: {:?}",
                kind
            );
            for child in children_of(&kind) {
                assert_ne!(child, HOLE, "a hole was left unfilled in {:?}", kind);
                if !seen[child] {
                    seen[child] = true;
                    stack.push(child);
                    walk.push(p.get_node(child).kind.clone());
                }
            }
        }
        assert!(stack.len() > 1, "the walk found nothing");
    }

    #[test]
    fn a_recovered_parse_still_builds_a_tree() {
        // Recovery cuts the stack back to a state that can go on, and every
        // entry left is still the state a symbol was reached by and the node
        // that symbol built -- so the reductions after one take the children
        // their rules call for, and `build` never sees a stack it cannot read.
        for source in [
            "fn a() { let x = ; }\nfn b() { g(] }\nfn c() {}\n",
            "fn f(x: ) {}\nstruct S { y: i32, }\n",
            "fn main() {\n    f(1, 2\n}\n",
            "fn main() {\n    match x {\n        1 => ,\n    }\n}\n",
        ] {
            let mut p = Parser::new(lexer::Lexer::new(source));
            let root = p.parse();
            assert!(!p.errors().is_empty(), "{}", source);
            // Whatever it built, it is a file or the `Empty` a parse that could
            // not recover gives back -- never a half-built rule.
            assert!(
                matches!(root.kind, ASTNodeKind::Program(_) | ASTNodeKind::Empty),
                "{} built {:?}",
                source,
                root.kind
            );
        }
    }

    /// Every handle a node names. One arm per kind that holds any, so that a
    /// kind added to the tree is not walked past in silence.
    fn children_of(kind: &ASTNodeKind) -> Vec<ASTNodeId> {
        let mut out = Vec::new();
        match kind {
            ASTNodeKind::Program(ids)
            | ASTNodeKind::List(ids)
            | ASTNodeKind::ArrayLit(ids)
            | ASTNodeKind::TupleLit(ids)
            | ASTNodeKind::TupleType(ids)
            | ASTNodeKind::TuplePat(ids)
            | ASTNodeKind::TuplePayload(ids)
            | ASTNodeKind::NamedPayload(ids) => out.extend_from_slice(ids),
            ASTNodeKind::Fn { attrs, generics, params, ret, wheres, body, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(generics);
                out.extend_from_slice(params);
                out.extend_from_slice(wheres);
                out.extend(ret.iter().chain(body.iter()));
            }
            ASTNodeKind::Struct { attrs, generics, fields, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(generics);
                out.extend_from_slice(fields);
            }
            ASTNodeKind::Enum { attrs, generics, variants, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(generics);
                out.extend_from_slice(variants);
            }
            ASTNodeKind::Trait { attrs, generics, members, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(generics);
                out.extend_from_slice(members);
            }
            ASTNodeKind::Impl { attrs, generics, ty, for_ty, wheres, members, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(generics);
                out.extend_from_slice(wheres);
                out.extend_from_slice(members);
                out.push(*ty);
                out.extend(for_ty.iter());
            }
            ASTNodeKind::Namespace { attrs, items, .. } => {
                out.extend_from_slice(attrs);
                out.extend_from_slice(items);
            }
            ASTNodeKind::Variable { attrs, ty, init, .. } => {
                out.extend_from_slice(attrs);
                out.extend(ty.iter().chain(init.iter()));
            }
            ASTNodeKind::Const { attrs, ty, value, .. } => {
                out.extend_from_slice(attrs);
                out.push(*ty);
                out.push(*value);
            }
            ASTNodeKind::Attr { args, .. } => out.extend_from_slice(args),
            ASTNodeKind::Param { ty, .. } => out.extend(ty.iter()),
            ASTNodeKind::FieldDecl { attrs, ty, .. } => {
                out.extend_from_slice(attrs);
                out.push(*ty);
            }
            ASTNodeKind::EnumVariant { attrs, body, .. } => {
                out.extend_from_slice(attrs);
                out.extend(body.iter());
            }
            ASTNodeKind::Discriminant(id)
            | ASTNodeKind::Run(id)
            | ASTNodeKind::ExprStmt(id)
            | ASTNodeKind::Unsafe(id) => out.push(*id),
            ASTNodeKind::GenericParam { bounds, .. } => out.extend_from_slice(bounds),
            ASTNodeKind::WherePred { ty, bounds } => {
                out.push(*ty);
                out.extend_from_slice(bounds);
            }
            ASTNodeKind::RefType { inner, .. } => out.push(*inner),
            ASTNodeKind::Array { elem, len } => {
                out.push(*elem);
                out.push(*len);
            }
            ASTNodeKind::Named { args, .. } => out.extend_from_slice(args),
            ASTNodeKind::Map { entries, .. } => out.extend_from_slice(entries),
            ASTNodeKind::Set { elems, .. } => out.extend_from_slice(elems),
            ASTNodeKind::MapEntry { key, value } => {
                out.push(*key);
                out.push(*value);
            }
            ASTNodeKind::Field { base, .. }
            | ASTNodeKind::TupleIndex { base, .. }
            | ASTNodeKind::Path { base, .. } => out.push(*base),
            ASTNodeKind::Call { callee, args } => {
                out.push(*callee);
                out.extend_from_slice(args);
            }
            ASTNodeKind::Index { base, index } => {
                out.push(*base);
                out.push(*index);
            }
            ASTNodeKind::StructLit { base, fields } => {
                out.push(*base);
                out.extend_from_slice(fields);
            }
            ASTNodeKind::FieldInit { value, .. } => out.push(*value),
            ASTNodeKind::Unary { operand, .. } => out.push(*operand),
            ASTNodeKind::Binary { lhs, rhs, .. } => {
                out.push(*lhs);
                out.push(*rhs);
            }
            ASTNodeKind::Assign { target, value, .. } => {
                out.push(*target);
                out.push(*value);
            }
            ASTNodeKind::Range { start, end, .. } => out.extend(start.iter().chain(end.iter())),
            ASTNodeKind::Cast { value, ty } => {
                out.push(*value);
                out.push(*ty);
            }
            ASTNodeKind::Closure { params, body, .. } => {
                out.extend_from_slice(params);
                out.push(*body);
            }
            ASTNodeKind::Block { stmts, tail } => {
                out.extend_from_slice(stmts);
                out.extend(tail.iter());
            }
            ASTNodeKind::If { cond, then, elifs, else_block } => {
                out.push(*cond);
                out.push(*then);
                out.extend_from_slice(elifs);
                out.extend(else_block.iter());
            }
            ASTNodeKind::Elif { cond, block } => {
                out.push(*cond);
                out.push(*block);
            }
            ASTNodeKind::While { cond, body } => {
                out.push(*cond);
                out.push(*body);
            }
            ASTNodeKind::For { iter, body, .. } => {
                out.push(*iter);
                out.push(*body);
            }
            ASTNodeKind::Match { scrutinee, arms } => {
                out.push(*scrutinee);
                out.extend_from_slice(arms);
            }
            ASTNodeKind::MatchArm { pats, body } => {
                out.extend_from_slice(pats);
                out.push(*body);
            }
            ASTNodeKind::Return(id) | ASTNodeKind::Break(id) => out.extend(id.iter()),
            ASTNodeKind::RangePat { lo, hi, .. } => {
                out.push(*lo);
                out.push(*hi);
            }
            ASTNodeKind::VariantPat { elems, .. } => out.extend_from_slice(elems),
            ASTNodeKind::StructPat { fields, .. } => out.extend_from_slice(fields),
            ASTNodeKind::FieldPat { pat, .. } => out.extend(pat.iter()),
            // The leaves, and the scaffolding that names nothing.
            ASTNodeKind::Empty
            | ASTNodeKind::Mark(_)
            | ASTNodeKind::Import { .. }
            | ASTNodeKind::Prim(_)
            | ASTNodeKind::Infer
            | ASTNodeKind::Literal(_)
            | ASTNodeKind::Ident(_)
            | ASTNodeKind::This
            | ASTNodeKind::Name(_)
            | ASTNodeKind::Continue
            | ASTNodeKind::Wildcard
            | ASTNodeKind::LitPat { .. } => {}
        }
        out
    }
}
