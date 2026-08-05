//! Reading what the children hold, and finishing what was built without them.
//!
//! The vocabulary every arm of `build` is written in. Most of it is reading: a
//! child is a `List` to be taken apart, a `Mark` to be read back, a name to be
//! spelled out. The rest fills the holes -- a `<postfix_op>` is reduced before
//! the parse says what it is a suffix of, so it is built around a `HOLE` and
//! finished here.

use super::*;

impl Parser {
    // ---- Reading what the children hold ----------------------------------

    /// What a handle names, for a rule that has to look before it builds.
    pub(super) fn kind(&self, id: ASTNodeId) -> &ASTNodeKind {
        &self.get_node(id).kind
    }

    /// A node of `kind` standing where the child `anchor` stands. A node's
    /// position belongs to its leftmost child, not to the token in hand, which
    /// by now is the lookahead that ended the rule rather than anything in it.
    pub(super) fn at(&self, kind: ASTNodeKind, anchor: ASTNodeId) -> ASTNode {
        let anchored = self.get_node(anchor);
        ASTNode::new(kind, anchored.line, anchored.col)
    }

    /// A node of `kind` at the token in hand -- an ε rule's only choice, having
    /// no child to take a position from. Nothing built this way is ever pointed
    /// at: it is an empty list or an option that was not written, and a
    /// diagnostic reaching one would have nothing to say about it.
    pub(super) fn here(&self, kind: ASTNodeKind) -> ASTNode {
        ASTNode::at(kind, self.peek())
    }

    /// A child passed straight up, which is the whole of what a rule with one
    /// symbol and no meaning of its own does.
    pub(super) fn pass(&self, id: ASTNodeId) -> ASTNode {
        self.get_node(id).clone()
    }

    /// The handles a `List` gathered. An `Empty` is a list that was never
    /// written, which is the same list as one written empty.
    pub(super) fn list(&self, id: ASTNodeId) -> Vec<ASTNodeId> {
        match self.kind(id) {
            ASTNodeKind::List(ids) => ids.clone(),
            ASTNodeKind::Empty => Vec::new(),
            other => panic!("a list rule built {:?}", other),
        }
    }

    /// `id`, unless it stands for an `<..._opt>` that was not written.
    pub(super) fn opt(&self, id: ASTNodeId) -> Option<ASTNodeId> {
        match self.kind(id) {
            ASTNodeKind::Empty => None,
            _ => Some(id),
        }
    }

    /// A list of one, standing where that one does.
    pub(super) fn one(&self, item: ASTNodeId) -> ASTNode {
        self.at(ASTNodeKind::List(vec![item]), item)
    }

    /// A list with one more on the end. An empty list has nowhere of its own to
    /// stand, so the first item lends it a position.
    pub(super) fn grew(&self, list: ASTNodeId, item: ASTNodeId) -> ASTNode {
        let mut ids = self.list(list);
        let anchor = if ids.is_empty() { item } else { list };
        ids.push(item);
        self.at(ASTNodeKind::List(ids), anchor)
    }

    /// The spelling an `Ident` leaf carried.
    pub(super) fn text(&self, id: ASTNodeId) -> String {
        match self.kind(id) {
            ASTNodeKind::Ident(name) => name.clone(),
            other => panic!("a rule wanted a name and was given {:?}", other),
        }
    }

    /// The segments a `Name` gathered.
    pub(super) fn path(&self, id: ASTNodeId) -> Vec<String> {
        match self.kind(id) {
            ASTNodeKind::Name(segments) => segments.clone(),
            other => panic!("a rule wanted a path and was given {:?}", other),
        }
    }

    /// The value a `Literal` leaf carried, for a pattern, which keeps its
    /// literals by value rather than by handle.
    pub(super) fn lit(&self, id: ASTNodeId) -> ASTLit {
        match self.kind(id) {
            ASTNodeKind::Literal(value) => value.clone(),
            ASTNodeKind::LitPat { value, .. } => value.clone(),
            other => panic!("a rule wanted a literal and was given {:?}", other),
        }
    }

    /// The number an `INT_LITERAL` leaf carried, for the `.0` of a tuple. No
    /// negative one can reach here: the `-` in front of a literal is an
    /// operator of its own, and no rule puts one after a `.`.
    pub(super) fn index(&self, id: ASTNodeId) -> u64 {
        match self.kind(id) {
            ASTNodeKind::Literal(ASTLit::Int(n)) => *n as u64,
            other => panic!("a rule wanted an index and was given {:?}", other),
        }
    }

    /// The members of a tuple: the one in front of the comma, and the rest.
    /// A tuple is spelled that way so that `(x)` stays a grouping -- see
    /// <tuple_expr> -- and the tree keeps the one list they read as.
    pub(super) fn members(&self, first: ASTNodeId, rest: ASTNodeId) -> Vec<ASTNodeId> {
        let mut elems = vec![first];
        elems.extend(self.list(rest));
        elems
    }

    /// What a `<binding_name>` or a `<param_name>` binds.
    pub(super) fn binding(&self, id: ASTNodeId) -> ASTBinding {
        match self.kind(id) {
            ASTNodeKind::Ident(name) => ASTBinding::Name(name.clone()),
            ASTNodeKind::Wildcard => ASTBinding::Discard,
            ASTNodeKind::This => ASTBinding::This,
            other => panic!("a rule wanted a binding and was given {:?}", other),
        }
    }

    /// The word an `ASTMark` carried up.
    pub(super) fn mark(&self, id: ASTNodeId) -> ASTMark {
        match self.kind(id) {
            ASTNodeKind::Mark(mark) => *mark,
            other => panic!("a rule wanted a word and was given {:?}", other),
        }
    }

    /// What a `<visibility_opt>` said, which where it said nothing is not
    /// `Private`: unwritten is its own answer, and whose it is to settle is not
    /// the parser's. See section 9 of docs/prose.txt.
    pub(super) fn visibility(&self, id: ASTNodeId) -> ASTVisibility {
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
    pub(super) fn with_base(&self, suffix: ASTNodeId, base: ASTNodeId) -> ASTNode {
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
    pub(super) fn fold_suffixes(&mut self, base: ASTNodeId, suffixes: ASTNodeId) -> ASTNode {
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
    pub(super) fn with_attrs(&self, decl: ASTNodeId, attrs: ASTNodeId, vis: ASTVisibility) -> ASTNode {
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
    pub(super) fn with_modifier(&self, head: ASTNodeId, at: ASTNodeId, is_const: bool, is_unsafe: bool) -> ASTNode {
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
    pub(super) fn with_tail(&self, list: ASTNodeId, tail: ASTNodeId) -> Vec<ASTNodeId> {
        let mut members = self.list(list);
        if let Some(last) = self.opt(tail) {
            members.push(last);
        }
        members
    }
}
