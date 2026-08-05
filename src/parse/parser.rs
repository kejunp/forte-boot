use super::ast_nodes::ASTNodeId;
use super::{ast_nodes, tables};
use crate::error::{Diagnostic, Diagnostics, Span};
use crate::lex::*;

// `build` is one arm per rule of the grammar, and long enough to crowd out the
// automaton it serves; it lives next door. A child module, so that it reaches
// the arena and the stack the same way the rest of `Parser` does.
mod build;

pub struct Parser {
    lexer: lexer::Lexer,
    nodes: Vec<ast_nodes::ASTNode>, // the arena: every node of the tree, side by side
    stack: Vec<(tables::State, ASTNodeId)>, // what has been read, and what it built
    current: tokens::Tok,
    /// The openers gone past and not yet closed, each with the depth the stack
    /// stood at when it went by, so that a recovery which throws away part of
    /// the stack throws away what was opened inside it too.
    open: Vec<(tokens::Tok, usize)>,
    /// What the parse has turned down, in the order it did. A parse that
    /// recovers has more than one, and all of them are worth showing.
    errors: Diagnostics,
    /// How many tokens the parse has taken since the last error it reported.
    /// A recovery leaves the parse somewhere it can go on from, not somewhere
    /// it belongs, so the tokens just after one draw errors of the recovery's
    /// making. See `report` and `SETTLED`.
    taken: usize,
}

/// Where a token was written: what a diagnostic points at.
fn span_of(tok: &tokens::Tok) -> Span {
    Span::new(tok.line, tok.col, tok.len)
}

/// The closer that mates an opener. Both kinds of `{` close with the same `}`:
/// which one it opened is the lexer's to know and not the reader's to write.
fn closer_of(opener: tables::Terminal) -> Option<tables::Terminal> {
    match opener {
        tables::Terminal::LParen => Some(tables::Terminal::RParen),
        tables::Terminal::LBracket => Some(tables::Terminal::RBracket),
        tables::Terminal::LCurlyBracket | tables::Terminal::LCurlyValue => {
            Some(tables::Terminal::RCurlyBracket)
        }
        _ => None,
    }
}

/// How a delimiter is written, for a note that has already said what it is
/// doing. `tables::name_of` tells the two `{` apart because a message about
/// what was wanted has to; one about what is still open has the opener's own
/// position to point at, and the longer name only gets in the way.
fn spelling_of(delimiter: tables::Terminal) -> &'static str {
    match delimiter {
        tables::Terminal::LParen => "`(`",
        tables::Terminal::LBracket => "`[`",
        tables::Terminal::LCurlyBracket | tables::Terminal::LCurlyValue => "`{`",
        other => tables::name_of(other),
    }
}

/// Near-misses worth naming outright: a terminal that was written, one that
/// was wanted, and what the difference between them is.
///
/// `expected .., found ..` is true of every error and says what, not why. These
/// are the pairs where the why is a rule of the language rather than a slip of
/// the finger, and where a reader looking at the two spellings would not see
/// it: the message has to say it.
const HINTS: &[(tables::Terminal, tables::Terminal, &str)] = &[
    (
        tables::Terminal::Equals,
        tables::Terminal::EqualsEquals,
        "`=` assigns; use `==` to compare",
    ),
    (
        tables::Terminal::EqualsEquals,
        tables::Terminal::Equals,
        "`==` compares; use `=` to assign",
    ),
    (
        tables::Terminal::Dot,
        tables::Terminal::ColonColon,
        "use `::` to name a path; `.` accesses a member",
    ),
    (
        tables::Terminal::ColonColon,
        tables::Terminal::Dot,
        "use `.` to access a member; `::` names a path",
    ),
    (
        tables::Terminal::Semicolon,
        tables::Terminal::Comma,
        "use `,` to separate entries",
    ),
    (
        tables::Terminal::DotDot,
        tables::Terminal::DotDotEquals,
        "`..` excludes its upper bound; use `..=` to include it",
    ),
    // The lexer has already decided which kind of `{` this is, so a state that
    // wanted the other kind is not asking for a different character.
    (
        tables::Terminal::LCurlyValue,
        tables::Terminal::LCurlyBracket,
        "this `{` opens a value literal, but a block is expected here; \
         parenthesise the literal to use one",
    ),
    (
        tables::Terminal::LCurlyBracket,
        tables::Terminal::LCurlyValue,
        "this `{` opens a block, but a value literal is expected here; an \
         empty map is written `{}` and an empty set `{,}`",
    ),
];

/// What a token becomes on the stack, so that a rule taking it can still reach
/// what it said. Only five token kinds carry a spelling, and each has the leaf
/// it will end up as; the rest are their own spelling, and a node of one would
/// hold nothing a reader could not read off the rule.
///
/// The leaf is what the token *is*, not what its rule makes of it: a `null` is
/// a literal here even where a type wanted `Prim(Null)`, and an `_` a wildcard
/// even where a binding wanted `Discard`. Turning one into the other is
/// `build`'s, which is the only place that knows which rule fired.
fn leaf_of(toktype: &tokens::TokType) -> ast_nodes::ASTNodeKind {
    use ast_nodes::{ASTLit, ASTNodeKind, ASTPrimType};
    match toktype {
        tokens::TokType::Identifier(name) => ASTNodeKind::Ident(name.clone()),
        tokens::TokType::IntLiteral(n) => ASTNodeKind::Literal(ASTLit::Int(*n)),
        tokens::TokType::FloatLiteral(f) => ASTNodeKind::Literal(ASTLit::Float(*f)),
        tokens::TokType::StringLiteral(s) => ASTNodeKind::Literal(ASTLit::Str(s.clone())),
        tokens::TokType::CharLiteral(c) => ASTNodeKind::Literal(ASTLit::Char(*c)),

        tokens::TokType::True => ASTNodeKind::Literal(ASTLit::Bool(true)),
        tokens::TokType::False => ASTNodeKind::Literal(ASTLit::Bool(false)),
        tokens::TokType::Null => ASTNodeKind::Literal(ASTLit::Null),
        tokens::TokType::This => ASTNodeKind::This,
        tokens::TokType::Underscore => ASTNodeKind::Wildcard,

        tokens::TokType::I8 => ASTNodeKind::Prim(ASTPrimType::I8),
        tokens::TokType::I16 => ASTNodeKind::Prim(ASTPrimType::I16),
        tokens::TokType::I32 => ASTNodeKind::Prim(ASTPrimType::I32),
        tokens::TokType::I64 => ASTNodeKind::Prim(ASTPrimType::I64),
        tokens::TokType::U8 => ASTNodeKind::Prim(ASTPrimType::U8),
        tokens::TokType::U16 => ASTNodeKind::Prim(ASTPrimType::U16),
        tokens::TokType::U32 => ASTNodeKind::Prim(ASTPrimType::U32),
        tokens::TokType::U64 => ASTNodeKind::Prim(ASTPrimType::U64),
        tokens::TokType::F32 => ASTNodeKind::Prim(ASTPrimType::F32),
        tokens::TokType::F64 => ASTNodeKind::Prim(ASTPrimType::F64),
        tokens::TokType::Bool => ASTNodeKind::Prim(ASTPrimType::Bool),
        tokens::TokType::Char => ASTNodeKind::Prim(ASTPrimType::Char),
        tokens::TokType::Str => ASTNodeKind::Prim(ASTPrimType::Str),
        tokens::TokType::Never => ASTNodeKind::Prim(ASTPrimType::Never),

        // A keyword, a delimiter, an operator: the rule it belongs to is the
        // whole of what it says, and the position is all a parent wants of it.
        _ => ASTNodeKind::Empty,
    }
}

/// How many tokens a parse has to take after an error before it is trusted to
/// report another. Yacc's number, and for yacc's reason: a recovery puts the
/// parse somewhere it can carry on from rather than where the source meant it
/// to be, and what it makes of the next token or two says more about where it
/// landed than about the source.
const SETTLED: usize = 3;

/// The terminals a recovering parse looks for. Both end something whole -- a
/// statement, a block -- so what follows one is a place the parse can be in
/// again, rather than the middle of whatever went wrong.
const SYNC: &[tables::Terminal] = &[
    tables::Terminal::Semicolon,
    tables::Terminal::RCurlyBracket,
];

impl Parser {
    /// A parser over `lexer_in`.
    ///
    /// It is handed a lexer and nothing else. What the source is called and
    /// what it says are the caller's -- a diagnostic carries a `Span` and the
    /// caller turns that into a quoted line, which is the only arrangement
    /// where a phase reading a preprocessed source cannot quote one back. See
    /// `errors`.
    pub fn new(mut lexer_in: lexer::Lexer) -> Self {
        // The first token is read before the lexer is handed over, because
        // afterward it is only reachable through the parser.
        let current = lexer_in.next_token();
        Parser {
            lexer: lexer_in,
            // Handle 0 is spent on a node that stands for nothing, so that the
            // start state below can hold a handle like any other entry rather
            // than an index into an arena that has no such node.
            nodes: vec![ast_nodes::ASTNode::new(ast_nodes::ASTNodeKind::Empty, 0, 0)],
            stack: vec![(tables::State::default(), 0)],
            current,
            open: Vec::new(),
            errors: Diagnostics::new(),
            // Nothing has gone wrong, so nothing is being waited out.
            taken: SETTLED,
        }
    }

    /// The token in hand: what the tables are asked about, and what `advance`
    /// would hand back. Lent rather than given, so that looking costs nothing.
    fn peek(&self) -> &tokens::Tok {
        &self.current
    }

    /// Takes the token in hand and reads the next one into its place.
    fn advance(&mut self) -> tokens::Tok {
        std::mem::replace(&mut self.current, self.lexer.next_token())
    }

    /// What the automaton does with `tok`: the tables' answer for it in the
    /// state on top of the stack.
    ///
    /// The state is not a parameter because there is only ever one it could be
    /// — a caller passing any other would be asking about a stack the parser
    /// does not have — while the token is, so that a lookahead can be tried
    /// without being taken.
    ///
    /// A token the lexer could not read is turned down like any other the state
    /// has no action for, and carries the lexer's account of it: that is
    /// `action_for`'s doing, and there is no case for it here.
    fn action(&self, tok: &tokens::TokType) -> tables::Action {
        let (state, _) = *self.stack.last().expect("the start state is never popped");
        tables::action_for(state, tok)
    }

    /// Where a reduction leaves the automaton: the state to enter now that
    /// `lhs` has been built. Asked once the rule's symbols are off the stack,
    /// so the state it reads is the one the pop uncovered.
    ///
    /// Every reduce the tables ask for has a goto to go with it, so there is no
    /// answer to give back: none would mean the tables and the stack have come
    /// apart, which no source can bring about. What the source can do wrong is
    /// `action`'s to report.
    fn goto(&self, lhs: tables::NonTerminal) -> tables::State {
        let (state, _) = *self.stack.last().expect("the start state is never popped");
        tables::goto(state, lhs).expect("a reduce the tables asked for has a goto")
    }

    /// Puts a node in the arena and gives back the only handle to it.
    fn push_node(&mut self, node: ast_nodes::ASTNode) -> ASTNodeId {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    /// A node by the handle `push_node` gave out.
    ///
    /// Lending is all a parent ever needs: it keeps its children by handle, so
    /// building one reads a child at most to take its position, and nothing is
    /// ever moved out of the arena.
    fn get_node(&self, id: ASTNodeId) -> &ast_nodes::ASTNode {
        &self.nodes[id]
    }

    /// Puts an entry on the stack: the state to parse in from here, and the
    /// node whatever got the parse there built.
    ///
    /// Both halves for the reason `pop` gives back both -- an entry is the two
    /// together, and there is no moment where the stack holds one without the
    /// other.
    fn push(&mut self, state: tables::State, node: ASTNodeId) {
        self.stack.push((state, node));
    }

    /// The top of the stack, state and node together.
    ///
    /// One method rather than two: an entry holds both, so a `pop_state` and a
    /// `pop_node` could not each take one -- the second would drop a whole
    /// entry to reach a half of it.
    fn pop(&mut self) -> (tables::State, ASTNodeId) {
        self.stack.pop().expect("the start state is never popped")
    }

    /// Takes the token in hand and pushes it under `next`, the state the tables
    /// send the parse to for it.
    ///
    /// Gives back the leaf's handle, which is the entry's own: a rule taking
    /// this terminal will find it among its children, positioned where the
    /// token was.
    ///
    /// `note_shift` comes last, so the depth it records an opener at is the one
    /// the stack stands at while that opener is open.
    fn shift(&mut self, next: tables::State) -> ASTNodeId {
        let tok = self.advance();
        let node = ast_nodes::ASTNode::at(leaf_of(&tok.toktype), &tok);
        let idx = self.push_node(node);
        self.push(next, idx);
        self.note_shift(&tok);
        idx
    }

    /// Runs one reduction: takes the rule's symbols off the stack, builds what
    /// they make, and pushes it under the state the tables send the parse to.
    ///
    /// Gives back the new node's handle, which is the whole tree's once the
    /// last reduction is done.
    fn reduce(&mut self, rule_id: tables::RuleId) -> ASTNodeId {
        let rule = &tables::RULES[rule_id as usize];

        // The symbols come off youngest first, so what is collected here is the
        // rule's right-hand side backwards.
        let mut children = Vec::with_capacity(rule.len);
        for _ in 0..rule.len {
            children.push(self.pop().1);
        }
        children.reverse();

        let node = self.build(rule_id, &children);
        let idx = self.push_node(node);
        // With the children gone, the stack's top is the state the rule began
        // in, which is the one that says where a `rule.lhs` goes next.
        let next = self.goto(rule.lhs);
        self.push(next, idx);
        idx
    }

    /// Takes note of a token shifted: the parse has taken something, so the
    /// next mistake is a mistake of its own rather than the last one again.
    ///
    /// Called after the state is pushed, so that the depth an opener is
    /// recorded at is the one the stack stands at while it is open.
    fn note_shift(&mut self, tok: &tokens::Tok) {
        self.taken += 1;
        self.note_delimiter(tok);
    }

    /// Follows a delimiter going past, whether the parse took it or a recovery
    /// dropped it. Either way it is no longer waiting to be closed.
    fn note_delimiter(&mut self, tok: &tokens::Tok) {
        let terminal = tables::terminal_of(&tok.toktype);
        if closer_of(terminal).is_some() {
            let depth = self.stack.len();
            self.open.push((tok.clone(), depth));
            return;
        }
        // A closer the tables took closes the innermost opener by construction,
        // so the check is only worth anything for the ones a recovery drops:
        // those the grammar never passed on, and a `]` where a `(` is open is
        // not the `(`'s closer and does not take it off.
        let innermost = self.open.last().map(|(opener, _)| {
            closer_of(tables::terminal_of(&opener.toktype)) == Some(terminal)
        });
        if innermost == Some(true) {
            self.open.pop();
        }
    }

    /// What the parse is in the middle of, if anything worth naming.
    ///
    /// Read off the stack rather than the state on top of it, because most
    /// states stand inside nothing on their own: a state partway through an
    /// expression is partway through an expression wherever that expression is,
    /// and which parameter list or match arm it sits in is further down.
    ///
    /// The innermost entry that names anything wins, and it can name something
    /// the source has finished writing: a rule is only off the stack once it is
    /// reduced, and a lookahead the tables turn down is one no state would
    /// reduce on. `f([1, 2]` stopped at the next token is still inside the array
    /// by that reckoning, though the `]` is written. What is named is always a
    /// rule the parse has begun and not finished, which is the honest answer
    /// even where a reader can see the end of it.
    fn context(&self) -> Option<&'static str> {
        self
            .stack
            .iter()
            .rev()
            .find_map(|&(state, _)| tables::context(state))
    }

    /// The opener still waiting to be closed, where that is what went wrong.
    ///
    /// Named only when the token in hand is the end of the file or a closer
    /// that does not mate it. Anywhere else there is nearly always something
    /// open -- a function body, an argument list -- and naming it would be a
    /// note on every error rather than an account of this one.
    fn unclosed(&self, found: tables::Terminal) -> Option<&tokens::Tok> {
        let (opener, _) = self.open.last()?;
        let mates = closer_of(tables::terminal_of(&opener.toktype)) == Some(found);
        let closes_something = matches!(
            found,
            tables::Terminal::RParen
                | tables::Terminal::RBracket
                | tables::Terminal::RCurlyBracket
        );
        if found == tables::Terminal::EOF || (closes_something && !mates) {
            return Some(opener);
        }
        None
    }

    /// Why the token in hand is not the one wanted, where the difference is a
    /// rule of the language rather than a slip. See `HINTS`.
    fn hint(&self, found: tables::Terminal) -> Option<String> {
        let expected = self.expected_tokens();
        // A keyword written where a name belongs is the one case worth naming
        // whichever keyword it is, so it is a rule rather than a table row.
        if tables::is_keyword(found) && expected.contains(&tables::Terminal::Identifier) {
            return Some(format!(
                "{} is a keyword and cannot be used as a name",
                tables::name_of(found)
            ));
        }
        for &(was, wanted, hint) in HINTS {
            if found == was && expected.contains(&wanted) {
                return Some(hint.to_string());
            }
        }
        None
    }

    /// Everything there is to say about the token in hand being the wrong one.
    ///
    /// `msg` is the tables' account, which is what was wanted and what came
    /// instead. What is added here is what the tables cannot know: which
    /// construct the stack is in the middle of, which opener is still waiting,
    /// and why the two spellings differ where that is worth saying.
    ///
    /// None of it is laid out here. What comes back is the facts, and how they
    /// are shown is `diag`'s -- a caret under the line for a reader, one line
    /// for a tool.
    fn parse_error(&self, msg: &str) -> Diagnostic {
        let found = tables::terminal_of(&self.current.toktype);
        let mut d = Diagnostic::error(msg.to_string(), span_of(&self.current));
        // The construct the parse is in the middle of, which is a phrase about
        // this same token: it goes in the margin beside the caret.
        if let Some(what) = self.context() {
            d = d.with_label(format!("while parsing {}", what));
        }
        if let Some(hint) = self.hint(found) {
            d = d.with_help(hint);
        }
        if let Some(opener) = self.unclosed(found) {
            let spelling = spelling_of(tables::terminal_of(&opener.toktype));
            d = d.with_secondary(span_of(opener), format!("unclosed {} opened", spelling));
        }
        d
    }

    /// Writes down what the tables turned down. `parse` reports and then
    /// recovers, so that one mistake does not hide the rest of the file.
    ///
    /// Silent until the parse has settled: see `SETTLED`. The cost is a second
    /// mistake that truly sits within a few tokens of the first, which is a
    /// fair price for not answering one stray brace with a paragraph.
    fn report(&mut self, msg: &str) {
        if self.taken < SETTLED {
            return;
        }
        let full = self.parse_error(msg);
        self.errors.push(full);
        self.taken = 0;
    }

    /// Everything the parse turned down, in the order it did.
    ///
    /// Spans and not text: each says which piece of the source it is about,
    /// and the caller -- which is holding the source as it was written --
    /// renders them against it. The parse may well have been run over a
    /// preprocessed copy, and quoting that back would show a reader a line
    /// they did not write.
    pub fn errors(&self) -> &Diagnostics {
        &self.errors
    }

    /// Puts the parse somewhere it can go on from, and says whether it found
    /// anywhere. Panic mode: skip to something that ends a whole construct,
    /// then uncover a state that can take it.
    ///
    /// The stack is cut back only as far as the innermost state that has an
    /// action for the token found, never to the bottom on the chance that it
    /// helps. What is given up is real -- everything built inside the~ cut is
    /// gone -- and giving up more of it than the mistake costs is how a
    /// recovery turns one error into a page of them.
    fn recover(&mut self) -> bool {
        loop {
            let found = tables::terminal_of(&self.current.toktype);
            if found == tables::Terminal::EOF {
                return false;
            }
            if SYNC.contains(&found) {
                let reachable = self.stack.iter().rposition(|&(state, _)| {
                    !matches!(tables::action(state, found), tables::Action::Error(_))
                });
                if let Some(depth) = reachable {
                    self.stack.truncate(depth + 1);
                    self.open.retain(|&(_, at)| at <= self.stack.len());
                    return true;
                }
            }
            let tok = self.advance();
            self.note_delimiter(&tok);
        }
    }

    /// The terminals the parse could take right now.
    ///
    /// `tables::Action::Error` already carries a written-out `expected ..`, and
    /// that is what an error should say; these are for a caller that wants the
    /// terminals themselves -- `hint`, which asks whether one in particular was
    /// among them.
    fn expected_tokens(&self) -> Vec<tables::Terminal> {
        let (state, _) = *self.stack.last().expect("the start state is never popped");
        tables::expected(state)
    }

    /// Runs the automaton over the token stream and gives back what it built.
    ///
    /// Takes `&mut self` because a parse is the whole of what a `Parser` does:
    /// it spends the lexer, the stack and the arena, and there is no second one
    /// to run afterward.
    /// A shift and a reduce are `shift` and `reduce`, which the tables' answer
    /// picks between; an error calls `report` and then `recover`, and gives up
    /// only where that says there is nowhere left to go on from.
    ///
    /// What comes back is the root, and the nodes it names stay in the arena --
    /// so the caller holds the `Parser` afterward for those and for `errors()`
    /// both. A parse that could not recover gives back an `Empty` standing
    /// where it stopped: there is no tree to give, and `errors` says why.
    ///
    /// Accept is the last word rather than EOF: the tables say it once the
    /// start symbol is the whole of the stack, which is the only place the
    /// parse is finished rather than merely out of tokens.
    pub fn parse(&mut self) -> ast_nodes::ASTNode {
        loop {
            let action = self.action(&self.current.toktype);
            match action {
                tables::Action::Shift(next) => {
                    self.shift(next);
                }
                tables::Action::Reduce(rule_id) => {
                    self.reduce(rule_id);
                }
                tables::Action::Accept => {
                    // The start symbol's own entry is on top, and its node is
                    // everything the parse built.
                    let (_, root) = *self.stack.last().expect("accept leaves the tree on top");
                    return self.get_node(root).clone();
                }
                tables::Action::Error(msg) => {
                    self.report(&msg);
                    if !self.recover() {
                        return ast_nodes::ASTNode::at(ast_nodes::ASTNodeKind::Empty, &self.current);
                    }
                }
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    /// Runs the automaton over `source`, building no nodes, and gives back
    /// every message it reported.
    ///
    /// `build` is not written yet, and nothing here needs a tree: what a
    /// message says is settled by the stack and the token in hand, and this
    /// drives both exactly as `parse` will. A shift is `shift` itself; a reduce
    /// is spelled out because `reduce` would reach `build`, and the node it
    /// pushes is handle 0, which stands for nothing and is never read.
    fn parsed(source: &str) -> Parser {
        let mut p = Parser::new(lexer::Lexer::new(source));
        loop {
            let action = p.action(&p.current.toktype);
            match action {
                tables::Action::Shift(next) => {
                    p.shift(next);
                }
                tables::Action::Reduce(rule_id) => {
                    let rule = &tables::RULES[rule_id as usize];
                    for _ in 0..rule.len {
                        p.pop();
                    }
                    let next = p.goto(rule.lhs);
                    p.push(next, 0);
                }
                tables::Action::Accept => break,
                tables::Action::Error(msg) => {
                    p.report(&msg);
                    if !p.recover() {
                        break;
                    }
                }
            }
        }
        p
    }

    /// Every message a source drew, each laid out on its own.
    ///
    /// What these tests are about is which facts a message carries -- the
    /// construct, the opener, the hint -- and where it points. All of that is
    /// on the page, so all of it is asserted as it will be read.
    fn errors_in(source: &str) -> Vec<String> {
        let text: Vec<char> = source.chars().collect();
        let quoted = crate::error::Source::new("input.fc", &text);
        parsed(source).errors().iter().map(|e| e.render(&quoted)).collect()
    }

    /// The one message a source is meant to draw.
    fn error_in(source: &str) -> String {
        let mut errors = errors_in(source);
        assert_eq!(errors.len(), 1, "{}\n{}", source, errors.join("\n\n"));
        errors.remove(0)
    }

    /// The lexer never sees a comment -- they are blanked out before it runs --
    /// but a reader has to be shown the line they wrote. Blanking keeps every
    /// character where it was, so nothing about the caret moves: only the text
    /// under it is the one that was written rather than the one that was lexed.
    #[test]
    fn a_comment_is_quoted_back_though_the_parse_never_saw_it() {
        let written = "fn main() {\n    let x = /* huh */ ;  // why\n}\n";
        let prepped = crate::prep::preprocess(written);
        // Blanking keeps every character where it was, which is what lets one
        // text be lexed and the other quoted with no span moved between them.
        assert_eq!(written.chars().count(), prepped.chars().count());

        let mut p = Parser::new(lexer::Lexer::new(&prepped));
        p.parse();

        let text: Vec<char> = written.chars().collect();
        let quoted = crate::error::Source::new("input.fc", &text);
        assert_eq!(
            p.errors().render(&quoted),
            "\
error: expected an expression, found `;`
 --> input.fc:2:23
  |
2 |     let x = /* huh */ ;  // why
  |                       ^ while parsing a variable declaration"
        );

        // The same errors against the text that was lexed: the caret falls in
        // the same column, under a line nobody wrote. That the caller chooses
        // is the whole of the difference.
        let lexed: Vec<char> = prepped.chars().collect();
        let other = crate::error::Source::new("input.fc", &lexed);
        assert!(
            p.errors().render(&other).contains("2 |     let x =           ;"),
            "{}",
            p.errors().render(&other)
        );
    }

    /// A source the grammar takes says nothing at all.
    #[test]
    fn a_parse_that_works_reports_nothing() {
        assert!(errors_in("fn main() {\n    let x = 1\n    g(x)\n}\n").is_empty());
        assert!(errors_in("struct P {\n    x: i32,\n}\n").is_empty());
    }

    /// Which construct the mistake is in, which the tables cannot say on their
    /// own: a state partway through an expression is partway through one
    /// wherever it stands, and where it stands is further down the stack.
    ///
    /// It is written beside the caret rather than in the message, where it
    /// reads as what the parse was doing when the underlined token arrived.
    #[test]
    fn names_the_construct_it_is_in() {
        assert_eq!(
            error_in("fn f(x: ) {}\n"),
            "\
error: expected a type, found `)`
 --> input.fc:1:9
  |
1 | fn f(x: ) {}
  |         ^ while parsing a parameter"
        );
        assert_eq!(
            error_in("struct P {\n    x: i32\n    y i32,\n}\n"),
            "\
error: expected `,`, `[` or `}`, found an identifier
 --> input.fc:3:5
  |
3 |     y i32,
  |     ^ while parsing a field"
        );
        assert_eq!(
            error_in("fn main() {\n    match x {\n        1 => ,\n    }\n}\n"),
            "\
error: expected an expression, found `,`
 --> input.fc:3:14
  |
3 |         1 => ,
  |              ^ while parsing a match arm"
        );
        assert_eq!(
            error_in("impl<T> Stack<T> where {\n}\n"),
            "\
error: expected a type, found a block `{`
 --> input.fc:1:24
  |
1 | impl<T> Stack<T> where {
  |                        ^ while parsing a `where` clause"
        );
        assert_eq!(
            error_in("fn main() {\n    let x: = 5\n}\n"),
            "\
error: expected a type, found `=`
 --> input.fc:2:12
  |
2 |     let x: = 5
  |            ^ while parsing a variable declaration"
        );
        // A tuple is the innermost thing it stands in, wherever that is: a
        // return type here, an argument list below.
        assert_eq!(
            error_in("fn f(): (i32, ) {}\n"),
            "\
error: expected a type, found `)`
 --> input.fc:1:15
  |
1 | fn f(): (i32, ) {}
  |               ^ while parsing a tuple type"
        );
        assert_eq!(
            error_in("fn main() {\n    g((1, ))\n}\n"),
            "\
error: expected an expression, found `)`
 --> input.fc:2:11
  |
2 |     g((1, ))
  |           ^ while parsing a tuple"
        );
        assert_eq!(
            error_in("fn main() {\n    match p {\n        (1, ) => a,\n    }\n}\n"),
            "\
error: expected a pattern, found `)`
 --> input.fc:3:13
  |
3 |         (1, ) => a,
  |             ^ while parsing a tuple pattern"
        );
    }

    /// A state stands inside something on nearly every error, so a note about
    /// what is open is worth making only where that is what went wrong.
    ///
    /// It is a snippet of its own, because the opener is nowhere near the token
    /// that gave it away and one caret cannot point at two lines.
    #[test]
    fn names_the_opener_that_was_never_closed() {
        assert_eq!(
            error_in("fn main() {\n    f(1, 2\n}\n"),
            "\
error: expected an operator, `,` or `)`, found `}`
 --> input.fc:3:1
  |
3 | }
  | ^ while parsing an argument list

note: unclosed `(` opened here
 --> input.fc:2:6
  |
2 |     f(1, 2
  |      ^"
        );
        // The end of the file is a place and not a piece of the source: one
        // caret, on the empty line after the last one written.
        assert_eq!(
            error_in("fn main() {\n    let x = 1\n"),
            "\
error: expected a statement or `}`, found end of file
 --> input.fc:3:1
  |
3 |
  | ^ while parsing a variable declaration

note: unclosed `{` opened here
 --> input.fc:1:11
  |
1 | fn main() {
  |           ^"
        );
        // The innermost one, and only that: the `[` is closed by the time the
        // `}` is turned down, so the `(` is what is still waiting.
        assert_eq!(
            error_in("fn main() {\n    f([1, 2]\n}\n"),
            "\
error: expected an operator, `,` or `)`, found `}`
 --> input.fc:3:1
  |
3 | }
  | ^ while parsing an array literal

note: unclosed `(` opened here
 --> input.fc:2:6
  |
2 |     f([1, 2]
  |      ^"
        );
        // Something is open at nearly every error. Here it is not the mistake,
        // and the message does not bring it up -- one snippet, not two.
        assert_eq!(
            error_in("fn main() {\n    let x = ;\n}\n"),
            "\
error: expected an expression, found `;`
 --> input.fc:2:13
  |
2 |     let x = ;
  |             ^ while parsing a variable declaration"
        );
    }

    /// Why the two spellings differ, where that is a rule of the language
    /// rather than a slip of the finger. It hangs off the end under a bar of
    /// its own, so that it reads as part of the same block.
    #[test]
    fn names_the_difference_where_it_is_a_rule() {
        // The caret is the token's width and not one column: `fn` is two.
        assert_eq!(
            error_in("fn fn() {}\n"),
            "\
error: expected an identifier, found `fn`
 --> input.fc:1:4
  |
1 | fn fn() {}
  |    ^~ while parsing a function's signature
  |
  = help: `fn` is a keyword and cannot be used as a name"
        );
        assert_eq!(
            error_in("struct P {\n    x: i32;\n}\n"),
            "\
error: expected `,`, `[` or `}`, found `;`
 --> input.fc:2:11
  |
2 |     x: i32;
  |           ^ while parsing a field
  |
  = help: use `,` to separate entries"
        );
        // The lexer has already decided which kind of `{` this is, so a state
        // that wanted the other kind is not asking for another character.
        assert_eq!(
            error_in("fn f(): i32 {1: 2}\n"),
            "\
error: expected `[`, a block `{`, `;` or `where`, found a value `{`
 --> input.fc:1:13
  |
1 | fn f(): i32 {1: 2}
  |             ^ while parsing a return type
  |
  = help: this `{` opens a value literal, but a block is expected here; \
             parenthesise the literal to use one"
        );
    }

    /// One mistake does not hide the rest of the file: the parse skips to
    /// something that ends a whole construct and goes on from there.
    ///
    /// Each is a block of its own with a blank line between, so that a run of
    /// them does not read as one long message.
    #[test]
    fn goes_on_after_an_error() {
        let source = "fn a() { let x = ; }\nfn b() { let y = ; }\nfn c() { g(] }\n";
        assert_eq!(errors_in(source).len(), 3, "{}", source);
        assert_eq!(
            errors_in(source).join("\n\n"),
            "\
error: expected an expression, found `;`
 --> input.fc:1:18
  |
1 | fn a() { let x = ; }
  |                  ^ while parsing a variable declaration

error: expected an expression, found `;`
 --> input.fc:2:18
  |
2 | fn b() { let y = ; }
  |                  ^ while parsing a variable declaration

error: expected an expression or `)`, found `]`
 --> input.fc:3:12
  |
3 | fn c() { g(] }
  |            ^ while parsing a function

note: unclosed `(` opened here
 --> input.fc:3:11
  |
3 | fn c() { g(] }
  |           ^"
        );
    }

    /// What a recovery makes of the tokens just after a mistake says more about
    /// where it landed than about the source, so it is not reported.
    #[test]
    fn does_not_answer_one_mistake_twice() {
        // The `{` is a literal's, so the `if` never gets a body and every
        // brace after it lands somewhere unintended. One error, not four.
        assert_eq!(
            error_in("fn main() {\n    if x {1: 2}\n}\n"),
            "\
error: expected an identifier or `}`, found an integer literal
 --> input.fc:2:11
  |
2 |     if x {1: 2}
  |           ^ while parsing a struct literal"
        );
    }

    /// A file with nothing left to sync on ends rather than saying the same
    /// thing about every token to the end of it.
    #[test]
    fn gives_up_where_there_is_nowhere_to_go_on_from() {
        assert_eq!(
            error_in("fn a(((((\n"),
            "\
error: expected an identifier, `)`, `this` or `_`, found `(`
 --> input.fc:1:6
  |
1 | fn a(((((
  |      ^ while parsing a function's signature"
        );
    }

    /// What the lexer could not read is turned down in the lexer's words, and
    /// the parser adds where the parse had got to.
    ///
    /// The token runs to the end of the file, so the caret stops at the end of
    /// the line -- as far as the reader can still see it.
    #[test]
    fn passes_on_what_the_lexer_says() {
        assert_eq!(
            error_in("fn main() {\n    let s = \"unclosed\n}\n"),
            "\
error: Unterminated string
 --> input.fc:2:13
  |
2 |     let s = \"unclosed
  |             ^~~~~~~~~ while parsing a variable declaration"
        );
    }
}
