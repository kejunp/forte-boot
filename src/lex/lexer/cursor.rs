// Where the scanner is, and how to put it back.
//
// The cursor is three numbers -- an index, a line and a column -- and the only
// interesting thing here is that all of it can be saved and restored. §7 asks
// questions that cannot be answered without reading ahead: whether a `{` opens
// a block or a map literal is settled by scanning its body and seeing what is
// in it, and that scan has to leave no trace.
//
// So `save` takes everything `next_token` mutates and `restore` puts it back.
// The input is not in the snapshot: it never changes, and copying it per
// lookahead would make a linear scan quadratic.


use super::{Lexer, State};

impl Lexer {
    pub fn new(input: &str) -> Self {
        Lexer {
            input: input.chars().collect(),
            index: 0,
            line:  1,
            col:   1,

            last_can_end:      false,
            last_closed_block: false,
            bracket_depth:     0,
            // Nothing precedes the first token, so a `&&` there is two `&`.
            last_ends_operand: false,

            in_attribute:       false,
            attr_bracket_depth: 0,
            in_visibility:      false,
            vis_bracket_depth:  0,

            brace_depth:        0,
            entry_braces:       0,
            value_braces:       0,
            pending_entry_body: false,
            pending_header:     false,
            header_depth:       0,
            header_brace_depth: 0,

            hash_prefix:    false,
            path_prefix:    false,
            // Nothing precedes the first token, and a statement may start there.
            prev_ends_stmt: true,
            prev_was_brace: false,
            prev_was_dot:   false,

            generic_depth:     0,
            last_was_name:     false,
            last_was_impl:     false,
            last_was_type_end: false,
            last_was_decl_kw: false,
            last_was_decl_name: false,

            in_closure_params:   false,
            closure_pipe_depth:  0,
            last_closed_closure: false,
        }
    }

    pub(super) fn peek_char(&self) -> Option<char> {
        self.input.get(self.index).copied()
    }

    pub(super) fn peek_char_at(&self, offset: usize) -> Option<char> {
        self.input.get(self.index + offset).copied()
    }

    pub(super) fn advance(&mut self) -> Option<char> {
        let ch = self.peek_char();
        if let Some(c) = ch {
            self.index += 1;
            if c == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        ch
    }

    pub(super) fn save(&self) -> State {
        State {
            index: self.index,
            line:  self.line,
            col:   self.col,

            last_can_end:      self.last_can_end,
            last_closed_block: self.last_closed_block,
            bracket_depth:     self.bracket_depth,
            last_ends_operand: self.last_ends_operand,

            in_attribute:       self.in_attribute,
            attr_bracket_depth: self.attr_bracket_depth,

            in_visibility:      self.in_visibility,
            vis_bracket_depth:  self.vis_bracket_depth,

            brace_depth:        self.brace_depth,
            entry_braces:       self.entry_braces,
            value_braces:       self.value_braces,
            pending_entry_body: self.pending_entry_body,
            pending_header:     self.pending_header,
            header_depth:       self.header_depth,
            header_brace_depth: self.header_brace_depth,

            hash_prefix:    self.hash_prefix,
            path_prefix:    self.path_prefix,
            prev_ends_stmt: self.prev_ends_stmt,
            prev_was_brace: self.prev_was_brace,
            prev_was_dot:   self.prev_was_dot,

            generic_depth:     self.generic_depth,
            last_was_name:     self.last_was_name,
            last_was_impl:     self.last_was_impl,
            last_was_type_end: self.last_was_type_end,
            last_was_decl_kw: self.last_was_decl_kw,
            last_was_decl_name: self.last_was_decl_name,

            in_closure_params:   self.in_closure_params,
            closure_pipe_depth:  self.closure_pipe_depth,
            last_closed_closure: self.last_closed_closure,
        }
    }

    pub(super) fn restore(&mut self, s: State) {
        self.index = s.index;
        self.line = s.line;
        self.col = s.col;

        self.last_can_end = s.last_can_end;
        self.last_closed_block = s.last_closed_block;
        self.bracket_depth = s.bracket_depth;
        self.last_ends_operand = s.last_ends_operand;
        self.in_attribute = s.in_attribute;
        self.attr_bracket_depth = s.attr_bracket_depth;
        self.in_visibility = s.in_visibility;
        self.vis_bracket_depth = s.vis_bracket_depth;

        self.brace_depth = s.brace_depth;
        self.entry_braces = s.entry_braces;
        self.value_braces = s.value_braces;
        self.pending_entry_body = s.pending_entry_body;
        self.pending_header = s.pending_header;
        self.header_depth = s.header_depth;
        self.header_brace_depth = s.header_brace_depth;

        self.hash_prefix = s.hash_prefix;
        self.path_prefix = s.path_prefix;
        self.prev_ends_stmt = s.prev_ends_stmt;
        self.prev_was_brace = s.prev_was_brace;
        self.prev_was_dot = s.prev_was_dot;

        self.generic_depth = s.generic_depth;
        self.last_was_name = s.last_was_name;
        self.last_was_impl = s.last_was_impl;
        self.last_was_type_end = s.last_was_type_end;
        self.last_was_decl_kw = s.last_was_decl_kw;
        self.last_was_decl_name = s.last_was_decl_name;

        self.in_closure_params = s.in_closure_params;
        self.closure_pipe_depth = s.closure_pipe_depth;
        self.last_closed_closure = s.last_closed_closure;
    }
}
