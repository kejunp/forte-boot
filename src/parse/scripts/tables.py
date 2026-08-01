#!/usr/bin/env python3
"""
Generate the ACTION/GOTO tables for the canonical LR(1) parser.
Usage: python3 tables.py grammar.bnf output.rs
"""

import sys
from collections import defaultdict

from first import END_OF_FILE, GrammarError, compute_first, parse_grammar
from items import sort_key
from states import AUGMENTED_START, build_states

# Every terminal the grammar can spell, and the TokType the lexer hands over for
# it. Generation fails on a terminal missing from here, so a new piece of syntax
# cannot reach the tables before the lexer knows how to produce it.
TOKENS = {
    'i8': 'I8', 'i16': 'I16', 'i32': 'I32', 'i64': 'I64',
    'u8': 'U8', 'u16': 'U16', 'u32': 'U32', 'u64': 'U64',
    'f32': 'F32', 'f64': 'F64',
    'bool': 'Bool', 'char': 'Char', 'str': 'Str', 'never': 'Never',

    'fn': 'Fn', 'let': 'Let', 'var': 'Var', 'const': 'Const',
    'struct': 'Struct', 'trait': 'Trait', 'impl': 'Impl',
    'public': 'Public', 'private': 'Private', 'import': 'Import',
    'enum': 'Enum', 'namespace': 'Namespace', 'unsafe': 'Unsafe',

    'if': 'If', 'elif': 'Elif', 'else': 'Else', 'while': 'While',
    'for': 'For', 'in': 'In', 'return': 'Return', 'break': 'Break',
    'continue': 'Continue', 'match': 'Match',

    'true': 'True', 'false': 'False', 'this': 'This', 'null': 'Null',
    '_': 'Underscore',

    'as': 'As', 'where': 'Where', 'move': 'Move',

    '+': 'Plus', '-': 'Minus', '*': 'Star', '/': 'Slash', '%': 'Percent',
    '<<': 'LShift', '>>': 'RShift',

    '==': 'EqualsEquals', '!=': 'BangEquals',
    '<': 'LessThan', '>': 'GreaterThan',
    '<=': 'LessOrEqual', '>=': 'GreaterOrEqual',

    '&&': 'And', '||': 'Or', '!': 'Bang', '|': 'Pipe', '&': 'Ampersand',

    '..': 'DotDot', '..=': 'DotDotEquals',

    '=': 'Equals', '+=': 'PlusEquals', '-=': 'MinusEquals',
    '*=': 'StarEquals', '/=': 'SlashEquals', '&=': 'AndEquals',
    '|=': 'OrEquals', '<<=': 'LShiftEquals', '>>=': 'RShiftEquals',

    '(': 'LParen', ')': 'RParen', '[': 'LBracket', ']': 'RBracket',
    '{': 'LCurlyBracket', '}': 'RCurlyBracket',
    # The lexer decides which kind of thing a `{` opens and says so; the grammar
    # is ambiguous without it. See `push_brace`.
    'VALUE_LCURLY': 'LCurlyValue',
    ':': 'Colon', '::': 'ColonColon', ',': 'Comma', '.': 'Dot',
    ';': 'Semicolon', '=>': 'FatArrow', '#': 'HashTag', '@': 'At',

    'IDENTIFIER': 'Identifier', 'INT_LITERAL': 'IntLiteral',
    'FLOAT_LITERAL': 'FloatLiteral', 'STRING_LITERAL': 'StringLiteral',
    'CHAR_LITERAL': 'CharLiteral',

    END_OF_FILE: 'EOF',
}

# TokType variants that carry a value, so their patterns need a placeholder.
PAYLOAD = {'Identifier', 'IntLiteral', 'FloatLiteral', 'StringLiteral', 'CharLiteral'}

# How a terminal is named in an error message. A terminal the grammar spells
# outright is quoted as it is written; the rest stand for a whole class of
# tokens, or for nothing the source can hold, and have to be described instead.
DESCRIPTIONS = {
    'IDENTIFIER': 'an identifier',
    'INT_LITERAL': 'an integer literal',
    'FLOAT_LITERAL': 'a float literal',
    'STRING_LITERAL': 'a string literal',
    'CHAR_LITERAL': 'a character literal',
    # Two terminals are both written `{`, and the message has to say which one
    # was wanted: the lexer has already decided, and that decision is the whole
    # difference between them.
    '{': '`{` opening a block',
    'VALUE_LCURLY': '`{` opening a value',
    END_OF_FILE: 'end of file',
}

# How many alternatives an error message lists before it gives up counting. A
# state can permit most of the terminals there are, and a list that long says
# nothing that a count does not.
MAX_EXPECTED = 6


def describe(terminal):
    """The name an error message gives a terminal, as a Rust string literal."""
    text = DESCRIPTIONS.get(terminal, f"`{terminal}`")
    return '"' + text.replace('\\', '\\\\').replace('"', '\\"') + '"'


class TableError(Exception):
    pass


def variant(non_terminal):
    """`<item_list>` -> `ItemList`."""
    return ''.join(part.capitalize() for part in non_terminal[1:-1].split('_'))


def build_tables(grammar, terminals, non_terminals, first_sets):
    """Build the ACTION and GOTO tables, collecting every conflict on the way."""
    states, transitions, augmented = build_states(
        grammar, terminals, non_terminals, first_sets)

    rules = [(lhs, rhs) for lhs, alternatives in augmented.items() for rhs in alternatives]
    rule_index = {(lhs, tuple(rhs)): i for i, (lhs, rhs) in enumerate(rules)}

    action = {}
    goto = {}
    conflicts = []

    def set_action(state, lookahead, entry):
        """Record an action, resolving any clash the way yacc would.

        Shift beats reduce, and between two reduces the rule written first in
        the grammar wins. Both are arbitrary, so every clash is kept and
        reported: the resolution stops the table from being ill-defined, it does
        not mean the grammar is right.
        """
        previous = action.get((state, lookahead))
        if previous is None:
            action[(state, lookahead)] = entry
            return
        if previous == entry:
            return
        conflicts.append((state, lookahead, previous, entry))
        if previous[0] == 'shift' or (previous[0] == entry[0] and previous[1] < entry[1]):
            return
        action[(state, lookahead)] = entry

    for (state, symbol), successor in transitions.items():
        if symbol in non_terminals:
            goto[(state, symbol)] = successor
        else:
            set_action(state, symbol, ('shift', successor))

    for i, state in enumerate(states):
        for item in sorted(state, key=sort_key):
            if item.dot != len(item.rhs):
                continue
            if item.lhs == AUGMENTED_START:
                set_action(i, item.lookahead, ('accept', 0))
            else:
                set_action(i, item.lookahead,
                           ('reduce', rule_index[(item.lhs, item.rhs)]))

    return states, action, goto, rules, conflicts


def report_conflicts(conflicts, rules, limit=12):
    """Describe conflicts by the pair of actions that disagree.

    A state holds hundreds of items, nearly all of them beside the point, so
    what is printed is the two actions rather than the state. One ambiguity in
    the grammar reappears in state after state and under lookahead after
    lookahead, so identical pairs are gathered onto one entry: those are the
    things there are to go and fix.
    """
    def describe(entry):
        kind, value = entry
        if kind != 'reduce':
            # The state a shift goes to differs at every site of the same
            # ambiguity, and says nothing about its cause.
            return kind
        lhs, rhs = rules[value]
        return f"reduce {lhs} -> {' '.join(rhs) if rhs else 'ε'}"

    kinds = defaultdict(int)
    grouped = {}
    for state, lookahead, previous, entry in conflicts:
        kinds['/'.join(sorted([previous[0], entry[0]]))] += 1
        lookaheads, states = grouped.setdefault(
            (describe(previous), describe(entry)), (set(), []))
        lookaheads.add(lookahead)
        states.append(state)

    print(f"\n{len(conflicts)} conflicts in {len(grouped)} pairs: "
          + ', '.join(f"{n} {kind}" for kind, n in sorted(kinds.items())),
          file=sys.stderr)

    order = sorted(grouped.items(), key=lambda kv: (-len(kv[1][1]), kv[0]))
    for (left, right), (lookaheads, states) in order[:limit]:
        shown = ' '.join(sorted(lookaheads)[:8])
        if len(lookaheads) > 8:
            shown += f" (+{len(lookaheads) - 8})"
        print(f"\n  {left}\n  vs {right}\n"
              f"    on: {shown}\n"
              f"    in {len(set(states))} states, first {min(states)}",
              file=sys.stderr)
    if len(grouped) > limit:
        print(f"\n  ... and {len(grouped) - limit} more pairs", file=sys.stderr)


def generate_rust(states, action, goto, rules, terminals, non_terminals):
    """Emit the tables as Rust.

    Rows are sparse and sorted by symbol, because most of a state's row is
    empty: 4.5k states against ~90 terminals is mostly holes, and the parser
    only ever asks about one entry at a time.
    """
    terminal_order = sorted(terminals, key=lambda t: TOKENS[t])
    terminal_id = {t: i for i, t in enumerate(terminal_order)}
    non_terminal_order = sorted(non_terminals)
    non_terminal_id = {nt: i for i, nt in enumerate(non_terminal_order)}

    # The row entries below are typed; say so when the grammar outgrows them,
    # rather than emitting Rust that silently truncates.
    for what, count, limit in (('terminals', len(terminal_order), 256),
                               ('non-terminals', len(non_terminal_order), 256),
                               ('states', len(states), 65536)):
        if count >= limit:
            raise TableError(f"{count} {what} does not fit the generated table's width")

    out = []
    w = out.append

    w("// Generated by src/parse/scripts/tables.py -- DO NOT EDIT.")
    w("// Canonical LR(1) tables for the grammar in docs/grammar.bnf.")
    w("")
    w("use crate::lex::tokens::TokType;")
    w("")

    w("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w("pub enum Terminal {")
    for t in terminal_order:
        w(f"    {TOKENS[t]},")
    w("}")
    w("")

    w("/// The terminal a token stands for, with its value dropped.")
    w("pub fn terminal_of(tok: &TokType) -> Option<Terminal> {")
    w("    Some(match tok {")
    for t in terminal_order:
        name = TOKENS[t]
        pattern = f"TokType::{name}(..)" if name in PAYLOAD else f"TokType::{name}"
        w(f"        {pattern} => Terminal::{name},")
    w("        TokType::Error(..) => return None,")
    w("    })")
    w("}")
    w("")

    w("/// What each terminal is called in an error message, by `Terminal as usize`.")
    w(f"static TERMINAL_NAMES: [&str; {len(terminal_order)}] = [")
    for t in terminal_order:
        w(f"    {describe(t)},")
    w("];")
    w("")

    w("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w("pub enum NonTerminal {")
    for nt in non_terminal_order:
        w(f"    {variant(nt)},")
    w("}")
    w("")

    w("/// What the table holds. The error case is not one of these: it is every")
    w("/// terminal a state's row leaves out, which is most of them.")
    w("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w("enum Entry {")
    w("    Shift(u16),")
    w("    Reduce(u16),")
    w("    Accept,")
    w("}")
    w("")

    w("#[derive(Debug, Clone, PartialEq, Eq)]")
    w("pub enum Action {")
    w("    Shift(u16),")
    w("    Reduce(u16),")
    w("    Accept,")
    w("    /// No action: the message says what the state would have taken instead.")
    w("    Error(String),")
    w("}")
    w("")

    w("/// One production: what it builds, and how many symbols it pops.")
    w("pub struct Rule {")
    w("    pub lhs: NonTerminal,")
    w("    pub len: usize,")
    w("}")
    w("")

    w("pub const RULES: &[Rule] = &[")
    for lhs, rhs in rules:
        w(f"    Rule {{ lhs: NonTerminal::{variant(lhs)}, len: {len(rhs)} }},"
          f" // {lhs} -> {' '.join(rhs) if rhs else 'ε'}")
    w("];")
    w("")

    rows = defaultdict(list)
    for (state, lookahead), (kind, value) in action.items():
        rendered = {'shift': f"Entry::Shift({value})",
                    'reduce': f"Entry::Reduce({value})",
                    'accept': "Entry::Accept"}[kind]
        rows[state].append((terminal_id[lookahead], rendered))

    w("/// Per state, the terminals with an action, sorted by `Terminal as usize`.")
    w("static ACTION: [&[(u8, Entry)]; NUM_STATES] = [")
    for state in range(len(states)):
        entries = ', '.join(f"({i}, {a})" for i, a in sorted(rows[state]))
        w(f"    &[{entries}],")
    w("];")
    w("")

    goto_rows = defaultdict(list)
    for (state, nt), successor in goto.items():
        goto_rows[state].append((non_terminal_id[nt], successor))

    w("/// Per state, the non-terminals with a transition, sorted the same way.")
    w("static GOTO: [&[(u8, u16)]; NUM_STATES] = [")
    for state in range(len(states)):
        entries = ', '.join(f"({i}, {s})" for i, s in sorted(goto_rows[state]))
        w(f"    &[{entries}],")
    w("];")
    w("")

    w(f"pub const NUM_STATES: usize = {len(states)};")
    w(f"pub const NUM_RULES: usize = {len(rules)};")
    w("")

    w("/// How many alternatives an error message lists before it counts the rest.")
    w(f"const MAX_EXPECTED: usize = {MAX_EXPECTED};")
    w("")

    w("/// `expected .., found ..`: what `state` would have taken, and what came.")
    w("///")
    w("/// The row is in `Terminal` order, which is the order the variants are")
    w("/// declared in and means nothing to a reader of the message. It is at least")
    w("/// the same order every time, so the same mistake reads the same way twice.")
    w("fn unexpected(state: usize, found: Terminal) -> String {")
    w("    let row = ACTION[state];")
    w("    let names: Vec<&str> = row")
    w("        .iter()")
    w("        .take(MAX_EXPECTED)")
    w("        .map(|&(t, _)| TERMINAL_NAMES[t as usize])")
    w("        .collect();")
    w("    let rest = row.len() - names.len();")
    w("")
    w("    let expected = if rest > 0 {")
    w("        format!(\"{}, or {} more\", names.join(\", \"), rest)")
    w("    } else {")
    w("        match names.split_last() {")
    w("            // A state with no action at all: unreachable from the start")
    w("            // state, so nothing can be the token that got here.")
    w("            None => \"nothing\".to_string(),")
    w("            Some((last, [])) => last.to_string(),")
    w("            Some((last, first)) => format!(\"{} or {}\", first.join(\", \"), last),")
    w("        }")
    w("    };")
    w("    format!(\"expected {}, found {}\", expected, TERMINAL_NAMES[found as usize])")
    w("}")
    w("")

    w("/// What to do in `state` when the next token is `terminal`.")
    w("pub fn action(state: usize, terminal: Terminal) -> Action {")
    w("    let key = terminal as u8;")
    w("    let row = ACTION[state];")
    w("    match row.binary_search_by_key(&key, |&(t, _)| t) {")
    w("        Ok(i) => match row[i].1 {")
    w("            Entry::Shift(next) => Action::Shift(next),")
    w("            Entry::Reduce(rule) => Action::Reduce(rule),")
    w("            Entry::Accept => Action::Accept,")
    w("        },")
    w("        Err(_) => Action::Error(unexpected(state, terminal)),")
    w("    }")
    w("}")
    w("")

    w("/// The state to enter after reducing to `non_terminal` in `state`.")
    w("pub fn goto(state: usize, non_terminal: NonTerminal) -> Option<usize> {")
    w("    let key = non_terminal as u8;")
    w("    let row = GOTO[state];")
    w("    row.binary_search_by_key(&key, |&(n, _)| n)")
    w("        .ok()")
    w("        .map(|i| row[i].1 as usize)")
    w("}")

    return '\n'.join(out) + '\n'


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 tables.py grammar.bnf output.rs", file=sys.stderr)
        sys.exit(1)

    try:
        grammar, terminals, non_terminals = parse_grammar(sys.argv[1])
    except GrammarError as e:
        print(f"{sys.argv[1]}: {e}", file=sys.stderr)
        sys.exit(1)

    unknown = sorted(t for t in terminals if t not in TOKENS)
    if unknown:
        print(f"{sys.argv[1]}: terminals with no TokType in tables.py: {unknown}",
              file=sys.stderr)
        sys.exit(1)

    first_sets = compute_first(grammar, terminals, non_terminals)
    states, action, goto, rules, conflicts = build_tables(
        grammar, terminals, non_terminals, first_sets)

    non_terminals = non_terminals | {AUGMENTED_START}
    try:
        rust = generate_rust(states, action, goto, rules, terminals, non_terminals)
    except TableError as e:
        print(f"{sys.argv[1]}: {e}", file=sys.stderr)
        sys.exit(1)
    with open(sys.argv[2], 'w') as f:
        f.write(rust)

    print(f"Tables written to {sys.argv[2]}")
    print(f"States: {len(states)}")
    print(f"Rules: {len(rules)}")
    print(f"Actions: {len(action)}")
    print(f"GOTOs: {len(goto)}")

    if conflicts:
        sys.stdout.flush()
        report_conflicts(conflicts, rules)
        sys.exit(1)


if __name__ == "__main__":
    main()
