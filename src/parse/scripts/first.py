#!/usr/bin/env python3
"""
Parse the fortec BNF and compute FIRST sets.
Usage: python3 first.py grammar.bnf
"""

import json
import sys

EPSILON = 'ε'

# The grammar file describes the whole language, lexis included. These names are
# produced by the lexer, so the parser sees them as terminals: their defining
# rules, and everything only they reach, are dropped before any table is built.
TOKEN_CLASSES = {
    'IDENTIFIER',
    'INT_LITERAL',
    'FLOAT_LITERAL',
    'STRING_LITERAL',
    'CHAR_LITERAL',
}

# Never spelled in the grammar's own notation; supplied by the lexer at the end
# of input and named explicitly by <program>.
END_OF_FILE = 'EOF'

START = '<program>'

# `<empty>` marks an alternative that derives nothing, not a symbol.
EMPTY = '<empty>'


class GrammarError(Exception):
    pass


def scan(text):
    """Split a line into BNF tokens, keeping quoted terminals whole.

    Quotes do not nest and there are no escapes: a terminal runs from its
    opening quote to the next quote of the same kind. That is what lets the
    grammar write `"|"` and `'"'` without either confusing the other.
    """
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c in '"\'':
            end = text.find(c, i + 1)
            if end < 0:
                raise GrammarError(f"unterminated terminal: {text[i:]!r}")
            tokens.append(text[i:end + 1])
            i = end + 1
            continue
        # A bare run: a non-terminal, a token class, or the `::=` / `|` marks.
        start = i
        while i < len(text) and not text[i].isspace() and text[i] not in '"\'':
            i += 1
        tokens.append(text[start:i])
    return tokens


def split_rules(lines):
    """Group the file's lines into (lhs, rhs tokens) pairs.

    A rule starts on the line holding its `::=` and runs until the next such
    line. Continuation lines belong to the rule above whether or not they open
    with `|`, which is how the multi-line productions stay intact.
    """
    rules = []
    for line in lines:
        # Whole-line comments only: `#` is a terminal of the language, so it
        # cannot also mean "rest of line ignored".
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        tokens = scan(line)
        if '::=' in tokens:
            mark = tokens.index('::=')
            if mark != 1:
                raise GrammarError(f"expected one symbol before ::= in: {line.strip()!r}")
            rules.append((tokens[0], tokens[mark + 1:]))
        elif rules:
            rules[-1][1].extend(tokens)
        else:
            raise GrammarError(f"text before the first rule: {line.strip()!r}")
    return rules


def parse_alternatives(lhs, tokens):
    """Split a rule's right-hand side on top-level `|` into symbol lists."""
    alternatives = []
    current = []
    for token in tokens + ['|']:
        if token == '|':
            alternatives.append(current)
            current = []
            continue
        if token.startswith('"') or token.startswith("'"):
            current.append(('terminal', token[1:-1]))
        elif token.startswith('<') and token.endswith('>'):
            if token != EMPTY:
                current.append(('non-terminal', token))
        elif token.isupper() and token.replace('_', '').isalnum():
            current.append(('token-class', token))
        else:
            raise GrammarError(f"unrecognised symbol {token!r} in rule {lhs}")
    return alternatives


def reachable_from(start, productions):
    """Non-terminals the start symbol can reach, not descending into tokens."""
    seen = {start}
    stack = [start]
    while stack:
        nt = stack.pop()
        if nt not in productions:
            raise GrammarError(f"{nt} is used but never defined")
        for alternative in productions[nt]:
            for kind, name in alternative:
                if kind == 'non-terminal' and name not in seen:
                    seen.add(name)
                    stack.append(name)
    return seen


def parse_grammar(filename):
    """Parse the BNF into {non-terminal: [production]}, plus its symbol sets.

    Only the part of the grammar the parser is responsible for survives: rules
    defining a token class are dropped, and so is anything reachable only
    through them (the character-level rules, `<keyword>`, `<comment>`).
    """
    with open(filename, 'r') as f:
        rules = split_rules(f.readlines())

    productions = {}
    for lhs, tokens in rules:
        if lhs == EMPTY or lhs in TOKEN_CLASSES:
            continue
        if not (lhs.startswith('<') and lhs.endswith('>')):
            raise GrammarError(f"rule name {lhs!r} is neither a non-terminal nor a token class")
        if lhs in productions:
            raise GrammarError(f"{lhs} is defined twice")
        productions[lhs] = parse_alternatives(lhs, tokens)

    if START not in productions:
        raise GrammarError(f"no {START} rule to start from")

    live = reachable_from(START, productions)
    grammar = {}
    terminals = {END_OF_FILE}
    for nt in sorted(live):
        alternatives = []
        for alternative in productions[nt]:
            symbols = []
            for kind, name in alternative:
                if kind != 'non-terminal':
                    terminals.add(name)
                symbols.append(name)
            if symbols not in alternatives:
                alternatives.append(symbols)
        grammar[nt] = alternatives

    non_terminals = set(grammar)
    clash = terminals & non_terminals
    if clash:
        raise GrammarError(f"names used as both terminal and non-terminal: {sorted(clash)}")

    # <program> must come first: it is the symbol the table generator augments.
    grammar = {START: grammar.pop(START), **grammar}
    return grammar, terminals, non_terminals


def first_of_sequence(symbols, first, terminals):
    """FIRST of a string of symbols, containing ε if the whole string is nullable."""
    result = set()
    for sym in symbols:
        if sym in terminals:
            result.add(sym)
            return result
        result |= first[sym] - {EPSILON}
        if EPSILON not in first[sym]:
            return result
    result.add(EPSILON)
    return result


def compute_first(grammar, terminals, non_terminals):
    """Compute FIRST sets by fixed-point iteration."""
    first = {nt: set() for nt in non_terminals}
    changed = True
    while changed:
        changed = False
        for nt, alternatives in grammar.items():
            for symbols in alternatives:
                add = first_of_sequence(symbols, first, terminals)
                if not add <= first[nt]:
                    first[nt] |= add
                    changed = True
    return first


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 first.py grammar.bnf", file=sys.stderr)
        sys.exit(1)

    try:
        grammar, terminals, non_terminals = parse_grammar(sys.argv[1])
    except GrammarError as e:
        print(f"{sys.argv[1]}: {e}", file=sys.stderr)
        sys.exit(1)

    first_sets = compute_first(grammar, terminals, non_terminals)

    print(f"Non-terminals: {len(non_terminals)}")
    print(f"Terminals: {len(terminals)}")
    print(f"Productions: {sum(len(a) for a in grammar.values())}")
    print()
    for nt in sorted(non_terminals):
        print(f"FIRST({nt}) = {{{', '.join(sorted(first_sets[nt]))}}}")

    print("\n--- MACHINE READABLE ---")
    print(json.dumps({
        'grammar': grammar,
        'terminals': sorted(terminals),
        'non_terminals': sorted(non_terminals),
        'first_sets': {k: sorted(v) for k, v in first_sets.items()},
    }))


if __name__ == "__main__":
    main()
