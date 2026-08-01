#!/usr/bin/env python3
"""
LR(1) items and closure.
Usage: python3 items.py grammar.bnf
"""

import sys

from first import (EPSILON, END_OF_FILE, START, GrammarError, compute_first,
                   first_of_sequence, parse_grammar)


class Item:
    """A production with a dot in it and one lookahead terminal."""

    __slots__ = ('lhs', 'rhs', 'dot', 'lookahead', '_hash')

    def __init__(self, lhs, rhs, dot, lookahead):
        self.lhs = lhs
        self.rhs = tuple(rhs)
        self.dot = dot
        self.lookahead = lookahead
        self._hash = hash((self.lhs, self.rhs, self.dot, self.lookahead))

    def key(self):
        return (self.lhs, self.rhs, self.dot, self.lookahead)

    def __eq__(self, other):
        return self._hash == other._hash and self.key() == other.key()

    def __hash__(self):
        return self._hash

    def __repr__(self):
        before = ' '.join(self.rhs[:self.dot])
        after = ' '.join(self.rhs[self.dot:])
        return f"{self.lhs} -> {before} · {after}, {self.lookahead}"


class Closure:
    """Closure over one grammar, reusing the FIRST work across item sets."""

    def __init__(self, grammar, first_sets, terminals, non_terminals):
        self.grammar = grammar
        self.first_sets = first_sets
        self.terminals = terminals
        self.non_terminals = non_terminals
        self._tails = {}

    def lookaheads(self, beta, lookahead):
        """FIRST(β a): the lookaheads an item's successors inherit."""
        first_beta = self._tails.get(beta)
        if first_beta is None:
            first_beta = first_of_sequence(beta, self.first_sets, self.terminals)
            self._tails[beta] = first_beta
        if EPSILON not in first_beta:
            return first_beta
        return (first_beta - {EPSILON}) | {lookahead}

    def __call__(self, items):
        """Close an item set: worklist, so each new item is expanded once."""
        result = set(items)
        pending = list(result)
        while pending:
            item = pending.pop()
            if item.dot == len(item.rhs):
                continue
            b = item.rhs[item.dot]
            if b not in self.non_terminals:
                continue
            beta = item.rhs[item.dot + 1:]
            for lookahead in self.lookaheads(beta, item.lookahead):
                for production in self.grammar[b]:
                    successor = Item(b, production, 0, lookahead)
                    if successor not in result:
                        result.add(successor)
                        pending.append(successor)
        return result


def sort_key(item):
    return (item.lhs, item.rhs, item.dot, item.lookahead)


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 items.py grammar.bnf", file=sys.stderr)
        sys.exit(1)

    try:
        grammar, terminals, non_terminals = parse_grammar(sys.argv[1])
    except GrammarError as e:
        print(f"{sys.argv[1]}: {e}", file=sys.stderr)
        sys.exit(1)

    first_sets = compute_first(grammar, terminals, non_terminals)
    close = Closure(grammar, first_sets, terminals, non_terminals)

    # EOF as the lookahead past the end, the same marker states.py builds with.
    start_item = Item(START, grammar[START][0], 0, END_OF_FILE)
    print("Start item:", start_item)
    print("\nClosure:")
    for item in sorted(close({start_item}), key=sort_key):
        print(f"  {item}")


if __name__ == "__main__":
    main()
