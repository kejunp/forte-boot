#!/usr/bin/env python3
"""
Build the canonical LR(1) state machine.
Usage: python3 states.py grammar.bnf
"""

import sys
from collections import defaultdict

from first import END_OF_FILE, START, GrammarError, compute_first, parse_grammar
from items import Closure, Item, sort_key

# The augmented start symbol. `<start>` cannot collide with a grammar symbol
# because no rule in the file is named that.
AUGMENTED_START = '<start>'

# The lookahead past the end of input. The usual `$` would be a symbol of its
# own, but the grammar already names that point in `<program> ::= <item_list>
# EOF`, so reusing EOF keeps one terminal where there would otherwise be two:
# the parser shifts EOF to finish `<program>`, then reads EOF again -- the lexer
# yields it for good once the source runs out -- and accepts.
END_MARKER = END_OF_FILE


def goto_sets(state):
    """Group a state's items by the symbol after the dot, dot advanced by one."""
    moved = defaultdict(set)
    for item in state:
        if item.dot < len(item.rhs):
            moved[item.rhs[item.dot]].add(
                Item(item.lhs, item.rhs, item.dot + 1, item.lookahead))
    return moved


def build_states(grammar, terminals, non_terminals, first_sets):
    """Build every LR(1) state and the transitions between them.

    The grammar is augmented with `<start> -> <program>` so that reducing it is
    the one accepting move, and so the start state has no item to re-enter.
    """
    grammar = {AUGMENTED_START: [[START]], **grammar}
    non_terminals = non_terminals | {AUGMENTED_START}
    close = Closure(grammar, first_sets, terminals, non_terminals)

    start_state = frozenset(close({Item(AUGMENTED_START, [START], 0, END_MARKER)}))
    states = [start_state]
    state_index = {start_state: 0}
    transitions = {}

    i = 0
    while i < len(states):
        # Sorted, so that state numbers depend on the grammar and nothing else:
        # item sets are sets, and their iteration order is not stable across
        # runs. The generated tables have to be reproducible.
        for symbol, moved in sorted(goto_sets(states[i]).items()):
            successor = frozenset(close(moved))
            index = state_index.get(successor)
            if index is None:
                index = len(states)
                state_index[successor] = index
                states.append(successor)
            transitions[(i, symbol)] = index
        i += 1

    return states, transitions, grammar


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 states.py grammar.bnf", file=sys.stderr)
        sys.exit(1)

    try:
        grammar, terminals, non_terminals = parse_grammar(sys.argv[1])
    except GrammarError as e:
        print(f"{sys.argv[1]}: {e}", file=sys.stderr)
        sys.exit(1)

    first_sets = compute_first(grammar, terminals, non_terminals)
    states, transitions, _ = build_states(grammar, terminals, non_terminals, first_sets)

    print(f"Total states: {len(states)}")
    print(f"Transitions: {len(transitions)}")

    for i, state in enumerate(states):
        print(f"\nState {i}:")
        for item in sorted(state, key=sort_key):
            print(f"  {item}")

    print("\nTransitions:")
    for (state, symbol), next_state in sorted(transitions.items()):
        print(f"  State {state} --{symbol}--> State {next_state}")


if __name__ == "__main__":
    main()
