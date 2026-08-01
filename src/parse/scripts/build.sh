#!/usr/bin/env bash
# Regenerate the parser's LR(1) tables from the grammar. Run from the repo root.
#
# With --dump, also write the listings the scripts produce for reading by hand:
# the FIRST sets, the start state's closure, and every state with its
# transitions. They go first so that they are on disk to consult if the table
# generator then reports a conflict.
set -euo pipefail

SCRIPTS="src/parse/scripts"
GRAMMAR="docs/grammar.bnf"
OUTPUT="src/parse/tables.rs"
DUMPS="build/parse"

if [[ "${1:-}" == "--dump" ]]; then
    mkdir -p "$DUMPS"

    echo "=== FIRST sets -> $DUMPS/first_sets.txt ==="
    python3 "$SCRIPTS/first.py" "$GRAMMAR" > "$DUMPS/first_sets.txt"

    echo "=== Start closure -> $DUMPS/closure.txt ==="
    python3 "$SCRIPTS/items.py" "$GRAMMAR" > "$DUMPS/closure.txt"

    echo "=== States -> $DUMPS/states.txt ==="
    python3 "$SCRIPTS/states.py" "$GRAMMAR" > "$DUMPS/states.txt"
elif [[ -n "${1:-}" ]]; then
    echo "usage: $0 [--dump]" >&2
    exit 1
fi

echo "=== Tables -> $OUTPUT ==="
python3 "$SCRIPTS/tables.py" "$GRAMMAR" "$OUTPUT"

echo "Done!"
