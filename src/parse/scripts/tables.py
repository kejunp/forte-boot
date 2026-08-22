#!/usr/bin/env python3
"""
Generate the ACTION/GOTO tables for the canonical LR(1) parser.
Usage: python3 tables.py grammar.bnf output.rs
"""

import sys
from collections import defaultdict

from first import (EPSILON, END_OF_FILE, TOKEN_CLASSES, GrammarError,
                   compute_first, parse_grammar)
from items import sort_key
from states import AUGMENTED_START, build_states

# The lexer's own failure. It is a terminal so that every token the lexer can
# hand over has one, and so that nothing downstream has to carry a case for the
# token that is not a terminal; no state has an action for it, so every state
# turns it down. What it could not read is in the token itself, and that is the
# message -- see `action_for`.
LEX_ERROR = 'LEX_ERROR'

# Every terminal the grammar can spell, and the TokType the lexer hands over for
# it. Generation fails on a terminal missing from here, so a new piece of syntax
# cannot reach the tables before the lexer knows how to produce it.
TOKENS = {
    'i8': 'I8', 'i16': 'I16', 'i32': 'I32', 'i64': 'I64', 'i128': 'I128',
    'u8': 'U8', 'u16': 'U16', 'u32': 'U32', 'u64': 'U64', 'u128': 'U128',
    'f32': 'F32', 'f64': 'F64',
    'bool': 'Bool', 'char': 'Char', 'str': 'Str', 'never': 'Never',
    'ptr': 'Ptr',

    'fn': 'Fn', 'let': 'Let', 'var': 'Var', 'const': 'Const',
    'struct': 'Struct', 'trait': 'Trait', 'impl': 'Impl', 'type': 'Type',
    'pub': 'Pub', 'priv': 'Priv', 'import': 'Import',
    'suite': 'Suite', 'super': 'Super',
    'enum': 'Enum', 'namespace': 'Namespace', 'unsafe': 'Unsafe',
    'gc': 'Gc',
    'macro': 'Macro',

    'if': 'If', 'elif': 'Elif', 'else': 'Else', 'while': 'While',
    'for': 'For', 'in': 'In', 'return': 'Return', 'break': 'Break',
    'continue': 'Continue', 'match': 'Match',

    'true': 'True', 'false': 'False', 'self': 'SelfKw', 'null': 'Null',
    '_': 'Underscore',

    'as': 'As', 'where': 'Where', 'move': 'Move', 'addr': 'Addr',

    '+': 'Plus', '-': 'Minus', '*': 'Star', '/': 'Slash', '%': 'Percent',
    '<<': 'LShift', '>>': 'RShift',

    '==': 'EqualsEquals', '!=': 'BangEquals',
    '<': 'LessThan', '>': 'GreaterThan',
    '<=': 'LessOrEqual', '>=': 'GreaterOrEqual',

    '&&': 'And', '||': 'Or', '^^': 'Xor', '!': 'Bang',
    '|': 'Pipe', '&': 'Ampersand', '^': 'Caret',

    '..': 'DotDot', '..=': 'DotDotEquals',

    '=': 'Equals', '+=': 'PlusEquals', '-=': 'MinusEquals',
    '*=': 'StarEquals', '/=': 'SlashEquals', '&=': 'AndEquals',
    '|=': 'OrEquals', '^=': 'CaretEquals',
    '<<=': 'LShiftEquals', '>>=': 'RShiftEquals',

    '(': 'LParen', ')': 'RParen', '[': 'LBracket', ']': 'RBracket',
    '{': 'LCurlyBracket', '}': 'RCurlyBracket',
    # The lexer decides which kind of thing a `{` opens and says so; the grammar
    # is ambiguous without it. See `push_brace`.
    'VALUE_LCURLY': 'LCurlyValue',
    # The `<` of a call's type arguments, told from a comparison by a look
    # ahead to the matching `>`. See `opens_type_args`.
    'GENERIC_LT': 'LessGeneric',
    ':': 'Colon', '::': 'ColonColon', ',': 'Comma', '.': 'Dot',
    # `::*`, glued as one token so that it ends an operand where a bare `*`
    # could not. See `TokType::Glob`.
    '::*': 'Glob',
    ';': 'Semicolon', '=>': 'FatArrow', '#': 'HashTag',

    'IDENTIFIER': 'Identifier', 'INT_LITERAL': 'IntLiteral',
    'FLOAT_LITERAL': 'FloatLiteral', 'STRING_LITERAL': 'StringLiteral',
    'CHAR_LITERAL': 'CharLiteral', 'LIFETIME': 'Lifetime',
    'ATTR_NAME': 'AttrName', 'MACRO_NAME': 'MacroName',
    'MACRO_PARAM': 'MacroParam',

    END_OF_FILE: 'EOF',
    LEX_ERROR: 'Error',
}

# TokType variants that carry a value, so their patterns need a placeholder.
PAYLOAD = {'Identifier', 'IntLiteral', 'FloatLiteral', 'StringLiteral',
           'CharLiteral', 'Lifetime', 'AttrName', 'MacroName',
           'MacroParam', 'Error'}

# How a terminal is named in an error message. A terminal the grammar spells
# outright is quoted as it is written; the rest stand for a whole class of
# tokens, or for nothing the source can hold, and have to be described instead.
DESCRIPTIONS = {
    'IDENTIFIER': 'an identifier',
    'INT_LITERAL': 'an integer literal',
    'FLOAT_LITERAL': 'a float literal',
    'STRING_LITERAL': 'a string literal',
    'CHAR_LITERAL': 'a character literal',
    'LIFETIME': 'a lifetime',
    'ATTR_NAME': 'an attribute',
    'MACRO_NAME': 'a macro',
    'MACRO_PARAM': 'a macro parameter',
    # Two terminals are both written `{`, and the message has to say which one
    # was wanted: the lexer has already decided, and that decision is the whole
    # difference between them.
    '{': 'a block `{`',
    'VALUE_LCURLY': 'a value `{`',
    'GENERIC_LT': 'a type argument list',
    END_OF_FILE: 'end of file',
    LEX_ERROR: 'a token that could not be read',
}

# What a whole class of terminals is called, when a state permits so many of
# them that naming them one by one says nothing. A class is named only where a
# state takes every terminal that can begin one -- so "an expression" is not a
# summary of the list but a fact about the state, and a shorter way to say a
# piece of it.
#
# Order is preference: the first entry that covers as much as any other wins,
# so the broadest reading of a state comes out in front of its parts.
CLASSES = {
    '<item>': 'a declaration',
    '<statement>': 'a statement',
    '<expression>': 'an expression',
    # The ladder below `<expression>`, for the places that take some of it and
    # not the rest: after `1 +` no block form may stand, and a state that says
    # so by listing eleven terminals says it worse than the word does.
    '<value_expr>': 'an expression',
    '<assignment>': 'an expression',
    '<unary>': 'an operand',
    '<primary>': 'an operand',
    '<pattern>': 'a pattern',
    '<type>': 'a type',
    # A `where` clause's subject is every type but one ending in a bare fn
    # type, which is a grammar's trouble with a colon and not a reader's: to
    # anybody being told what was expected here, it is a type.
    '<where_subject>': 'a type',
    '<block>': 'a block',
    '<literal>': 'a literal',
    '<attribute>': 'an attribute',
    '<match_arm>': 'a match arm',
    '<enum_variant>': 'an enum variant',
    '<field_decl>': 'a field',
    '<field_init>': 'a field initialiser',
    '<map_entry>': 'a map entry',
    '<param>': 'a parameter',
    '<generic_param>': 'a type parameter',
    '<impl_member>': 'an impl member',
    '<trait_member>': 'a trait member',
    '<primitive_type>': 'a primitive type',
    '<qualified_name>': 'a name',
    # The one rung of the ladder a state does offer whole: an assignment takes
    # any of the ten at once, where a `+` is only ever offered beside a `*`
    # that the rung above has already taken.
    '<assign_op>': 'an assignment operator',
}

# Classes named where a state takes most of what can begin one, rather than all
# of it. A precedence ladder never offers the whole of itself at once -- with
# `a + b` in hand the parser has an additive, and a `*` cannot follow one -- so
# nothing would ever be called an operator if every operator had to fit. What
# is lost is that the message does not say which few are missing; what is kept
# is that it does not list twenty-five terminals instead.
#
# A key may be several symbols, and terminals of its own, for a class the
# grammar writes into the rules that use it rather than into a rule of its own.
LOOSE_CLASSES = {
    ('<additive_op>', '<multiplicative_op>', '<shift_op>', '<comparison_op>',
     '<equality_op>', '<assign_op>', '<range_op>', '<postfix_op>',
     '&', '|', '^', '&&', '||', '^^', 'as'): 'an operator',
}

# Every class, strict ones first so that they win a tie: both describe the
# state, and the one that leaves nothing out describes it better.
CANDIDATES = ([(symbols, phrase, True) for symbols, phrase in CLASSES.items()]
              + [(symbols, phrase, False) for symbols, phrase in LOOSE_CLASSES.items()])

# What a state is in the middle of, for the `in ..` an error message ends with.
# A state's kernel items are the rules it is partway through, and their left
# sides are every construct it stands inside; this says which of them to name.
#
# Order is preference, innermost first: a state inside a parameter's type is
# inside the parameter, the signature and the function too, and the innermost of
# those is the one that says where to look. What is left out is deliberate --
# `a statement` names nothing a reader could not see -- and a state whose
# kernels are all left out says nothing, which is better than saying that.
CONTEXTS = {
    '<attr_arg_list>': "an attribute's arguments",
    '<attribute>': 'an attribute',

    # Both stand inside whatever holds them -- an argument list, a match's
    # scrutinee, a variant's payload -- and are the innermost of it, so they
    # are named ahead of everything they can be written in.
    '<tuple_expr>': 'a tuple',
    '<tuple_pattern>': 'a tuple pattern',

    '<field_pattern_list>': 'a struct pattern',
    '<pattern_list>': "a pattern's payload",
    '<range_pattern>': 'a range pattern',
    '<pattern_alternatives>': 'a pattern',
    '<pattern>': 'a pattern',
    '<match_arm>': 'a match arm',
    '<match_arm_list>': "a `match`'s arms",
    '<match_expr>': 'a `match`',

    '<map_entry>': 'a map entry',
    '<map_literal>': 'a map literal',
    '<set_literal>': 'a set literal',
    '<array_literal>': 'an array literal',
    '<field_init>': 'a field initialiser',
    '<field_init_list>': 'a struct literal',
    '<struct_literal_tail>': 'a struct literal',

    '<arg_list>': 'an argument list',
    '<closure_param_list>': "a closure's parameters",
    '<closure_expr>': 'a closure',
    '<index>': 'an index',
    '<grouping>': 'a parenthesised expression',

    '<field_decl>': 'a field',
    '<field_decl_list>': "a struct's fields",
    '<enum_variant>': 'an enum variant',
    '<named_payload>': "a variant's fields",
    '<enum_variant_list>': "an enum's variants",

    '<receiver>': 'a receiver',
    '<param>': 'a parameter',
    '<param_seq>': 'a parameter list',
    '<param_list>': 'a parameter list',
    '<return_type_opt>': 'a return type',
    '<fn_sig>': "a function's signature",
    '<fn_head>': "a function's signature",

    '<generic_args>': 'a type argument list',
    '<generic_param>': 'a type parameter',
    '<generic_param_list>': 'a type parameter list',
    '<where_pred>': 'a `where` clause',
    '<where_pred_list>': 'a `where` clause',
    '<where_clause_opt>': 'a `where` clause',
    '<type_bounds>': 'a type bound',
    '<tuple_type>': 'a tuple type',
    '<grouped_type>': 'a parenthesised type',
    '<array_suffix>': 'an array type',
    '<ref_type>': 'a type',
    '<named_type>': 'a type',
    '<type>': 'a type',
    # A `where` clause's subject is every type but one ending in a bare fn
    # type, which is a grammar's trouble with a colon and not a reader's: to
    # anybody being told what was expected here, it is a type.
    '<where_subject>': 'a type',
    '<fn_type>': 'a type',

    '<if_expr>': 'an `if`',
    '<elif_list>': 'an `elif`',
    '<else_opt>': 'an `else`',
    '<while_expr>': 'a `while`',
    '<for_expr>': 'a `for`',

    # The rules a declaration is spelled out in, as well as the declaration
    # itself: `let x = ..` is a `<var_head>` all the way to its terminator, and
    # the `<var_decl>` around it is only ever partway through at the `;`.
    #
    # `<type_annotation_opt>` is left out on purpose although it is the innermost
    # rule of `x: ..` wherever one is written. It stands in a parameter, a field
    # and a declaration alike, and each of those says where to look where `a type
    # annotation` only says again what `expected a type` has said.
    '<import_path>': 'an `import`',
    '<import_tree>': 'an `import`',
    '<import_seq>': "an `import`'s group",
    '<import_list>': "an `import`'s group",
    '<import_head>': 'an `import`',
    '<import_decl>': 'an `import`',
    '<initializer_opt>': 'a variable declaration',
    '<var_head>': 'a variable declaration',
    '<var_decl>': 'a variable declaration',
    '<const_head>': 'a `const`',
    '<const_decl>': 'a `const`',
    '<discriminant>': 'an enum variant',
    '<struct_decl>': 'a struct declaration',
    '<enum_decl>': 'an enum declaration',
    '<trait_member>': 'a trait member',
    '<trait_decl>': 'a trait declaration',
    '<impl_member>': 'an impl member',
    '<impl_decl>': 'an impl block',
    '<namespace_decl>': 'a namespace',
    '<fn_decl>': 'a function',
}

# How many things an error message names before it gives up counting. A state
# can permit most of the terminals there are, and a list that long says nothing
# that a count does not.
MAX_EXPECTED = 6

# How much of what is left a class has to account for to be worth naming. One
# terminal is better named outright than called an expression.
MIN_CLASS = 2


def text_of(terminal):
    """The name an error message gives a terminal."""
    return DESCRIPTIONS.get(terminal, f"`{terminal}`")


def quote(text):
    """`text` as a Rust string literal."""
    return '"' + text.replace('\\', '\\\\').replace('"', '\\"') + '"'


def describe(terminal):
    """The name an error message gives a terminal, as a Rust string literal."""
    return quote(text_of(terminal))


def starts_of(symbols, first_sets):
    """Every terminal a class can begin with.

    A class is one symbol or several, and a symbol is a non-terminal -- taken
    by its FIRST set -- or a terminal standing for itself, which is how an
    operator the grammar writes into the rule that uses it is named at all.
    """
    if isinstance(symbols, str):
        symbols = (symbols,)
    starts = set()
    for symbol in symbols:
        if symbol in first_sets:
            starts |= first_sets[symbol] - {EPSILON}
        elif symbol in TOKENS:
            starts.add(symbol)
        else:
            raise TableError(f"{symbol} in CLASSES is neither a non-terminal nor a token")
    return starts


def expected_of(lookaheads, first_sets):
    """What a state is waiting for, in words: the text after `expected`.

    A class is named only where the state takes what begins one -- all of it,
    or most of it where the class says so -- so the phrase is true of the state
    and not merely of the part of the list it stands in for. Classes are taken
    greedily, largest first, until what is left is short enough to name
    outright: a state that permits every start of an expression says so in two
    words, where the list runs to fifty.
    """
    permitted = set(lookaheads)
    remaining = set(lookaheads)
    phrases = []
    while len(remaining) > MAX_EXPECTED:
        best, covered = None, set()
        for symbols, phrase, strict in CANDIDATES:
            if phrase in phrases:
                continue
            starts = starts_of(symbols, first_sets)
            missing = starts - permitted
            if not starts or (missing if strict else len(missing) * 2 >= len(starts)):
                continue
            reach = starts & remaining
            if len(reach) > len(covered):
                best, covered = phrase, reach
        if best is None or len(covered) < MIN_CLASS:
            break
        phrases.append(best)
        remaining -= covered

    ordered = sorted(remaining, key=lambda t: TOKENS[t])
    named = [text_of(t) for t in ordered[:MAX_EXPECTED]]
    uncounted = len(ordered) - len(named)

    items = phrases + named
    if uncounted:
        return ', '.join(items) + f", or {uncounted} more"
    if not items:
        # A state with no action at all: unreachable from the start state, so
        # nothing can be the token that got here.
        return "nothing"
    if len(items) == 1:
        return items[0]
    return ', '.join(items[:-1]) + ' or ' + items[-1]


def context_of(state):
    """What a state is in the middle of building: the text after `in`.

    Only the items with the dot inside them say it. An item with the dot at the
    front was put there by the closure -- it is something the state could go on
    to start, not something it has started -- and a state at the head of an
    expression is inside every rule an expression can begin, which is no place
    at all. An item with the dot at the end has finished: the rule is waiting to
    be reduced, which a lookahead the tables turn down never lets it be, and a
    parse stopped at `f([1, 2]` is no longer inside the array.
    """
    started = {item.lhs for item in state if 0 < item.dot < len(item.rhs)}
    for non_terminal, phrase in CONTEXTS.items():
        if non_terminal in started:
            return phrase
    return ""


def keywords_of(terminals):
    """The terminals that are words of the language rather than punctuation.

    A name cannot be spelled with one, and that is worth saying outright when a
    name was what was wanted. Spelling decides it: what the lexer would have
    read as an identifier had the language not claimed it first.
    """
    return {t for t in terminals
            if t.isidentifier() and t not in TOKEN_CLASSES
            and t not in (END_OF_FILE, LEX_ERROR, '_', 'VALUE_LCURLY')}


class TableError(Exception):
    pass


def variant(non_terminal):
    """`<item_list>` -> `ItemList`."""
    return ''.join(part.capitalize() for part in non_terminal[1:-1].split('_'))


def width_for(count, what):
    """The Rust type wide enough for `count` distinct numbers.

    Which width the tables need is a fact about the grammar, so it is worked out
    here rather than chosen by hand and revisited when the language grows. `u16`
    is the floor: a narrower one would churn the type on a toy grammar and save
    nothing once the entries around it are padded out.
    """
    for ty, limit in (('u16', 1 << 16), ('u32', 1 << 32)):
        if count < limit:
            return ty
    raise TableError(f"{count} {what} does not fit any width the tables emit")


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


def generate_rust(states, action, goto, rules, terminals, non_terminals, first_sets):
    """Emit the tables as Rust.

    Rows are sparse and sorted by symbol, because most of a state's row is
    empty: 4.5k states against ~90 terminals is mostly holes, and the parser
    only ever asks about one entry at a time.
    """
    terminal_order = sorted(set(terminals) | {LEX_ERROR}, key=lambda t: TOKENS[t])
    terminal_id = {t: i for i, t in enumerate(terminal_order)}
    non_terminal_order = sorted(non_terminals)
    non_terminal_id = {nt: i for i, nt in enumerate(non_terminal_order)}

    # A row is keyed by the symbol itself -- a `Terminal` or a `NonTerminal` --
    # so nothing here has a width to outgrow. What a state number and a rule
    # number are stored in is still the generator's to pick, because nothing
    # outside the tables spells either of them out.
    state_ty = width_for(len(states), 'states')
    rule_ty = width_for(len(rules), 'rules')

    out = []
    w = out.append

    w("// Generated by src/parse/scripts/tables.py -- DO NOT EDIT.")
    w("// Canonical LR(1) tables for the grammar in docs/grammar.bnf.")
    w("")
    w("use crate::lex::tokens::TokType;")
    w("")

    w("// A state of the automaton, and what a parser's stack is made of. The")
    w(f"// width is the generator's to pick -- {len(states)} states wanted this one --")
    w("// so nothing downstream says a width of its own.")
    w(f"pub type State = {state_ty};")
    w("")

    w("// An index into `RULES`. The same width as a `State` today and no relation")
    w("// to one: separate names so a reduce cannot be read as a shift.")
    w(f"pub type RuleId = {rule_ty};")
    w("")

    w("// A terminal of the grammar: a token with whatever it carries dropped. The")
    w("// order is the tables' own and the rows are sorted in it, so a lookup can")
    w("// bisect. Alphabetical by name, which is only there to stay stable.")
    w("#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]")
    w("pub enum Terminal {")
    for t in terminal_order:
        w(f"    {TOKENS[t]},")
    w("}")
    w("")

    w("// The terminal a token stands for, with its value dropped. Total: every")
    w("// token the lexer can hand over is a terminal, the one it could not read")
    w("// included. No state has an action for that one -- see `action_for`, which")
    w("// says why in the lexer's own words.")
    w("pub fn terminal_of(tok: &TokType) -> Terminal {")
    w("    match tok {")
    for t in terminal_order:
        name = TOKENS[t]
        pattern = f"TokType::{name}(..)" if name in PAYLOAD else f"TokType::{name}"
        w(f"        {pattern} => Terminal::{name},")
    w("    }")
    w("}")
    w("")

    w("// What each terminal is called in an error message, by `Terminal as usize`.")
    w(f"static TERMINAL_NAMES: [&str; {len(terminal_order)}] = [")
    for t in terminal_order:
        w(f"    {describe(t)},")
    w("];")
    w("")

    w("// What a terminal is called in an error message.")
    w("pub fn name_of(terminal: Terminal) -> &'static str {")
    w("    TERMINAL_NAMES[terminal as usize]")
    w("}")
    w("")

    w("// A non-terminal, ordered and sorted on the same terms as a `Terminal`.")
    w("#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]")
    w("pub enum NonTerminal {")
    for nt in non_terminal_order:
        w(f"    {variant(nt)},")
    w("}")
    w("")

    w("// What the table holds. The error case is not one of these: it is every")
    w("// terminal a state's row leaves out, which is most of them.")
    w("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w("enum Entry {")
    w("    Shift(State),")
    w("    Reduce(RuleId),")
    w("    Accept,")
    w("}")
    w("")

    w("#[derive(Debug, Clone, PartialEq, Eq)]")
    w("pub enum Action {")
    w("    Shift(State),")
    w("    Reduce(RuleId),")
    w("    Accept,")
    w("    // No action: the message says what the state would have taken instead.")
    w("    Error(String),")
    w("}")
    w("")

    w("// One production: what it builds, and how many symbols it pops.")
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
        rows[state].append((terminal_id[lookahead],
                            f"(Terminal::{TOKENS[lookahead]}, {rendered})"))

    w("// Per state, the terminals with an action, in `Terminal` order.")
    w("static ACTION: [&[(Terminal, Entry)]; NUM_STATES] = [")
    for state in range(len(states)):
        entries = ', '.join(entry for _, entry in sorted(rows[state]))
        w(f"    &[{entries}],")
    w("];")
    w("")

    goto_rows = defaultdict(list)
    for (state, nt), successor in goto.items():
        goto_rows[state].append((non_terminal_id[nt],
                                 f"(NonTerminal::{variant(nt)}, {successor})"))

    w("// Per state, the non-terminals with a transition, sorted the same way.")
    w("static GOTO: [&[(NonTerminal, State)]; NUM_STATES] = [")
    for state in range(len(states)):
        entries = ', '.join(entry for _, entry in sorted(goto_rows[state]))
        w(f"    &[{entries}],")
    w("];")
    w("")

    w(f"pub const NUM_STATES: usize = {len(states)};")
    w(f"pub const NUM_RULES: usize = {len(rules)};")
    w("")

    w("// Per state, what it is waiting for: the text after `expected`. Worked out")
    w("// when the tables are built, since it is a fact about the state and not the")
    w("// token that ran into it. A state permitting more than a handful is")
    w("// described by what it can build -- `an expression` -- and the terminals no")
    w("// such class accounts for are named after it.")
    w(f"static EXPECTED: [&str; NUM_STATES] = [")
    lookaheads = defaultdict(list)
    for (state, terminal) in action:
        lookaheads[state].append(terminal)
    for state in range(len(states)):
        w(f"    {quote(expected_of(lookaheads[state], first_sets))},")
    w("];")
    w("")

    w("// Per state, what the parse is in the middle of: the text after `in`. Empty")
    w("// where a state stands inside nothing worth naming. The tables can say this")
    w("// and a stack cannot: a state is the whole of what has been read so far.")
    w("static CONTEXTS: [&str; NUM_STATES] = [")
    for state in states:
        w(f"    {quote(context_of(state))},")
    w("];")
    w("")

    w("// What the parse is in the middle of in `state`, where that is worth")
    w("// naming: the innermost construct it has begun and not yet finished.")
    w("pub fn context(state: State) -> Option<&'static str> {")
    w("    let text = CONTEXTS[state as usize];")
    w("    if text.is_empty() {")
    w("        return None;")
    w("    }")
    w("    Some(text)")
    w("}")
    w("")

    keywords = sorted(keywords_of(terminal_order), key=lambda t: TOKENS[t])
    w("// Whether a terminal is a word of the language rather than punctuation. For")
    w("// one thing only: a name was wanted and a keyword was written, worth saying")
    w("// in those words rather than as `expected an identifier`. See `Parser::hint`.")
    w("pub fn is_keyword(terminal: Terminal) -> bool {")
    w("    matches!(")
    w("        terminal,")
    w("        " + "\n            | ".join(
        [f"Terminal::{TOKENS[keywords[0]]}"]
        + [f"Terminal::{TOKENS[t]}" for t in keywords[1:]]))
    w("    )")
    w("}")
    w("")

    w("// `expected .., found ..`: what `state` was waiting for, and what came.")
    w("fn unexpected(state: State, found: Terminal) -> String {")
    w("    format!(")
    w("        \"expected {}, found {}\",")
    w("        EXPECTED[state as usize], TERMINAL_NAMES[found as usize]")
    w("    )")
    w("}")
    w("")

    w("// What to do in `state` when the next token is `terminal`.")
    w("pub fn action(state: State, terminal: Terminal) -> Action {")
    w("    let row = ACTION[state as usize];")
    w("    match row.binary_search_by_key(&terminal, |&(t, _)| t) {")
    w("        Ok(i) => match row[i].1 {")
    w("            Entry::Shift(next) => Action::Shift(next),")
    w("            Entry::Reduce(rule) => Action::Reduce(rule),")
    w("            Entry::Accept => Action::Accept,")
    w("        },")
    w("        Err(_) => Action::Error(unexpected(state, terminal)),")
    w("    }")
    w("}")
    w("")

    w("// What to do in `state` when the next token is `tok`. The one thing a token")
    w("// says that a terminal does not is that the lexer could not read it:")
    w("// `Terminal::Error` is in no state's row, so an `expected ..` would be about")
    w("// a token that was never there, and the lexer's words are the whole of it.")
    w("pub fn action_for(state: State, tok: &TokType) -> Action {")
    w("    if let TokType::Error(why) = tok {")
    w("        return Action::Error(why.clone());")
    w("    }")
    w("    action(state, terminal_of(tok))")
    w("}")
    w("")

    w("// The terminals `state` has an action for, in `Terminal` order. `action`")
    w("// already says this in words when it turns one down, which is the message to")
    w("// show; this is the same fact unworded, for a caller that wants them.")
    w("pub fn expected(state: State) -> Vec<Terminal> {")
    w("    ACTION[state as usize].iter().map(|&(t, _)| t).collect()")
    w("}")
    w("")

    w("// The state to enter after reducing to `non_terminal` in `state`.")
    w("pub fn goto(state: State, non_terminal: NonTerminal) -> Option<State> {")
    w("    let row = GOTO[state as usize];")
    w("    row.binary_search_by_key(&non_terminal, |&(n, _)| n)")
    w("        .ok()")
    w("        .map(|i| row[i].1)")
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

    # A grammar with a conflict has no table worth writing: where two actions
    # disagree the generator keeps whichever it saw first, which is an answer
    # about the order the states came out in and not about the language. The
    # report comes before the file is opened, so a run that fails leaves the
    # tables the last good grammar produced -- a conflict costs the caller the
    # regeneration, and not what they had.
    if conflicts:
        report_conflicts(conflicts, rules)
        sys.exit(1)

    non_terminals = non_terminals | {AUGMENTED_START}
    try:
        rust = generate_rust(states, action, goto, rules, terminals, non_terminals,
                             first_sets)
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


if __name__ == "__main__":
    main()
