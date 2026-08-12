pub mod ast_nodes;
pub mod parser;
pub mod tables;

// Runs the tables over a token stream and says whether they accept it. No tree
// is built: this tests that the grammar and the lexer agree about the language.
#[cfg(test)]
fn recognise(source: &str) -> Result<(), String> {
    use crate::lex::lexer::Lexer;
    use tables::{action_for, goto, Action, State, RULES};

    let mut lexer = Lexer::new(source);
    let mut stack: Vec<State> = vec![0];
    loop {
        let tok = lexer.peek();
        let state = *stack.last().unwrap();
        match action_for(state, &tok.toktype) {
            Action::Shift(next) => {
                lexer.next_token();
                stack.push(next);
            }
            Action::Reduce(rule) => {
                let rule = &RULES[rule as usize];
                stack.truncate(stack.len() - rule.len);
                let state = *stack.last().unwrap();
                let next = goto(state, rule.lhs)
                    .ok_or_else(|| format!("no goto for {:?} in state {}", rule.lhs, state))?;
                stack.push(next);
            }
            Action::Accept => return Ok(()),
            Action::Error(why) => return Err(format!("{}:{}: {}", tok.line, tok.col, why)),
        }
    }
}

#[cfg(test)]
fn accepts(source: &str) {
    if let Err(e) = recognise(source) {
        panic!("rejected:\n{}\n  {}", source, e);
    }
}

// A statement is not an item, so these snippets get a function to stand in.
#[cfg(test)]
fn accepts_body(body: &str) {
    accepts(&format!("fn main() {{\n{}\n}}\n", body));
}

// Every declaration a file can hold, in the lexer tests' own spellings: the
// grammar decides what a `{` may be only because the lexer already said what
// this one is.
#[test]
fn parses_declarations() {
    accepts("let x = 25;");
    accepts("let x = 25\nlet y = x + 1\n");
    accepts("import shapes::circle;\n");
    accepts("import shapes::circle as circ;\n");
    accepts("public const MAX: i32 = 1 << 20\n");
    accepts("struct P {\n    x: i32,\n    y: i32,\n}\n");
    accepts("public struct P<T> {\n    private x: T\n}\n");
    accepts("enum E {\n    A,\n    B(i32),\n    C { x: i32 },\n    D = 4,\n}\n");
    accepts("trait Show<T> {\n    fn show(this: T): str\n}\n");
    accepts("trait Show {\n    fn show(this): str\n    fn id(this): i32\n}\n");
    accepts("impl Show<i32> for Box {\n    fn show(this: i32): str { return \"box\" }\n}\n");
    accepts("impl<T> Stack<T> where T: Ord + Show {\n    fn len(this): i32;\n}\n");
    // A type is a type: an impl takes any of them, primitives included.
    accepts("impl i32 {\n    fn abs(this): i32;\n}\n");
    accepts("impl Show for str {\n    fn show(this): str { return this }\n}\n");
    accepts("impl<T> Show for T[] {\n    fn show(this): str;\n}\n");
    accepts("namespace limits {\n    public const MAX: i32 = 255\n}\n");
    accepts("%inline\n%repr(C)\npublic fn f();\n");
    accepts("%symbol(\"malloc\")\nfn malloc(n: u64): *u8;\n");
    accepts("const fn square(n: i32): i32 { n * n }\n");
    accepts("public unsafe fn write(dst: *u8[], n: u64);\n");
    accepts("fn panic(m: str): never;\n");
    accepts("fn log(m: str): null;\n");
    accepts("fn f() {\n    let x = 1\n    g(x)\n}\n");
}

// The statement and expression forms, from the same source.
#[test]
fn parses_statements() {
    accepts_body("let x: i32 = 25;");
    accepts_body("let m: Map<str, List<i32>> = empty()");
    accepts_body("let v: Vec<&str> = empty()\nlet m: Map<str, List<*Node>> = empty()");
    accepts_body("let n = bits >> 2");
    accepts_body("let n = c as i64 + 1");
    accepts_body("let big = 2_147_483_647");
    accepts_body("for i in 0..10 {}\nfor j in 0..=n {}");
    accepts_body("for i in 0.. {}\nfor j in ..10 {}\nfor k in .. {}");
    accepts_body("while c {\n    f()\n}\ng()");
    accepts_body("let x = if c {\n    1\n} else {\n    2\n}\nlet y = x");
    accepts_body("if c {\n    1\n} elif d {\n    2\n} else {\n    3\n}");
    accepts_body("let rr: &&i32 = &&x\nlet ok = a && b");
    accepts_body("let f = |x: i32| x * 2\nlet g = || 0\nlet ok = a || b");
    accepts_body("let show = || print(n)\nlet own = move || n + 1");
    accepts_body("let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\nlet s: &i32[] = &a");
    accepts_body("let w: *i32[] = *a[1..3]\nlet all = s[..]");
    accepts_body("let view: &i32[]\nlet refs: (&i32)[8]");
    accepts_body("let grid: i32[ROWS][ROWS]\nlet v: Vec<_> = f()");
    accepts_body("let c = shapes::Color::Red.name\nlet n = limits::MAX");
    // A primitive has methods like anything else, and "5." is not a float.
    accepts_body("let n = 5.abs()\nlet f = 5.0 + 1.0");
    accepts_body("let found = for x in xs {\n    if p(x) { break x }\n}");
    accepts_body("while true {\n    break\n    continue\n}");
    accepts_body("return");
}

// A `{` is a block or a value, and the lexer says which.
#[test]
fn parses_braces_of_both_kinds() {
    // A literal, and a block whose statements sit in the same place.
    accepts_body("let p = Point {\n    x: 1,\n    y: 2,\n}");
    accepts_body("let p = shapes::Point { x: 1 }");
    // The brace hangs off whatever the separators built, and does not care
    // which of them built it -- that a `.` chain is not how a module is
    // reached is settled above the grammar, which takes either.
    accepts_body("let p = cfg.shapes.Point { x: 1 }");
    accepts_body("let v = {\n    f()\n    g()\n}\n{\n    h()\n    k()\n}");
    accepts_body("let x = {\n    let a = 1\n    a\n}");
    accepts_body("let x = {\n    f();\n    g()\n}");
    // The collection literals, hashed and not, and the spellings of the empty
    // ones that work where a block would otherwise be read.
    accepts_body("let a = [1, 2, 3]\nlet m = {1: 2, 3: 4}\nlet s = {1, 2, 3}\nlet h = #{1: 2}");
    accepts_body("let m = {}\nlet s = {,}\nlet one = {x}");
    accepts_body("let m = {:}\nlet h = #{}\nlet g = #{1, 2}");
    accepts_body("let m = {\n    \"a\": 1,\n    \"b\": 2,\n}\n.len()");
    accepts_body("let n = Point { x: 1 }\n    .norm()");
    // A header claims its brace; a literal at the top level of one does not
    // give it up.
    accepts_body("if ready {\n    f()\n    g()\n}");
    accepts_body("for x in {1, 2} {\n    f(x)\n    g(x)\n}");
    accepts_body("for x in #{{1, 2}, {3}} {\n    f(x)\n    g(x)\n}");
    accepts_body("if (Cfg { on: true }).on {\n    f()\n}");
    // A header waits for its body across the commas of its own brackets: a
    // parameter list separates parameters and ends nothing, so the brace
    // below is the body even where what is inside it reads as a set.
    accepts("fn f(a: i32, b: i32): i32 {\n    (a)\n}\n");
    accepts("fn divmod(a: i32, b: i32): (i32, i32) {\n    (a / b, a % b)\n}\n");
    accepts_body("if (a, b) == (c, d) {\n    f()\n    g()\n}");
    // A block nested inside a literal's entry is a block again.
    accepts_body("let m = {\n    1: {\n        f()\n        g()\n    },\n}");
    accepts_body("let p = Point {\n    x: if c {\n        f()\n        g()\n    } else { 2 },\n}");
}

#[test]
fn parses_match_and_patterns() {
    accepts_body("match x {\n    1 => a,\n    _ => b,\n}");
    accepts_body("match x {\n    1 => {\n        f()\n        g()\n    },\n    2 => h()\n}");
    accepts_body("let x = match c {\n    1 => 5,\n    _ => panic(\"no\"),\n}");
    accepts_body("match x {\n    Color::Red | Color::Blue => a,\n    Shape::Circle(r) => r,\n    Pair::Of(_, _) => 0,\n    Point { x: a, y } => a,\n    1..=9 => 1,\n    -1 => 2,\n}");
    accepts_body("match x {\n    1 => a\n}\n-1");
}

// Tuples: a type, a literal, a pattern and the `.0` that reaches into one. The
// comma makes each of them, so the group of one still groups.
#[test]
fn parses_tuples() {
    accepts("fn divmod(a: i32, b: i32): (i32, i32) {\n    (a / b, a % b)\n}\n");
    accepts("fn head(p: (i32, str)): i32 {\n    p.0\n}\n");
    accepts_body("let p: (i32, str) = (1, \"a\")");
    accepts_body("let t = (1, 2, 3)\nlet trailing = (1, 2,)");
    accepts_body("let nested: ((i32, i32), str) = ((1, 2), \"a\")");
    accepts_body("let pairs: (i32, str)[8]\nlet view: &(i32, str)[]");
    accepts_body("let v: Vec<(i32, str)> = empty()");
    accepts_body("let q = x as (i32, str)");
    accepts_body("let n = t.0 + t.1.0\nlet m = f().1\nlet k = ps[0].1");
    accepts_body("let swapped = (b, a)\n(a, b) = (b, a)");
    accepts_body("match p {\n    (0, 0) => a,\n    (x, y) => x,\n    _ => b,\n}");
    accepts_body("for x in (1, 2) {\n    f(x)\n    g(x)\n}");
    accepts_body("let f = |x| (x, x)\nlet t = (\n    1,\n    2,\n)");
    accepts("enum E {\n    B((i32, str)),\n}\n");
    accepts("impl (i32, str) {\n    fn first(this): i32;\n}\n");
    accepts("fn f<T>(p: (T, T)): T where T: Ord;\n");
    // A group of one is what it always was, and a call takes its own comma.
    accepts_body("let g = (1)\nlet refs: (&i32)[8]\nlet c = f(1, 2)");
    // Two members at least, so neither the empty tuple nor the one-tuple is
    // written -- in a type or in an expression.
    assert!(recognise("fn f(): () {}\n").is_err());
    assert!(recognise("fn f(): (i32,) {}\n").is_err());
    assert!(recognise("fn main() {\n    let t = (1,)\n}\n").is_err());
    assert!(recognise("fn main() {\n    let t = ()\n}\n").is_err());
}

#[test]
fn parses_unsafe() {
    accepts_body("unsafe {\n    let buf = malloc(n)\n    fill(buf, n)\n}");
    accepts_body("unsafe free(q)");
    accepts_body("unsafe p = P { x: 1 }");
    accepts_body("unsafe let p = malloc(n)");
    accepts_body("unsafe fn write(n: u64) {\n    f()\n}");
}

// `&` and `|` between two operands. Both already spelled other things -- a
// reference, a closure's parameters, a pattern's alternatives -- and each of
// those has to go on reading as it did.
#[test]
fn parses_the_bitwise_operators() {
    accepts_body("let m = a & b\nlet n = a | b\nlet o = a ^ b");
    accepts_body("let ok = a ^^ b\nlet p = (a && b) ^^ (c || d)");
    accepts_body("let m = a | b ^ c & d\nlet n = a || b ^^ c && d");
    accepts_body("let m = flags & 0xFF | 1\nlet n = (a | b) & c");
    accepts_body("let m = a & b << c | d >> e");
    accepts_body("let ok = a & b == 0\nlet p = x | y != 0");
    // Still a reference where nothing stands in front of it, and still one
    // where the thing in front of it is the operator.
    accepts_body("let r = &x\nlet m = a & &b\nlet rr: &&i32 = &&x");
    // Still the logical pair, which the lexer tells apart from these.
    accepts_body("let ok = a && b\nlet no = a || b\nlet x = a ^^ b");
    // Still a closure's parameters, with a `|` inside the body for good
    // measure, and still one after `move`.
    accepts_body("let f = |x: i32| x & 1\nlet g = || a | b\nlet h = move || a & b");
    // Still a pattern's alternatives, in a match whose arms are expressions
    // that use the operators themselves.
    accepts_body("match x {\n    1 | 2 => a & b,\n    _ => c | d,\n}");
    // And still the compound assignments, which were always spelled this way.
    accepts_body("a &= b\na |= b\na ^= b");
    // Only the single `^` takes the `=`. `a ^^= b` is `^^` and then a `=`,
    // which nothing takes -- there is no compound assignment for a logical
    // operator, and `a = a ^^ b` is how that is written.
    assert!(recognise("fn main() {\n    a ^^= b\n}\n").is_err());
    assert!(recognise("fn main() {\n    a &&= b\n}\n").is_err());
}

// `Copy` and `Drop` are traits the compiler knows by name, and neither needs a
// rule of its own: an empty impl body and a one-method impl are both written
// already. Nothing here is new grammar -- this pins that down so it stays true.
#[test]
fn copy_and_drop_need_no_grammar_of_their_own() {
    // `Drop` holds the one method, whose receiver writes to what it releases.
    accepts("impl Drop for Buf {\n    fn drop(this: *Buf) {\n        unsafe free(this.p)\n    }\n}\n");
    accepts("impl Drop for Buf {\n    fn drop(this: *Buf);\n}\n");
    // `Copy` holds nothing, so its body is empty.
    accepts("impl Copy for Point {}\n");
    accepts("trait Copy {}\n");
    accepts("trait Drop {\n    fn drop(this: *This);\n}\n");
    // Both compose with everything an impl already takes: parameters, a
    // `where` clause, and the lifetimes of section 3.
    accepts("impl<T> Drop for Vec<T> {\n    fn drop(this: *Vec<T>);\n}\n");
    accepts("impl<T> Copy for Pair<T> where T: Copy {}\n");
    accepts("impl<~a> Drop for Parser<~a> {\n    fn drop(this: *Parser<~a>);\n}\n");
    accepts("impl<~a, T> Drop for Held<~a, T> where T: ~a {\n    fn drop(this: *Held<~a, T>);\n}\n");
}

// A macro is declared with a keyword and invoked with `@`. Its parameters are
// `$name:fragment`, and the fragment is an IDENTIFIER the checker knows rather
// than a keyword the grammar does.
#[test]
fn parses_macros() {
    accepts("macro twice($x:expr) {\n    $x\n    $x\n}\n");
    accepts("macro nothing() {\n    f()\n}\n");
    accepts("macro pair($a:expr, $b:expr) {\n    ($a, $b)\n}\n");
    // A macro is a declaration, so it takes attributes and a visibility, and
    // stands inside a namespace or a block like any other.
    accepts("%deprecated(\"use log\")\npublic macro shout($m:expr) {\n    print($m)\n}\n");
    accepts("namespace m {\n    macro one($x:expr) {\n        $x\n    }\n}\n");
    accepts_body("macro inner($x:expr) {\n    $x\n}\nlet n = 1");
    // The invocation is an operand, so it stands wherever a value does.
    accepts_body("let n = @twice(f())");
    accepts_body("@log(\"started\")");
    accepts_body("f(@twice(x), 1)");
    accepts_body("let n = @nothing() + 1");
    // A `$x` stands in the three places its fragment might let it: an operand,
    // a type, and a pattern.
    accepts("macro m($x:expr, $t:ident, $p:ident) {\n    let v: $t = $x\n    match v {\n        $p => 1,\n        _ => 2,\n    }\n}\n");
    accepts("macro g($t:ident) {\n    let v: Vec<$t> = empty()\n}\n");
    // A fragment is an IDENTIFIER here, so the grammar takes any word; which
    // words are fragments is the expander's, and `banana` is its error.
    accepts("macro b($x:banana) {\n    $x\n}\n");
    // A macro needs a name after its sigil, and its parameters need fragments.
    assert!(recognise("fn main() {\n    let n = @(1)\n}\n").is_err());
    assert!(recognise("macro m($x) {\n    $x\n}\n").is_err());
}

// `%` spells the remainder operator and an attribute both, and where it stands
// is the whole of what tells them apart -- the rule `*` already follows.
#[test]
fn percent_is_an_attribute_and_an_operator() {
    accepts_body("let r = a % b\nlet s = a%b\nlet t = 7 % 2");
    accepts("%inline\nfn f();\n");
    // After a statement ends, a `%` glued to a name is the attribute.
    accepts("let x = 1\n%inline\nfn f();\n");
    // A declaration inside a block takes no attributes -- `<statement>` is a
    // bare `<declaration>`, where an `<item>` carries the list -- so what is
    // checked here is only that the lexer hands the attribute over.
    accepts("let v = a % b\n%inline\nfn g();\n");
}

// A declaration may take more than one generic parameter. The commas between
// them sit in a `<..>` that `bracket_depth` does not count, so the header has
// to keep waiting for its body across them -- exactly as it does across the
// commas of a parameter list.
#[test]
fn a_header_survives_the_commas_of_its_generic_parameters() {
    accepts("struct Pair<A, B> {\n    l: A,\n    r: B,\n}\n");
    accepts("enum Either<A, B> {\n    L(A),\n    R(B),\n}\n");
    accepts("trait Into<A, B> {\n    fn into(this): B;\n}\n");
    accepts("impl<A, B> Into<A, B> for Pair<A, B> {\n    fn into(this): B;\n}\n");
    accepts("fn zip<A, B>(a: A, b: B): (A, B) {\n    (a, b)\n}\n");
    // Three of them, and one carrying bounds, still leave the brace alone.
    accepts("struct T3<A, B, C> {\n    a: A,\n}\n");
    accepts("struct Ord2<A: Ord, B: Ord + Show> {\n    a: A,\n}\n");
    // And a nested argument list inside the parameters is still not the body.
    accepts("struct Held<A, B> {\n    m: Map<A, Vec<B>>,\n}\n");
}

// A lifetime is `~a`: one token, since `~` spells nothing else. It stands as a
// parameter, as a type argument, in front of what a reference refers to, and on
// either side of a `where` predicate's colon.
#[test]
fn parses_lifetimes() {
    accepts("fn longest<~a>(x: &~a str, y: &~a str): &~a str;\n");
    accepts("struct Parser<~a> {\n    text: &~a str,\n}\n");
    accepts("struct Pair<~a, ~b, T> {\n    l: &~a T,\n    r: &~b T,\n}\n");
    // Bounds, both kinds, inline and in a `where`.
    accepts("fn f<~a, ~b: ~a, T: Show + ~a>(x: &~a T);\n");
    accepts("fn f<~a, T>(x: &~a T) where T: ~a, ~a: ~b;\n");
    accepts("impl<~a> Show for Parser<~a> {\n    fn show(this: &~a Parser<~a>): str;\n}\n");
    // A mutable reference names one the same way, and a view is a reference.
    accepts_body("let w: *~a i32 = *a\nlet v: &~a i32[] = &a");
    // Nested arguments still close: the `>>` splits with a lifetime inside.
    accepts_body("let m: Map<~a, Vec<&~b str>> = empty()");
    accepts_body("let n: Vec<Vec<~a>> = empty()");
    // `~_` is the one with no name worth giving.
    accepts_body("let p: &~_ i32 = &x");
    // A lifetime is not a value, and `~` alone is not a lifetime.
    assert!(recognise("fn main() {\n    let x = ~a\n}\n").is_err());
    assert!(recognise("fn f<~>(x: i32);\n").is_err());
}

// The `~` of a lifetime takes nothing away from a char literal, which is what
// the spelling was chosen for: `'a'` needs no lookahead to stay itself.
#[test]
fn a_lifetime_leaves_char_literals_alone() {
    accepts_body("let c = 'a'\nlet d = '\\n'");
    accepts("fn f<~a>(c: char, s: &~a str): char { 'x' }\n");
}

#[test]
fn parses_wildcards_and_discards() {
    accepts_body("let _ = f()\nfor _ in 0..3 {}\nlet _foo = 1");
    accepts("fn f(_: i32) {}\n");
}

// The readings given up to keep the tables free of conflicts.
#[test]
fn rejects_what_the_grammar_gave_up() {
    // A cast names no type arguments; parenthesise to say it.
    assert!(recognise("fn main() {\n    let v = x as Vec<i32>\n}\n").is_err());
    accepts_body("let v = x as (Vec<i32>)");
    // A block form is a whole expression, not an operand.
    assert!(recognise("fn main() {\n    let n = 1 + if c { 1 } else { 2 }\n}\n").is_err());
    accepts_body("let n = 1 + (if c { 1 } else { 2 })");
    // A jump says all it has to say on its own.
    assert!(recognise("fn main() {\n    let f = || break\n}\n").is_err());
    accepts_body("let f = || { break }");
}

// The message an error carries: where, what was wanted, what was there.
#[test]
fn says_what_it_expected() {
    // A state that permits one thing says which thing.
    assert_eq!(
        recognise("struct 3 {}\n").unwrap_err(),
        "1:8: expected an identifier, found an integer literal"
    );
    assert_eq!(
        recognise("fn f(x i32);\n").unwrap_err(),
        "1:8: expected `:`, `,` or `)`, found `i32`"
    );
    // A state that permits the start of any expression says so, rather than
    // spelling out the fifty terminals that begin one.
    assert_eq!(
        recognise("fn f() {\n    let x = ;\n}\n").unwrap_err(),
        "2:13: expected an expression, found `;`"
    );
    // A state partway through one names what may carry it on. `*` cannot: the
    // parser has an additive in hand, and that is the looseness `an operator`
    // buys -- the terminals it leaves out are not listed either.
    assert_eq!(
        recognise("fn f() {\n    let x = 1 + 2 3\n}\n").unwrap_err(),
        "2:19: expected an operator, `}` or `;`, found an integer literal"
    );
}

// A token the lexer could not read is not a terminal, so no state has an action
// for it. What it says of itself is the whole message.
#[test]
fn says_what_the_lexer_could_not_read() {
    assert_eq!(
        recognise("fn f() {\n    let x = ?\n}\n").unwrap_err(),
        "2:13: Unexpected character '?'"
    );
    assert_eq!(
        recognise("fn f() {\n    let s = \"oops\n}\n").unwrap_err(),
        "2:13: Unterminated string"
    );
}









