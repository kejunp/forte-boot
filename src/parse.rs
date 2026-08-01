pub mod tables;

/// Runs the generated tables over a token stream and says whether they accept
/// it. No tree is built: this is the tables' own test, and what it tests is
/// that the grammar and the lexer agree about the language.
#[cfg(test)]
fn recognise(source: &str) -> Result<(), String> {
    use crate::lex::lexer::Lexer;
    use tables::{action, goto, terminal_of, Action, RULES};

    let mut lexer = Lexer::new(source);
    let mut stack = vec![0usize];
    loop {
        let tok = lexer.peek();
        let terminal = terminal_of(&tok.toktype)
            .ok_or_else(|| format!("{}:{}: {:?}", tok.line, tok.col, tok.toktype))?;
        let state = *stack.last().unwrap();
        match action(state, terminal) {
            Action::Shift(next) => {
                lexer.next_token();
                stack.push(next as usize);
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

/// A statement is not an item, so the snippets that are statements are given a
/// function to stand in.
#[cfg(test)]
fn accepts_body(body: &str) {
    accepts(&format!("fn main() {{\n{}\n}}\n", body));
}

/// Every declaration a file can hold, in the spellings the lexer's own tests
/// use. The two halves have to agree: the grammar decides what a `{` may be
/// only because the lexer has already decided what this one is.
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
    accepts("namespace limits {\n    public const MAX: i32 = 255\n}\n");
    accepts("@inline\n@repr(C)\npublic fn f();\n");
    accepts("@symbol(\"malloc\")\nfn malloc(n: u64): *u8;\n");
    accepts("const fn square(n: i32): i32 { n * n }\n");
    accepts("public unsafe fn write(dst: *u8[], n: u64);\n");
    accepts("fn panic(m: str): never;\n");
    accepts("fn log(m: str): null;\n");
    accepts("fn f() {\n    let x = 1\n    g(x)\n}\n");
}

/// The statement and expression forms, from the same source.
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
    accepts_body("let c = shapes.Color::Red\nlet n = limits::MAX");
    accepts_body("let found = for x in xs {\n    if p(x) { break x }\n}");
    accepts_body("while true {\n    break\n    continue\n}");
    accepts_body("return");
}

/// A `{` is a block or a value, and the lexer says which. Every one of these
/// turns on it.
#[test]
fn parses_braces_of_both_kinds() {
    // A literal, and a block whose statements sit in the same place.
    accepts_body("let p = Point {\n    x: 1,\n    y: 2,\n}");
    accepts_body("let p = shapes.Point { x: 1 }");
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

#[test]
fn parses_unsafe() {
    accepts_body("unsafe {\n    let buf = malloc(n)\n    fill(buf, n)\n}");
    accepts_body("unsafe free(q)");
    accepts_body("unsafe p = P { x: 1 }");
    accepts_body("unsafe let p = malloc(n)");
    accepts_body("unsafe fn write(n: u64) {\n    f()\n}");
}

#[test]
fn parses_wildcards_and_discards() {
    accepts_body("let _ = f()\nfor _ in 0..3 {}\nlet _foo = 1");
    accepts("fn f(_: i32) {}\n");
}

/// What the grammar is not: the cases where a reading had to be given up to
/// keep the tables free of conflicts.
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

/// The message an error carries: where it is, what was wanted, what was there.
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
    // A state that permits the start of any expression counts the rest rather
    // than spelling out most of the terminals there are.
    let e = recognise("fn f() {\n    let x = ;\n}\n").unwrap_err();
    assert!(e.starts_with("2:13: expected "), "{e}");
    assert!(e.contains(" more, found `;`"), "{e}");
}
