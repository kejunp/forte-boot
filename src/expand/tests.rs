// What expansion makes of a tree, checked against the tree it should make.
use super::*;
use crate::lex::lexer::Lexer;
use crate::prep::preprocess;

// Parses, expands, and gives back the arena and the expanded root. The parse
// must succeed: what expansion does with a broken tree is not what is tested.
fn expanded(source: &str) -> (Parser, ASTNode, Diagnostics) {
    let prepped = preprocess(source);
    let mut p = Parser::new(Lexer::new(&prepped));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{}\n{:#?}", source, p.errors());
    let (root, errors) = {
        let mut e = Expander::new(&mut p);
        let out = e.expand(&root);
        (out, e.errors().clone())
    };
    (p, root, errors)
}

fn items(root: &ASTNode) -> Vec<ASTNodeId> {
    match &root.kind {
        ASTNodeKind::Program(items) => items.clone(),
        other => panic!("a file built {:?}", other),
    }
}

// The messages expansion drew, rendered against the source as written.
fn errors_in(source: &str) -> Vec<String> {
    let (_, _, errors) = expanded(source);
    let text: Vec<char> = source.chars().collect();
    let quoted = crate::error::Source::new("input.ft", &text);
    errors.iter().map(|e| e.render(&quoted)).collect()
}

// Nothing that reaches the other side is a macro: not the call, and not the
// declaration it named.
fn no_macros_left(p: &Parser, root: &ASTNode) {
    let mut seen = vec![false; 1];
    let mut walk = vec![root.kind.clone()];
    while let Some(mut kind) = walk.pop() {
        assert!(
            !matches!(kind, ASTNodeKind::MacroCall { .. }
                          | ASTNodeKind::MacroDecl { .. }
                          | ASTNodeKind::MacroVar(_)),
            "a macro survived expansion: {:?}",
            kind
        );
        for child in children_mut(&mut kind).into_iter().map(|s| *s) {
            if child >= seen.len() {
                seen.resize(child + 1, false);
            }
            if !seen[child] {
                seen[child] = true;
                walk.push(p.get_node(child).kind.clone());
            }
        }
    }
}

#[test]
fn a_call_becomes_the_body_with_its_arguments_put_in() {
    // The `;` makes the call a statement, so the expansion sits where it is
    // easy to name; without one it would be the block's trailing expression.
    let source = "macro twice($x:expr) {
    $x
    $x
}
fn main() {
    @twice(f());
}
";
    let (p, root, errors) = expanded(source);
    assert!(errors.is_empty(), "{:#?}", errors);
    no_macros_left(&p, &root);

    // The declaration is gone, so `fn main` is the only item left.
    let items = items(&root);
    assert_eq!(items.len(), 1);
    assert!(matches!(p.get_node(items[0]).kind, ASTNodeKind::Fn { .. }));

    let body = match &p.get_node(items[0]).kind {
        ASTNodeKind::Fn { body: Some(id), .. } => *id,
        other => panic!("{:?}", other),
    };
    let stmts = match &p.get_node(body).kind {
        ASTNodeKind::Block { stmts, .. } => stmts.clone(),
        other => panic!("{:?}", other),
    };
    assert_eq!(stmts.len(), 1, "the one statement of `fn main`");
    let inner = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };

    // What the call became is the macro's block: `$x` once as a statement and
    // once as the value, since nothing separated the second from the `}`.
    let (first, tail) = match &p.get_node(inner).kind {
        ASTNodeKind::Block { stmts, tail } => {
            assert_eq!(stmts.len(), 1, "the block the macro stood for");
            (stmts[0], tail.expect("a trailing expression"))
        }
        other => panic!("the expansion built {:?}", other),
    };

    // Two subtrees and not one handle used twice: `$x` twice is the argument
    // twice, which is what makes it evaluated twice.
    assert_ne!(first, tail);
    let called = match &p.get_node(first).kind {
        ASTNodeKind::ExprStmt(e) => *e,
        other => panic!("{:?}", other),
    };
    assert!(matches!(p.get_node(called).kind, ASTNodeKind::Call { .. }));
    assert!(matches!(p.get_node(tail).kind, ASTNodeKind::Call { .. }));
}

#[test]
fn a_macro_may_take_no_arguments_and_may_be_nested() {
    let source = "macro one() {\n    1\n}\nmacro two() {\n    @one() + @one()\n}\nfn main() {\n    let n = @two()\n}\n";
    let (p, root, errors) = expanded(source);
    assert!(errors.is_empty(), "{:#?}", errors);
    no_macros_left(&p, &root);
    assert_eq!(items(&root).len(), 1);
}

// A macro declared inside a namespace is found, and the namespace loses it.
#[test]
fn a_namespace_holds_macros_and_gives_them_up() {
    let source = "namespace m {\n    macro one() {\n        1\n    }\n}\nfn main() {\n    let n = @one()\n}\n";
    let (p, root, errors) = expanded(source);
    assert!(errors.is_empty(), "{:#?}", errors);
    no_macros_left(&p, &root);
    let items = items(&root);
    let inner = match &p.get_node(items[0]).kind {
        ASTNodeKind::Namespace { items, .. } => items.clone(),
        other => panic!("{:?}", other),
    };
    assert!(inner.is_empty(), "the namespace kept {:?}", inner);
}

#[test]
fn an_unknown_macro_is_an_error_where_it_is_written() {
    assert_eq!(
        errors_in("fn main() {\n    @nope(1)\n}\n"),
        vec![
            "\
error: unknown macro `@nope`
 --> input.ft:2:5
  |
2 |     @nope(1)
  |     ^ no macro of this name
  |
  = help: a macro is declared with `macro`, and the set is not open"
        ]
    );
}

#[test]
fn the_wrong_number_of_arguments_says_so_and_points_at_the_declaration() {
    let messages = errors_in("macro one($x:expr) {\n    $x\n}\nfn main() {\n    @one(1, 2)\n}\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("takes 1 argument, and 2 were given"), "{}", messages[0]);
    assert!(messages[0].contains("declared here"), "{}", messages[0]);
}

#[test]
fn a_fragment_is_checked_against_what_was_handed_over() {
    let messages = errors_in("macro n($x:ident) {\n    $x\n}\nfn main() {\n    @n(1 + 2)\n}\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("`$x` wants a name, and was given an operation"), "{}", messages[0]);
    // A name is what it wanted, so this one draws nothing.
    assert!(errors_in("macro n($x:ident) {\n    $x\n}\nfn main() {\n    @n(y)\n}\n").is_empty());
    // And `expr` asks nothing of what it is given.
    assert!(errors_in("macro e($x:expr) {\n    $x\n}\nfn main() {\n    @e(1 + 2)\n}\n").is_empty());
}

#[test]
fn an_unknown_fragment_is_an_error_where_it_is_declared() {
    let messages = errors_in("macro t($x:banana) {\n    $x\n}\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("unknown fragment `banana`"), "{}", messages[0]);
    assert!(messages[0].contains("`expr`, `ident`, `lit`"), "{}", messages[0]);
}

#[test]
fn a_macro_declared_twice_says_where_the_first_one_was() {
    let messages = errors_in("macro m() {\n    1\n}\nmacro m() {\n    2\n}\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("declared twice"), "{}", messages[0]);
    assert!(messages[0].contains("first declared here"), "{}", messages[0]);
}

// A macro that invokes itself has nothing to stop it, so the depth does.
#[test]
fn a_macro_that_never_stops_is_stopped() {
    let messages = errors_in("macro loop_it() {\n    @loop_it()\n}\nfn main() {\n    @loop_it()\n}\n");
    assert!(!messages.is_empty());
    assert!(messages[0].contains("expanded 64 deep"), "{}", messages[0]);
}

// A `ptr` holds a type, so substitution has to reach through one: the walk that
// puts arguments in descends into every child a node has, and a pointer's
// referent is a child like any other. What arrives is the name shaped as the
// expression it was written as, which lowering makes a type of -- see
// `a_pointer_holds_a_name_a_macro_put_there`.
#[test]
fn a_name_is_put_in_under_a_pointer() {
    let source = "macro hold($t:ident) {\n    unsafe let p: ptr $t = addr y\n}\nfn main() {\n    @hold(Node);\n}\n";
    let (p, root, errors) = expanded(source);
    assert!(errors.is_empty(), "{:#?}", errors);
    no_macros_left(&p, &root);

    let mut walk = vec![root.kind.clone()];
    let mut found = false;
    while let Some(mut kind) = walk.pop() {
        if let ASTNodeKind::PtrType(inner) = kind {
            assert_eq!(p.get_node(inner).kind, ASTNodeKind::Ident("Node".to_string()));
            found = true;
        }
        for id in super::children_mut(&mut kind) {
            walk.push(p.get_node(*id).kind.clone());
        }
    }
    assert!(found, "no pointer type in the expansion of {}", source);
}

// ---- What a `%derive` stands for --------------------------------------------

// The impl is in the tree after this pass and the reader wrote none, which is
// the whole claim: `sema` is handed a file it cannot tell from one that was
// typed. What the impl *does* is `src/tests.rs`', running being the only thing
// that can say.
fn impls_in(p: &Parser, root: &ASTNode) -> Vec<String> {
    items(root)
        .iter()
        .filter_map(|&i| match &p.get_node(i).kind {
            ASTNodeKind::Impl { for_ty: Some(held), .. } => {
                Some(format!("{:?}", p.get_node(*held).kind))
            }
            _ => None,
        })
        .collect()
}

#[test]
fn a_derive_writes_the_impl_it_stands_for() {
    let (p, root, errors) = expanded(
        "%derive(Show)\nstruct Point {\n    pub x: i64,\n    pub y: i64,\n}\n",
    );
    assert!(errors.is_empty(), "{:#?}", errors);
    let held = impls_in(&p, &root);
    assert_eq!(held.len(), 1, "one impl was meant to appear: {:?}", held);
    assert!(held[0].contains("Point"), "{:?}", held);
}

// Two derives on one declaration are two impls, and a declaration with none is
// left as it was.
#[test]
fn a_declaration_with_no_derive_grows_nothing() {
    let (p, root, _) = expanded("struct Point {\n    pub x: i64,\n}\n");
    assert!(impls_in(&p, &root).is_empty());
}

// A name this compiler does not know how to write. The set is closed as the
// attributes' own set is, and for the same reason: the body is the thing that
// has to exist, and only what is listed has one.
#[test]
fn a_derive_of_something_unwritten_is_refused() {
    let said = errors_in("%derive(Clone)\nstruct Point {\n    pub x: i64,\n}\n");
    assert_eq!(said.len(), 1, "{:#?}", said);
    assert!(said[0].contains("`Clone` is not something `%derive` writes"), "{}", said[0]);
    assert!(said[0].contains("`Show`"), "{}", said[0]);
}

// An enum is a choice among shapes and gets a `match` over them, which is a
// second body this writes and not a second thing it refuses.
#[test]
fn a_derive_on_an_enum_writes_a_match_over_its_variants() {
    let (p, root, errors) = expanded(
        "%derive(Show)\nenum Held {\n    One,\n    Two(i64),\n    Three { x: i64 },\n}\n",
    );
    assert!(errors.is_empty(), "{:#?}", errors);
    assert_eq!(impls_in(&p, &root).len(), 1);
}

// A declaration with parameters gets an impl with the same ones, each bounded
// by the trait: every field of a `T` has to answer `Show` for the body to be
// able to ask it, and there is nothing else the bound could be.
#[test]
fn a_derive_on_a_declaration_with_parameters_bounds_them() {
    let (p, root, errors) = expanded("%derive(Show)\nstruct Box<T> {\n    pub held: T,\n}\n");
    assert!(errors.is_empty(), "{:#?}", errors);
    assert_eq!(impls_in(&p, &root).len(), 1);
    // And of an enum, which takes them the same way and for the same reason.
    let (p, root, errors) = expanded("%derive(Show)\nenum Held<T> {\n    One(T),\n}\n");
    assert!(errors.is_empty(), "{:#?}", errors);
    assert_eq!(impls_in(&p, &root).len(), 1);
}

// A derive inside a namespace is a derive like any other: a namespace holds
// items and this walks into one.
#[test]
fn a_derive_inside_a_namespace_is_written_too() {
    let (p, root, errors) = expanded(
        "namespace held {\n    %derive(Show)\n    struct Point {\n        pub x: i64,\n    }\n}\n",
    );
    assert!(errors.is_empty(), "{:#?}", errors);
    // At the file's top level, where every impl in a suite lives: an impl is
    // found by the type it is written for and not by where it stands.
    assert_eq!(impls_in(&p, &root).len(), 1);
}
