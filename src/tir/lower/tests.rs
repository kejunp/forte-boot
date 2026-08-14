// What lowering makes of a tree, checked against the TIR it should make.

use super::*;
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::prep::preprocess;

// Parses, expands and lowers. The parse and the expansion must both succeed:
// what lowering does with a broken tree is not what is under test here.
fn lowered(source: &str) -> (TIRProgram, Diagnostics) {
    let prepped = preprocess(source);
    let mut p = Parser::new(Lexer::new(&prepped));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{}\n{:#?}", source, p.errors());
    let root = {
        let mut e = Expander::new(&mut p);
        let out = e.expand(&root);
        assert!(e.errors().is_empty(), "{}\n{:#?}", source, e.errors());
        out
    };
    let mut l = Lowerer::new(&p);
    l.lower(&root);
    let errors = l.errors().clone();
    (l.finish(), errors)
}

fn clean(source: &str) -> TIRProgram {
    let (tir, errors) = lowered(source);
    assert!(errors.is_empty(), "{}\n{:#?}", source, errors);
    tir
}

// The messages lowering drew, rendered against the source as written.
fn errors_in(source: &str) -> Vec<String> {
    let (_, errors) = lowered(source);
    let text: Vec<char> = source.chars().collect();
    let quoted = crate::error::Source::new("input.fc", &text);
    errors.iter().map(|e| e.render(&quoted)).collect()
}

fn only_fn(tir: &TIRProgram) -> &TIRFn {
    assert_eq!(tir.roots.len(), 1);
    match &tir.items[tir.roots[0]].kind {
        TIRItemKind::Fn(f) => f,
        other => panic!("{:?}", other),
    }
}

fn body_of<'a>(tir: &'a TIRProgram, f: &TIRFn) -> &'a TIRExprKind {
    &tir.exprs[f.body.expect("a body")].kind
}

// The `elif`s the AST keeps as written become nested `If`s, so every pass below
// reads one shape instead of two.
#[test]
fn elifs_fold_into_nested_ifs() {
    let tir = clean("fn main() {\n    if a {\n        1\n    } elif b {\n        2\n    } elif c {\n        3\n    } else {\n        4\n    }\n}\n");
    let f = only_fn(&tir);
    let tail = match body_of(&tir, f) {
        TIRExprKind::Block { tail, .. } => tail.expect("the if is the block's value"),
        other => panic!("{:?}", other),
    };
    // if a { .. } else { if b { .. } else { if c { .. } else { .. } } }
    let mut depth = 0;
    let mut here = tail;
    loop {
        match &tir.exprs[here].kind {
            TIRExprKind::If { els, .. } => {
                depth += 1;
                match els {
                    Some(next) => here = *next,
                    None => panic!("the last `else` went missing"),
                }
            }
            TIRExprKind::Block { .. } => break,
            other => panic!("{:?}", other),
        }
    }
    assert_eq!(depth, 3, "one `if` and two `elif`s");
}

// One AST node, two TIR shapes: a global at file scope, a `let` in a block.
#[test]
fn a_var_decl_is_a_global_or_a_let_by_where_it_stands() {
    let tir = clean("pub var n: i32 = 1\nfn main() {\n    let x = 2\n    g(x)\n}\n");
    assert_eq!(tir.roots.len(), 2);
    match &tir.items[tir.roots[0]].kind {
        TIRItemKind::Global { vis, intro, name, .. } => {
            assert_eq!(*vis, TIRVis::Pub);
            assert_eq!(*intro, TIRIntro::Var);
            assert_eq!(*name, TIRBinding::Name("n".to_string()));
        }
        other => panic!("{:?}", other),
    }

    let f = match &tir.items[tir.roots[1]].kind {
        TIRItemKind::Fn(f) => f,
        other => panic!("{:?}", other),
    };
    match body_of(&tir, f) {
        TIRExprKind::Block { stmts, .. } => match &stmts[0] {
            TIRStmt::Let { intro, name, is_unsafe, .. } => {
                assert_eq!(*intro, TIRIntro::Let);
                assert_eq!(*name, TIRBinding::Name("x".to_string()));
                assert!(!is_unsafe);
            }
            other => panic!("{:?}", other),
        },
        other => panic!("{:?}", other),
    }
}

// `unsafe` in front of a statement becomes a flag on it: there are exactly two
// statements it can prefix, and a node wrapped round one said no more.
#[test]
fn unsafe_becomes_a_flag_on_the_statement() {
    let tir = clean("fn main() {\n    unsafe let b = malloc(n)\n    unsafe free(b)\n    g();\n}\n");
    let f = only_fn(&tir);
    let stmts = match body_of(&tir, f) {
        TIRExprKind::Block { stmts, .. } => stmts,
        other => panic!("{:?}", other),
    };
    assert!(matches!(stmts[0], TIRStmt::Let { is_unsafe: true, .. }));
    assert!(matches!(stmts[1], TIRStmt::Expr { is_unsafe: true, .. }));
    assert!(matches!(stmts[2], TIRStmt::Expr { is_unsafe: false, .. }));
}

// The three payload nodes become one enum, leaving no fourth state to handle.
#[test]
fn the_three_payloads_become_one() {
    let tir = clean("enum E {\n    A,\n    B(i32, str),\n    C { x: i32 },\n    D = 4,\n}\n");
    let variants = match &tir.items[tir.roots[0]].kind {
        TIRItemKind::Enum { variants, .. } => variants,
        other => panic!("{:?}", other),
    };
    assert_eq!(variants.len(), 4);
    assert!(matches!(variants[0].payload, TIRPayload::None));
    assert!(matches!(&variants[1].payload, TIRPayload::Tuple(t) if t.len() == 2));
    assert!(matches!(&variants[2].payload, TIRPayload::Named(f) if f.len() == 1));
    assert!(matches!(variants[3].payload, TIRPayload::Discriminant(_)));
}

// A generic list holds both kinds in the order they were written, and a bound
// is a trait or a lifetime.
#[test]
fn generics_and_bounds_keep_both_kinds() {
    let tir = clean("fn f<'a, T: Show + 'a>(x: &'a T) where T: 'a, 'a: 'b;\n");
    let f = only_fn(&tir);
    assert_eq!(f.generics.len(), 2);
    match &f.generics[0] {
        TIRGeneric::Life { name, bounds } => {
            assert_eq!(name, "a");
            assert!(bounds.is_empty());
        }
        other => panic!("{:?}", other),
    }
    match &f.generics[1] {
        TIRGeneric::Type { name, bounds } => {
            assert_eq!(name, "T");
            assert_eq!(bounds.len(), 2);
            assert!(matches!(bounds[0], TIRBound::Trait(_)));
            assert!(matches!(&bounds[1], TIRBound::Life(l) if l == "a"));
        }
        other => panic!("{:?}", other),
    }
    // A `where` takes a lifetime on either side of its colon.
    assert_eq!(f.wheres.len(), 2);
    assert!(matches!(f.wheres[0].subject, TIRBound::Trait(_)));
    assert!(matches!(&f.wheres[1].subject, TIRBound::Life(l) if l == "a"));

    // The parameter's `&'a T` keeps the lifetime it was written with.
    let ty = f.params[0].ty.expect("a type");
    match &tir.types[ty].kind {
        TIRTypeKind::Ref { op, life, .. } => {
            assert_eq!(*op, TIRRefOp::Imm);
            assert_eq!(life.as_deref(), Some("a"));
        }
        other => panic!("{:?}", other),
    }
}

// `.` and `::` look alike once resolved and are kept apart until then, since
// which was written is what the resolver is about to read.
#[test]
fn a_dot_and_a_path_stay_different() {
    let tir = clean("fn main() {\n    let n = shapes::Color::Red.name\n}\n");
    let f = only_fn(&tir);
    let tail = match body_of(&tir, f) {
        TIRExprKind::Block { stmts, .. } => match &stmts[0] {
            TIRStmt::Let { init: Some(id), .. } => *id,
            other => panic!("{:?}", other),
        },
        other => panic!("{:?}", other),
    };
    // `.name` outermost, then `::Red`, then `::Color`, then the name.
    let base = match &tir.exprs[tail].kind {
        TIRExprKind::Field { base, name } => {
            assert_eq!(name, "name");
            *base
        }
        other => panic!("the outermost is {:?}", other),
    };
    let base = match &tir.exprs[base].kind {
        TIRExprKind::Path { base, name } => {
            assert_eq!(name, "Red");
            *base
        }
        other => panic!("{:?}", other),
    };
    assert!(matches!(&tir.exprs[base].kind, TIRExprKind::Path { name, .. } if name == "Color"));
}

// A macro that puts a name where a type belongs is normalised here: the parser
// would have built a `Named`, and this is where the expanded tree is put right.
#[test]
fn a_name_substituted_into_a_type_becomes_a_named_type() {
    let tir = clean("macro g($t:ident) {\n    let v: Vec<$t> = empty()\n}\nfn main() {\n    @g(Point);\n}\n");
    let named = tir.types.iter().any(|t| {
        matches!(&t.kind, TIRTypeKind::Named { path, .. } if path == &vec!["Point".to_string()])
    });
    assert!(named, "the substituted name is not a type: {:#?}", tir.types);
}

// ---- Attributes -----------------------------------------------------------

#[test]
fn the_six_attributes_become_fields() {
    let tir = clean("%symbol(\"malloc\")\n%must_use\n%noinline\n%deprecated(\"use alloc\")\n%test\nfn f();\n");
    let f = only_fn(&tir);
    assert_eq!(f.attrs.symbol.as_deref(), Some("malloc"));
    assert!(f.attrs.must_use);
    assert_eq!(f.attrs.inline, TIRInline::Never);
    assert_eq!(f.attrs.common.deprecated.as_deref(), Some("use alloc"));
    assert!(f.attrs.is_test);

    // Nothing written is not `Never`: it is the answer the backend still has.
    let tir = clean("fn f();\n");
    assert_eq!(only_fn(&tir).attrs.inline, TIRInline::Unwritten);
}

#[test]
fn an_unknown_attribute_names_what_was_probably_meant() {
    let messages = errors_in("%inlien\nfn f();\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("unknown attribute `%inlien`"), "{}", messages[0]);
    assert!(messages[0].contains("did you mean `%inline`?"), "{}", messages[0]);

    // Nothing near enough to guess at gets the list instead.
    let messages = errors_in("%banana\nfn f();\n");
    assert!(messages[0].contains("the attributes are"), "{}", messages[0]);
}

#[test]
fn an_attribute_on_the_wrong_declaration_says_so() {
    let messages = errors_in("%symbol(\"s\")\nstruct P {\n    x: i32,\n}\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("`%symbol` goes on a function"), "{}", messages[0]);
    assert!(messages[0].contains("this is a struct"), "{}", messages[0]);

    // `%deprecated` is the one that goes on anything.
    assert!(errors_in("%deprecated(\"go\")\nstruct P {\n    x: i32,\n}\n").is_empty());
}

#[test]
fn an_attributes_arguments_are_checked() {
    let messages = errors_in("%symbol\nfn f();\n");
    assert!(messages[0].contains("`%symbol` takes one string"), "{}", messages[0]);

    let messages = errors_in("%symbol(1)\nfn f();\n");
    assert!(messages[0].contains("takes a string"), "{}", messages[0]);
    assert!(messages[0].contains("an integer"), "{}", messages[0]);

    let messages = errors_in("%inline(C)\nfn f();\n");
    assert!(messages[0].contains("`%inline` takes no arguments"), "{}", messages[0]);
}

#[test]
fn inline_and_noinline_contradict_and_a_repeat_is_refused() {
    let messages = errors_in("%inline\n%noinline\nfn f();\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("contradict"), "{}", messages[0]);
    assert!(messages[0].contains("the first one is here"), "{}", messages[0]);

    let messages = errors_in("%inline\n%inline\nfn f();\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("`%inline` is written twice"), "{}", messages[0]);
}

// Everything the parser's own coverage source holds, lowered. It exercises every
// declaration form the language has, lifetimes and all; what is asserted is that
// none of it reaches an arm that panics and none of it draws a diagnostic.
#[test]
fn the_whole_language_lowers() {
    let source = "import a::b as c;\n\
                  pub import a::{b, c::*, d::{e, f as g}};\n\
                  pub(suite) import super::super::h::*;\n\
                  import suite::i::j;\n\
                  %deprecated(\"go\")\n\
                  pub const unsafe fn f<'a, T: Ord + 'a>(&self, x: *i32[2]): (bool, i32)\n\
                      where T: 'a {\n\
                      let y = -x.a as i64 .. 3;\n\
                      let t: (i32, str) = (1, \"a\");\n\
                      let u = t.1;\n\
                      let v = suite::limits::MAX + super::k::n;\n\
                      let w: super::Node = self;\n\
                      if y { g(#{1: 2}, {,}, [1]) } else { move |z| z + 1 };\n\
                      while y { continue }\n\
                      for i in 0..=9 { break }\n\
                      unsafe q = 1;\n\
                      match x {\n\
                          1..=2 => a,\n\
                          -3 => b,\n\
                          P::Q(m) => m,\n\
                          (m, _) => m,\n\
                          P { n: o } => o,\n\
                          _ => return,\n\
                      }\n\
                  }\n\
                  namespace n {\n\
                      const K: i32 = 1;\n\
                      var g: i32 = 2;\n\
                      enum E { A, B(i32), C { x: i32 }, D = 4 }\n\
                      struct S<T> { priv v: T[] }\n\
                      trait W { fn w<T>(&self, t: T): str where T: Ord; }\n\
                      impl W for S<i32> { priv fn w(&self): str { P { r: 1 } } }\n\
                      impl S<i32> { fn take(self); fn put(*self); }\n\
                      struct H<'a, 'b: 'a> { v: &'a i32[], w: *'b i32 }\n\
                  }\n";
    let tir = clean(source);
    assert!(!tir.roots.is_empty());
    // A trait's and an impl's members are handles into the same arena every
    // other function is in, so nothing is a special case below this pass.
    let members: Vec<TIRItemId> = tir
        .items
        .iter()
        .filter_map(|i| match &i.kind {
            TIRItemKind::Trait { members, .. } | TIRItemKind::Impl { members, .. } => {
                Some(members.clone())
            }
            _ => None,
        })
        .flatten()
        .collect();
    assert_eq!(members.len(), 4);
    for m in members {
        assert!(matches!(tir.items[m].kind, TIRItemKind::Fn(_)));
    }
}

// The type a number named for itself reaches the TIR beside the value, in an
// expression and in a pattern alike. Nothing here asks whether the value fits
// it -- that is the checker's, and `-128_i8` is why: the `-` is an operator,
// and only a tree with both in it can tell that from an overflow.
#[test]
fn a_number_keeps_the_type_it_named() {
    let tir = clean("fn main() {\n    let x = 5_u8;\n    let y = 2.6_f32;\n    match x {\n        1_u8 => a,\n        -3_i8 => b,\n        _ => c,\n    }\n}\n");

    let suffixes: Vec<Option<TIRPrim>> = tir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TIRExprKind::Literal { suffix, .. } => Some(*suffix),
            _ => None,
        })
        .collect();
    assert!(suffixes.contains(&Some(TIRPrim::U8)));
    assert!(suffixes.contains(&Some(TIRPrim::F32)));

    let pats: Vec<(bool, Option<TIRPrim>)> = tir
        .pats
        .iter()
        .filter_map(|p| match &p.kind {
            TIRPatKind::Lit { negated, suffix, .. } => Some((*negated, *suffix)),
            _ => None,
        })
        .collect();
    assert!(pats.contains(&(false, Some(TIRPrim::U8))));
    // The `-` is folded into the value where it can be; the suffix is the
    // number's either way.
    assert!(pats.iter().any(|(_, s)| *s == Some(TIRPrim::I8)));

    // An unsuffixed number carries nothing, and is the same literal it was.
    let tir = clean("fn main() {\n    let x = 5;\n}\n");
    assert!(tir.exprs.iter().any(|e| matches!(
        &e.kind,
        TIRExprKind::Literal { value: TIRLit::Int(5), suffix: None }
    )));
}

// A type alias reaches the TIR as an item of its own. It goes no further: the
// resolver follows it, and what comes after has the type it named.
#[test]
fn a_type_alias_is_an_item_that_names_a_type() {
    let tir = clean("pub type Pair<T> = (T, T)\n");
    assert_eq!(tir.roots.len(), 1);
    match &tir.items[tir.roots[0]].kind {
        TIRItemKind::TypeAlias { vis, name, generics, ty, .. } => {
            assert_eq!(*vis, TIRVis::Pub);
            assert_eq!(name, "Pair");
            assert_eq!(generics.len(), 1);
            assert!(matches!(&tir.types[*ty].kind, TIRTypeKind::Tuple(t) if t.len() == 2));
        }
        other => panic!("{:?}", other),
    }

    // `%deprecated` goes on anything, so it goes on this too.
    let tir = clean("%deprecated(\"use i64\")\ntype Old = i32\n");
    match &tir.items[tir.roots[0]].kind {
        TIRItemKind::TypeAlias { attrs, .. } => {
            assert_eq!(attrs.deprecated.as_deref(), Some("use i64"));
        }
        other => panic!("{:?}", other),
    }
}

// An attribute that is a function's is refused on one, as on any other
// declaration that is not a function.
#[test]
fn a_function_attribute_is_refused_on_a_type_alias() {
    let messages = errors_in("%inline\ntype T = i32\n");
    assert_eq!(messages.len(), 1);
    assert!(messages[0].contains("`%inline` goes on a function"), "{}", messages[0]);
    assert!(messages[0].contains("this is a type alias"), "{}", messages[0]);
}
