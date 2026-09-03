// What the checker makes of a source. Unlike every other test under `sema`,
// these start from text: the whole pipeline runs, so what is asserted on is
// what a reader would have got.
//
// One file per part of the pass below, named for the file it tests. What
// stays here is the one thing every one of them wants: a source string run
// through every pass up to and including this one.

use super::*;
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::parse::parser::Parser;
use crate::prep::preprocess;
use crate::tir::lower::Lowerer as TIRLowerer;
// Named rather than reached through `super::*`: the pass itself imports only
// what it uses, and what these assert on is a good deal more than that.
use crate::tir::tir_nodes::{TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::*;

mod basics;
mod bounds;
mod closures;
mod consts;
mod containers;
mod lives;
mod loops;
mod matches;
mod methods;
mod paths;
mod refs;
mod regions;
mod structs;
mod suites;

// Source to typed tree. The passes before this one must all succeed: what this
// makes of a tree they turned down is not what is under test.
fn typed(source: &str) -> (TTIRProgram, Vec<String>) {
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
    let mut l = TIRLowerer::new(&p);
    l.lower(&root);
    assert!(l.errors().is_empty(), "{}\n{:#?}", source, l.errors());
    let tir = l.finish();

    let (ttir, errors) = Lowerer::new(&tir).lower(vec!["t".to_string()]);
    let text: Vec<char> = source.chars().collect();
    let quoted = crate::error::Source::new("t.ft", &text);
    let said = errors.iter().map(|e| e.render(&quoted)).collect();
    (ttir, said)
}

fn clean(source: &str) -> TTIRProgram {
    let (ttir, said) = typed(source);
    assert!(said.is_empty(), "{}\n{:#?}", source, said);
    ttir
}

fn refused(source: &str) -> String {
    typed(source).1.join("\n")
}

// Several files at once, each with its module path and what its imports bound.
// The same road `main::compile` takes for a real build, minus the resolver:
// what a path on disk names is `sema::imports`' question and is tested there,
// and what is under test here is what happens once it is answered.
fn suite(files: &[(&str, &str)], bound: &[Vec<Bound>]) -> (TTIRProgram, Vec<String>) {
    let mut tirs = Vec::new();
    for (_, source) in files {
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
        let mut l = TIRLowerer::new(&p);
        l.lower(&root);
        assert!(l.errors().is_empty(), "{}\n{:#?}", source, l.errors());
        tirs.push(l.finish());
    }
    let paths: Vec<Vec<String>> =
        files.iter().map(|(name, _)| vec![name.to_string()]).collect();
    let held: Vec<&crate::tir::tir_nodes::TIRProgram> = tirs.iter().collect();
    let (ttir, errors) = Lowerer::across(held, paths).lower_suite(bound);

    // Each quoted against its own text, which is the whole of why a diagnostic
    // carries a file at all.
    let texts: Vec<Vec<char>> = files.iter().map(|(_, s)| s.chars().collect()).collect();
    let names: Vec<String> = files.iter().map(|(n, _)| format!("{}.ft", n)).collect();
    let quoted: Vec<crate::error::Source> = names
        .iter()
        .zip(texts.iter())
        .map(|(name, text)| crate::error::Source::new(name, text))
        .collect();
    let said = errors
        .iter()
        .zip(errors.whose().iter())
        .map(|(e, &whose)| e.render(&quoted[whose]))
        .collect();
    (ttir, said)
}

fn bound(name: &str, file: usize, path: &[&str]) -> Bound {
    Bound {
        name: name.to_string(),
        file,
        path: path.iter().map(|p| p.to_string()).collect(),
    }
}

// Everything a file declares becomes an item, and every one of them a symbol.

// The fn a name belongs to, and the region every reference in its signature
// stands in, parameters first and the return last.
fn signature(ttir: &TTIRProgram, name: &str) -> (Vec<usize>, Vec<usize>, Vec<(usize, usize)>) {
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == name => Some(f),
        _ => None,
    }).expect("the fn");
    let lives = |ty: usize| match &ttir.types[ty] {
        Ty::Ref { life, .. } => vec![*life],
        _ => Vec::new(),
    };
    let Ty::Fn { params, ret, .. } = &ttir.types[f.ty] else { panic!("a fn type") };
    let brought = params.iter().flat_map(|&p| lives(p)).collect();
    (brought, lives(*ret), f.outlives.clone())
}
