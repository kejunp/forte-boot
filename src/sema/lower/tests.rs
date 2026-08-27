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
mod containers;
mod lives;
mod loops;
mod matches;
mod methods;
mod paths;
mod refs;
mod regions;
mod structs;

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
    let quoted = crate::error::Source::new("t.fc", &text);
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
