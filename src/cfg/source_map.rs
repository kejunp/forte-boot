// Where a simplified tree came from. `opt` rewrites nodes in place and stops
// pointing at others, and both of those lose something a message would want:
// a folded constant no longer holds the `+` it replaced, and an eliminated
// branch is no longer anywhere the roots can reach.
//
// This is kept beside the tree rather than in it. `CFGProgram` stays what it
// is -- a tree and nothing else -- and a reader with no interest in where a
// node came from does not have to carry the answer.
//
// Nothing consumes this yet. `dropped` is what an "unreachable code" warning
// would point at, and what a pass wanting to check code the simplifier removed
// would start from; `origin` is what a message about a folded constant would
// name it by. Both are written for the pass that comes after, so the allow
// stays until one is reading them.
#![allow(dead_code)]

use std::collections::HashMap;

use super::cfg_nodes::{CFGBlockId, CFGBodyId, CFGExprId};

// What a rewrite did to the node it was written on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rewrite {
    // Operands the pass could work out for itself.
    Folded,
    // `&&` or `||` settled by the side that was already a literal.
    ShortCircuited,
    // The branch a literal condition picked.
    BranchTaken,
    // A `while` whose condition was never true.
    LoopNeverRan,
    // A block that bound nothing, replaced by its value.
    Collapsed,
}

// Why a subtree is no longer pointed at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    BranchNotTaken,
    LoopBodyNeverRan,
    // Everything after a statement that leaves the block.
    AfterDiverging,
    // The side of `&&` or `||` that is never evaluated.
    ShortCircuited,
}

// Where a node was written, and what stood there, before a rewrite moved it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin {
    pub line: usize,
    pub col:  usize,
    // What was there, in the words a message would use: "a binary `+`".
    pub was:  &'static str,
    pub why:  Rewrite,
}

// A block nothing reaches any more, kept with where it was written. A block and
// not a subtree: control flow is edges here, and what a rewrite stops pointing
// at is a block of the graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dropped {
    pub body:  CFGBodyId,
    pub block: CFGBlockId,
    pub line:  usize,
    pub col:   usize,
    pub why:   Reason,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct CFGSourceMap {
    pub rounds: usize,
    rewritten:  HashMap<CFGExprId, Origin>,
    blocks:     HashMap<(CFGBodyId, CFGBlockId), Origin>,
    dropped:    Vec<Dropped>,
}

impl CFGSourceMap {
    pub fn new() -> CFGSourceMap {
        CFGSourceMap::default()
    }

    // Notes what stood at `id` before this rewrite. The *first* answer is the
    // one kept: a handle may be rewritten several times over -- `if 1 < 2 { 3 }`
    // folds, then takes its branch, then collapses, all on the one node -- and
    // the position worth having is the one the source was written at, which is
    // the first. Every rewrite after that overwrites the node's own line and
    // col, so this is the only place it survives.
    pub fn record(&mut self, id: CFGExprId, line: usize, col: usize, was: &'static str,
                  why: Rewrite) {
        self.rewritten.entry(id).or_insert(Origin { line, col, was, why });
    }

    pub fn drop_block(&mut self, body: CFGBodyId, block: CFGBlockId, line: usize, col: usize,
                      why: Reason) {
        if self.dropped.iter().any(|d| d.body == body && d.block == block) {
            return;
        }
        self.dropped.push(Dropped { body, block, line, col, why });
    }

    // A block whose edges were redirected. Keyed by the pair, since a block is
    // numbered within its body and not across the program.
    pub fn record_block(&mut self, body: CFGBodyId, block: CFGBlockId, line: usize, col: usize,
                        was: &'static str, why: Rewrite) {
        self.blocks.entry((body, block)).or_insert(Origin { line, col, was, why });
    }

    // Where the node at `id` was written, if a rewrite moved it.
    pub fn origin(&self, id: CFGExprId) -> Option<&Origin> {
        self.rewritten.get(&id)
    }

    pub fn dropped(&self) -> &[Dropped] {
        &self.dropped
    }

    pub fn block_origin(&self, body: CFGBodyId, block: CFGBlockId) -> Option<&Origin> {
        self.blocks.get(&(body, block))
    }

    pub fn rewrites(&self) -> usize {
        self.rewritten.len() + self.blocks.len()
    }
}
