// Dominance on the four shapes a graph is made of: a line, a diamond, a loop,
// and a block nothing reaches.

use super::*;
use crate::sir::sir_nodes::*;

// A body that is nothing but its control flow. Dominance is a question about
// edges, so the blocks need hold nothing at all.
fn body(terms: Vec<SIRTerm>) -> SIRBody {
    SIRBody {
        entry:  0,
        blocks: terms
            .into_iter()
            .map(|term| SIRBlock {
                phis:  Vec::new(),
                insts: Vec::new(),
                term,
                line:  1,
                col:   1,
            })
            .collect(),
        values: Vec::new(),
        slots:  Vec::new(),
        params: Vec::new(),
    }
}

fn branch(then: SIRBlockId, els: SIRBlockId) -> SIRTerm {
    SIRTerm::Branch { cond: 0, then, els }
}

//     b0 -> b1 -> b2
#[test]
fn a_line_is_dominated_by_everything_above_it() {
    let b = body(vec![SIRTerm::Goto(1), SIRTerm::Goto(2), SIRTerm::Return(None)]);
    let doms = Dominators::of(&b);

    assert_eq!(doms.idom, vec![None, Some(0), Some(1)]);
    assert!(doms.dominates(0, 2), "the entry stands before the last");
    assert!(!doms.dominates(2, 0), "and the last before nothing");
    assert!(doms.dominates(1, 1), "a block stands before itself");
}

//     b0 -> b1 -\
//       \-> b2 --> b3
#[test]
fn neither_side_of_a_diamond_dominates_the_join() {
    let b = body(vec![branch(1, 2), SIRTerm::Goto(3), SIRTerm::Goto(3), SIRTerm::Return(None)]);
    let doms = Dominators::of(&b);

    assert_eq!(doms.idom, vec![None, Some(0), Some(0), Some(0)]);
    assert!(!doms.dominates(1, 3), "the join is reached without b1");
    assert!(!doms.dominates(2, 3), "and without b2");
}

// Which is what makes the join the frontier of both, and so where a phi goes.
#[test]
fn a_diamond_puts_the_join_on_both_frontiers() {
    let b = body(vec![branch(1, 2), SIRTerm::Goto(3), SIRTerm::Goto(3), SIRTerm::Return(None)]);
    let doms = Dominators::of(&b);
    let f = doms.frontiers(&b);

    assert_eq!(f[1], vec![3]);
    assert_eq!(f[2], vec![3]);
    assert!(f[0].is_empty(), "the entry's reach stops nowhere: {:?}", f[0]);
    assert!(f[3].is_empty(), "and nothing is past the join: {:?}", f[3]);
}

//     b0 -> b1 -> b2 -\
//              \       \-> back to b1
//               \-> b3
#[test]
fn a_loop_head_is_on_its_own_frontier() {
    let b = body(vec![
        SIRTerm::Goto(1),
        branch(2, 3),
        SIRTerm::Goto(1),
        SIRTerm::Return(None),
    ]);
    let doms = Dominators::of(&b);

    assert_eq!(doms.idom, vec![None, Some(0), Some(1), Some(1)]);
    assert!(doms.dominates(1, 2), "every turn goes through the head");

    // The head is reached again without dominating the block that reached it,
    // which is exactly what a phi at the top of a loop is for.
    let f = doms.frontiers(&b);
    assert_eq!(f[2], vec![1]);
    assert_eq!(f[1], vec![1], "the head reaches itself");
}

#[test]
fn a_block_nothing_reaches_has_no_dominator() {
    //  b0 -> b2, and b1 standing on its own.
    let b = body(vec![SIRTerm::Goto(2), SIRTerm::Goto(2), SIRTerm::Return(None)]);
    let doms = Dominators::of(&b);

    assert_eq!(doms.idom[1], None, "b1 is not reached, so nothing stands before it");
    // And its edge into b2 is not a way in, so b2 is nobody's frontier and no
    // phi is placed for a path that is never taken.
    assert_eq!(doms.idom[2], Some(0));
    let f = doms.frontiers(&b);
    assert!(f.iter().all(|held| held.is_empty()), "{:?}", f);
}

// The dominator tree read downwards, which is the order `sir::promote` walks.
#[test]
fn the_children_of_a_diamond_are_all_three_of_its_blocks() {
    let b = body(vec![branch(1, 2), SIRTerm::Goto(3), SIRTerm::Goto(3), SIRTerm::Return(None)]);
    let doms = Dominators::of(&b);
    let mut children = doms.children()[0].clone();
    children.sort();

    assert_eq!(children, vec![1, 2, 3]);
}
