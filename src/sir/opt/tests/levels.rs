// What each of the four levels turns on, written down as a test rather than
// as a comment.

use super::*;

// Nothing at all, which is what `-O0` is for: what comes out is what the
// lowering and the promotion made of the source.
#[test]
fn the_bottom_level_changes_nothing() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::None);

    assert_eq!(stats, crate::sir::opt::Stats::default(), "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(!loops(body).is_empty(), "the loop is still a loop");
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Call { .. })) > 0,
        "and the call is still a call: {:#?}",
        kinds(body)
    );
}

// The first level takes things away and moves nothing.
#[test]
fn the_first_level_removes_and_does_not_move() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::Less);

    assert_eq!(stats.inlined, 0, "{:#?}", stats);
    assert_eq!(stats.unrolled, 0, "{:#?}", stats);
    assert_eq!(stats.hoisted, 0, "{:#?}", stats);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert!(stats.dead > 0 || stats.folded > 0 || stats.shared > 0, "{:#?}", stats);
    assert!(!loops(p.bodies.last().expect("a body")).is_empty(), "the loop stands");
}

// The second moves code as well, which is where a program may come out bigger
// than it went in.
#[test]
fn the_second_level_writes_calls_and_loops_out() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::Default);

    assert!(stats.inlined > 0, "{:#?}", stats);
    assert!(stats.unrolled > 0, "{:#?}", stats);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    assert!(loops(body).is_empty(), "the loop is written out: {:#?}", body.blocks);
    // `twice(3) + 0` is 6, worked out here and not there.
    assert!(
        count(body, |k| matches!(k, SIRInstKind::Literal(TIRLit::Int(6)))) > 0,
        "{:#?}",
        kinds(body)
    );
}

// And the third widens what the second left in a straight line.
#[test]
fn the_third_level_runs_the_turns_together() {
    let (p, stats) = compiled_at(EVERYTHING, crate::sir::opt::Level::More);

    assert!(stats.inlined > 0, "{:#?}", stats);
    assert!(stats.unrolled > 0, "{:#?}", stats);
    assert_eq!(stats.widened, 1, "{:#?}", stats);
    let body = p.bodies.last().expect("a body");
    // The literal that does not vary with the turn is in every lane of one
    // value rather than in four instructions.
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Pack(_))),
        1,
        "{:#?}",
        kinds(body)
    );
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::VecStore { .. })), 1);
}

// The levels are ordered, which is what lets a rewrite ask `>= Default`
// instead of naming every level it runs at.
#[test]
fn the_levels_are_ordered_and_numbered() {
    use crate::sir::opt::Level;
    assert!(Level::None < Level::Less);
    assert!(Level::Less < Level::Default);
    assert!(Level::Default < Level::More);
    assert_eq!(Level::of(0), Level::None);
    assert_eq!(Level::of(2), Level::Default);
    assert_eq!(Level::of(3), Level::More);
    // A number nobody wrote a level for is the most there is.
    assert_eq!(Level::of(9), Level::More);
    assert_eq!(Level::default(), Level::Default);
}
