// The turns of a loop run several at a time -- when the writes are
// neighbours, when the machine has the instruction, and when it pays.

use super::*;

#[test]
fn a_run_of_writes_to_neighbouring_places_becomes_one_write() {
    let (p, stats) = compiled_at(NEIGHBOURS, crate::sir::opt::Level::More);
    let body = &p.bodies[0];

    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
    assert_eq!(stats.widened, 1, "{:#?}", stats);

    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::VecStore { .. })),
        1,
        "one write where there were four: {:#?}",
        kinds(body)
    );
    assert_eq!(
        count(body, |k| matches!(k, SIRInstKind::Lanes { lanes: 4, .. })),
        2,
        "and one read of each thing read: {:#?}",
        kinds(body)
    );
    // The add is one instruction over four of everything.
    assert_eq!(
        wide(body, |k| matches!(k, SIRInstKind::Binary { .. })),
        vec![4],
        "{:#?}",
        kinds(body)
    );
    // And the elements are not read one at a time any more.
    assert_eq!(count(body, |k| matches!(k, SIRInstKind::Index { .. })), 0, "{:#?}", kinds(body));
}

// It stands at the top level alone: the width is a guess about a machine, and
// a guess is not something to make on a program's behalf unless it was asked
// for.
#[test]
fn nothing_is_widened_below_the_top_level() {
    for level in [
        crate::sir::opt::Level::Less,
        crate::sir::opt::Level::Default,
    ] {
        let (p, stats) = compiled_at(NEIGHBOURS, level);
        assert_eq!(stats.widened, 0, "at {:?}: {:#?}", level, stats);
        assert_eq!(
            count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })),
            0,
            "at {:?}",
            level
        );
    }
}

// And only where the writes can be brought together. A call standing between
// them is what decides it -- and whether it decides it turns entirely on
// whether the call could have reached what is being written, which is the
// question `sir::alias` answers and nothing before it could.
#[test]
fn a_call_between_the_writes_stops_it_only_if_it_could_have_reached_them() {
    let build = |lets_out: bool| {
        let source = format!(
            "struct Range<T> {{ pub lo: T, pub hi: T }}\n\
             %noinline\n\
             fn sink(p: &i32[4]): null {{ null }}\n\
             %noinline\n\
             fn touch(): null {{ null }}\n\
             fn go(a: i32[4]): i32[4] {{\n\
                 var c: i32[4] = [0, 0, 0, 0];\n\
                 {}\n\
                 for i in 0..4 {{ c[i] = a[i]; touch(); }}\n\
                 c\n\
             }}\n",
            if lets_out { "sink(&c);" } else { "" }
        );
        compiled_at(&source, crate::sir::opt::Level::More)
    };

    let (_, shut) = build(false);
    assert_eq!(
        shut.widened, 1,
        "nothing kept the address of `c`, so the calls cannot have written it: {:#?}",
        shut
    );

    let (_, open) = build(true);
    assert_eq!(
        open.widened, 0,
        "the address went out, so what the calls did with it is not known: {:#?}",
        open
    );
}

// One write is never a group, however wide the machine. Two is the floor, and
// it is the floor because one of something at a time is what the program
// already said.
#[test]
fn one_write_on_its_own_is_not_a_group() {
    let (p, stats) = compiled_at(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn one(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..1 { c[i] = a[i]; }\n\
             c\n\
         }\n",
        crate::sir::opt::Level::More,
    );

    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert_eq!(
        count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })),
        0,
        "{:#?}",
        kinds(&p.bodies[0])
    );
}

// And two of them are, on a machine that holds four: the register is a ceiling
// and not a quota.
#[test]
fn two_writes_are_a_group_on_a_machine_that_holds_four() {
    let (p, stats) = compiled_at(
        "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn two(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..2 { c[i] = a[i]; }\n\
             c\n\
         }\n",
        crate::sir::opt::Level::More,
    );

    assert_eq!(stats.widened, 1, "{:#?}", stats);
    assert_eq!(written_wide(&p.bodies[0]), vec![2], "{:#?}", kinds(&p.bodies[0]));
}

// How many go at once is the register over the thing, so the same source over
// the same type comes out in twos on one machine and fours on another.
#[test]
fn a_wider_machine_takes_more_at_a_time() {
    let (narrow, _) = compiled_for(COPY64, crate::sir::opt::Level::More, crate::sir::target::X86_64);
    assert_eq!(
        written_wide(&narrow.bodies[0]),
        vec![2, 2],
        "two eight-byte things in sixteen bytes, so the four are written twice: {:#?}",
        kinds(&narrow.bodies[0])
    );

    let (wide, _) =
        compiled_for(COPY64, crate::sir::opt::Level::More, crate::sir::target::X86_64_V3);
    assert_eq!(
        written_wide(&wide.bodies[0]),
        vec![4],
        "and four of them in thirty-two, so once: {:#?}",
        kinds(&wide.bodies[0])
    );
}

// A register filled halfway is still a register. Four of something on a
// machine that holds eight is written out as four rather than left alone.
#[test]
fn a_group_narrower_than_the_register_is_still_worth_making() {
    let (p, stats) =
        compiled_for(NEIGHBOURS, crate::sir::opt::Level::More, crate::sir::target::X86_64_V4);
    assert_eq!(stats.widened, 1, "{:#?}", stats);
    assert_eq!(
        written_wide(&p.bodies[0]),
        vec![4],
        "sixteen would fit and there are four: {:#?}",
        kinds(&p.bodies[0])
    );
}

// A machine with no vectors is a target like any other, and nothing is widened
// for it however hard the level says to try.
#[test]
fn a_machine_with_no_vectors_leaves_it_all_alone() {
    let (p, stats) =
        compiled_for(NEIGHBOURS, crate::sir::opt::Level::More, crate::sir::target::NONE);
    assert_eq!(stats.widened, 0, "{:#?}", stats);
    assert_eq!(count(&p.bodies[0], |k| matches!(k, SIRInstKind::VecStore { .. })), 0);
    // And the rest of the level still happened.
    assert_eq!(stats.unrolled, 1, "{:#?}", stats);
}

// What the machine has not got is not done to several at once, whatever the
// shape of the loop. An integer divide is the one everybody expects to be
// there: four of them line up as neatly as four adds, and there is no machine
// here that can do them together.
#[test]
fn what_the_machine_cannot_do_is_left_one_at_a_time() {
    let divided = |ty: &str, by: &str| {
        format!(
            "struct Range<T> {{ pub lo: T, pub hi: T }}\n\
             fn half(a: {0}[4]): {0}[4] {{\n\
                 var c: {0}[4] = [{1}, {1}, {1}, {1}];\n\
                 for i in 0..4 {{ c[i] = a[i] / {2}; }}\n\
                 c\n\
             }}\n",
            ty,
            if ty == "f32" { "0.0" } else { "0" },
            by
        )
    };

    let (_, whole) = compiled_at(&divided("i32", "2"), crate::sir::opt::Level::More);
    assert_eq!(whole.widened, 0, "there is no integer divide over a vector: {:#?}", whole);

    let (p, real) = compiled_at(&divided("f32", "2.0"), crate::sir::opt::Level::More);
    assert_eq!(real.widened, 1, "and there is a float one: {:#?}", real);
    assert_eq!(written_wide(&p.bodies[0]), vec![4]);
}

// ---- Whether it is worth it -------------------------------------------------

// Values that have to be fetched one at a time cost an insert each, which is
// most of what a group of them would have saved. The same loop with the values
// already lined up is worth making, and it is the only difference between the
// two.
#[test]
fn a_group_that_must_be_gathered_is_not_worth_making() {
    let gathered = "struct Range<T> { pub lo: T, pub hi: T }\n\
         %noinline\n\
         fn make(n: i32): i32 { n }\n\
         fn go(): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..4 { c[i] = make(i); }\n\
             c\n\
         }\n";
    let (_, stats) = compiled_at(gathered, crate::sir::opt::Level::More);
    assert_eq!(
        stats.widened, 0,
        "four inserts to save four stores is not a saving: {:#?}",
        stats
    );

    let lined_up = "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn go(a: i32[4]): i32[4] {\n\
             var c: i32[4] = [0, 0, 0, 0];\n\
             for i in 0..4 { c[i] = a[i]; }\n\
             c\n\
         }\n";
    let (_, stats) = compiled_at(lined_up, crate::sir::opt::Level::More);
    assert_eq!(stats.widened, 1, "one read and one write is: {:#?}", stats);
}

// And a machine where an insert costs more is a machine where fewer groups are
// worth making, which is what a cost model is for.
#[test]
fn what_an_insert_costs_changes_what_is_worth_making() {
    // Two values that cannot be lined up, written to neighbouring places.
    let source = "struct Range<T> { pub lo: T, pub hi: T }\n\
         fn go(a: i64[4], b: i64[4]): i64[4] {\n\
             var c: i64[4] = [0, 0, 0, 0];\n\
             c[0] = a[1];\n\
             c[1] = b[0];\n\
             c\n\
         }\n";
    let cheap = crate::sir::target::Target { insert: 1, ..crate::sir::target::X86_64 };
    let dear = crate::sir::target::Target { insert: 4, ..crate::sir::target::X86_64 };

    let (_, held) = compiled_for(source, crate::sir::opt::Level::More, dear);
    assert_eq!(held.widened, 0, "four an insert is more than the stores cost: {:#?}", held);

    // The same program, the same everything, and one number different.
    let (_, held) = compiled_for(source, crate::sir::opt::Level::More, cheap);
    assert!(held.widened <= 1, "{:#?}", held);
}

// ---- How hard to try --------------------------------------------------------

// A program with something for every kind of rewrite in it, run at each level,
// so that what each one turns on is written down as a test rather than as a
