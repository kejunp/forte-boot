// What a release does, checked against declarations that say what should
// happen to them.
//
// These go through `fixture::lowered` like the rest of the lowering's tests,
// so every glue body below is held to `verify` and `verify_order` before
// anything is asserted about it. That matters more here than elsewhere: a glue
// body is *written* rather than lowered -- its blocks and its phis and its
// terminators are put there by hand -- and a body built by hand is exactly the
// kind that walks and is wrong.
//
// Every source declares its own `Drop`. The compiler finds the trait by name
// and there is no prelude, so a suite that wants one has to write one.

use super::super::super::fixture::*;
use super::super::super::mir_nodes::*;

// The declarations every case here needs: a `Drop` to name, and a type that
// has one.
const HELD: &str = "trait Drop {\n    fn drop(self)\n}\n\
                    struct Handle {\n    pub n: i32,\n}\n\
                    impl Drop for Handle {\n    fn drop(self) {\n    }\n}\n";

fn built(rest: &str) -> MIRProgram {
    lowered(&format!("{}{}", HELD, rest))
}

fn glue<'a>(p: &'a MIRProgram, name: &str) -> &'a MIRBody {
    p.bodies
        .iter()
        .find(|body| body.symbol == name)
        .unwrap_or_else(|| {
            panic!(
                "no routine called {}: there is {:#?}",
                name,
                p.bodies.iter().map(|b| &b.symbol).collect::<Vec<_>>()
            )
        })
}

fn calls(body: &MIRBody) -> Vec<String> {
    body.blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .filter_map(|inst| match &inst.kind {
            MIRInstKind::Call { to: MIRCallee::Symbol(held), .. } => Some(held.clone()),
            _ => None,
        })
        .collect()
}

// ---- Every call has something to call --------------------------------------

// The property the whole file exists for. A `__D` in a body that names nothing
// is a link error, and it is the kind that turns up long after the compiler
// said it was happy.
#[test]
fn every_release_a_program_calls_has_a_body() {
    let p = built(
        "struct Pair {\n    pub a: Handle,\n    pub b: i32,\n}\n\
         fn f() {\n    let h = Handle { n: 1 }\n    let p = Pair { a: Handle { n: 2 }, b: 3 }\n}\n",
    );
    let mut wanted: Vec<String> = p
        .bodies
        .iter()
        .flat_map(calls)
        .filter(|held| held.starts_with("__D"))
        .collect();
    wanted.sort();
    wanted.dedup();
    assert!(!wanted.is_empty(), "nothing asked for a release at all");
    for name in wanted {
        glue(&p, &name);
    }
}

// ---- What one is made of ---------------------------------------------------

#[test]
fn a_type_with_a_drop_impl_calls_the_one_that_was_written() {
    let p = built("fn f() {\n    let h = Handle { n: 1 }\n}\n");
    let held = glue(&p, "__D9t::Handle");
    assert!(
        calls(held).iter().any(|name| name.contains("Drop4drop")),
        "{:?}",
        calls(held)
    );
}

// A struct's routine releases the fields that have something to release and
// leaves the rest alone. A routine that called one per field would be a call
// per number in the program.
#[test]
fn a_structure_releases_the_fields_that_have_something_to_release() {
    let p = built(
        "struct Pair {\n    pub a: Handle,\n    pub b: i32,\n}\n\
         fn f() {\n    let p = Pair { a: Handle { n: 1 }, b: 2 }\n}\n",
    );
    let held = glue(&p, "__D7t::Pair");
    assert_eq!(calls(held), vec!["__D9t::Handle".to_string()]);
}

#[test]
fn a_structure_of_numbers_has_no_release_at_all() {
    let p = built("struct Plain {\n    pub a: i32,\n}\nfn f() {\n    let p = Plain { a: 1 }\n}\n");
    assert!(
        !p.bodies.iter().any(|body| body.symbol == "__D8t::Plain"),
        "nothing about it has to be released, so nothing asked"
    );
}

// The release of a field is at the offset the layout worked out, not at the
// field's number: a `Handle` after an `i32` is four bytes along.
#[test]
fn a_field_is_released_at_the_offset_it_sits_at() {
    let p = built(
        "struct Pair {\n    pub b: i32,\n    pub a: Handle,\n}\n\
         fn f() {\n    let p = Pair { b: 1, a: Handle { n: 2 } }\n}\n",
    );
    let held = glue(&p, "__D7t::Pair");
    let offsets: Vec<i64> = held
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .filter_map(|inst| match inst.kind {
            MIRInstKind::Offset { bytes, .. } => Some(bytes),
            _ => None,
        })
        .collect();
    assert_eq!(offsets, vec![4], "the handle is behind the number");
}

// ---- The order -------------------------------------------------------------

// The user's `drop` is handed the whole value and may read any of it, so it
// runs before any part of it has gone.
#[test]
fn the_written_drop_runs_before_the_fields_are_released() {
    let p = built(
        "struct Both {\n    pub a: Handle,\n}\n\
         impl Drop for Both {\n    fn drop(self) {\n    }\n}\n\
         fn f() {\n    let b = Both { a: Handle { n: 1 } }\n}\n",
    );
    let held = calls(glue(&p, "__D7t::Both"));
    let own = held.iter().position(|n| n.contains("Both4Drop4drop")).expect("its own");
    let field = held.iter().position(|n| n == "__D9t::Handle").expect("its field");
    assert!(own < field, "{:?}", held);
}

// And it does not release its own receiver, which would be this routine again.
// `gir::drops` is where that is decided; this is the shape it has to leave.
#[test]
fn a_written_drop_does_not_call_the_release_it_is() {
    let p = built("fn f() {\n    let h = Handle { n: 1 }\n}\n");
    let own = p
        .bodies
        .iter()
        .find(|body| body.symbol.contains("Handle4Drop4drop"))
        .expect("the written drop");
    assert!(
        !calls(own).iter().any(|name| name.starts_with("__D")),
        "it releases itself, so it never returns: {:?}",
        calls(own)
    );
}

// ---- An enum ---------------------------------------------------------------

// Which variant is in there is not a fact about the type, so the routine reads
// the tag and branches rather than releasing every payload it can think of.
#[test]
fn an_enum_reads_its_tag_and_releases_only_the_variant_that_matched() {
    let p = built(
        "enum Held {\n    Empty,\n    One(Handle),\n}\n\
         fn f() {\n    let h = Held::One(Handle { n: 1 })\n}\n",
    );
    let held = glue(&p, "__D7t::Held");
    assert!(
        held.blocks.iter().flat_map(|b| b.insts.iter()).any(|inst| matches!(
            inst.kind,
            MIRInstKind::Load { .. }
        )),
        "the tag is not read"
    );
    assert!(
        held.blocks.iter().any(|b| matches!(b.term, MIRTerm::Branch { .. })),
        "nothing branches on it"
    );
    assert_eq!(calls(held), vec!["__D9t::Handle".to_string()], "once, for the one variant");
}

// A variant with nothing in it is not a branch: the comparison would be
// written, taken, and lead to a block that does nothing.
#[test]
fn a_variant_with_nothing_to_release_gets_no_branch_of_its_own() {
    let p = built(
        "enum Held {\n    Empty,\n    One(Handle),\n    Two(i32),\n}\n\
         fn f() {\n    let h = Held::One(Handle { n: 1 })\n}\n",
    );
    let held = glue(&p, "__D7t::Held");
    let branches =
        held.blocks.iter().filter(|b| matches!(b.term, MIRTerm::Branch { .. })).count();
    assert_eq!(branches, 1, "only `One` holds anything");
}

// ---- An array --------------------------------------------------------------

// A loop and not an unrolling, or `T[10000]` would be ten thousand calls in a
// row.
#[test]
fn an_array_is_released_by_a_loop_over_its_elements() {
    let p = built(
        "struct Many {\n    pub xs: Handle[3],\n}\n\
         fn f(a: Handle, b: Handle, c: Handle) {\n    let m = Many { xs: [a, b, c] }\n}\n",
    );
    let held = glue(&p, "__D12t::Handle[3]");
    assert_eq!(calls(held), vec!["__D9t::Handle".to_string()], "one call, not three");
    assert!(
        held.blocks.iter().any(|b| matches!(b.term, MIRTerm::Branch { .. })),
        "a loop wants a test"
    );
    assert!(
        held.blocks.iter().flat_map(|b| b.insts.iter()).any(|inst| matches!(
            inst.kind,
            MIRInstKind::Scaled { .. }
        )),
        "nothing steps through the elements"
    );
}

// The counter is a slot, which is what lets the loop be written without a phi
// in a body nothing checked the phis of by eye.
#[test]
fn the_loop_counts_in_a_slot_rather_than_a_phi() {
    let p = built(
        "struct Many {\n    pub xs: Handle[2],\n}\n\
         fn f(a: Handle, b: Handle) {\n    let m = Many { xs: [a, b] }\n}\n",
    );
    let held = glue(&p, "__D12t::Handle[2]");
    assert!(held.blocks.iter().all(|b| b.phis.is_empty()), "a phi was written by hand");
    assert_eq!(held.frame.len(), 1, "the counter is the only thing in the frame");
}

// ---- Reaching further ------------------------------------------------------

// A routine is written by emitting calls to other routines, so the ones it
// asks for have to be written too -- however deep that goes.
#[test]
fn a_release_that_asks_for_another_gets_it() {
    let p = built(
        "struct Inner {\n    pub h: Handle,\n}\n\
         struct Outer {\n    pub i: Inner,\n}\n\
         fn f() {\n    let o = Outer { i: Inner { h: Handle { n: 1 } } }\n}\n",
    );
    for name in ["__D8t::Outer", "__D8t::Inner", "__D9t::Handle"] {
        glue(&p, name);
    }
}

// One routine per type however many times it is asked for, or a linker would
// be handed the same name twice.
#[test]
fn a_type_gets_one_routine_however_often_it_is_released() {
    let p = built(
        "fn f() {\n    let a = Handle { n: 1 }\n}\n\
         fn g() {\n    let b = Handle { n: 2 }\n}\n",
    );
    let held = p.bodies.iter().filter(|body| body.symbol == "__D9t::Handle").count();
    assert_eq!(held, 1);
}

// ---- The shape of one ------------------------------------------------------

// One address in, nothing out -- which is what `Lowerer::release` has always
// emitted at the call.
#[test]
fn a_release_takes_one_address_and_answers_with_nothing() {
    let p = built("fn f() {\n    let h = Handle { n: 1 }\n}\n");
    let held = glue(&p, "__D9t::Handle");
    assert_eq!(held.params.len(), 1);
    assert!(
        held.blocks
            .iter()
            .all(|b| !matches!(b.term, MIRTerm::Return(Some(_)))),
        "a release answers with nothing"
    );
}
