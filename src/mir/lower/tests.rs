// What a program comes to once a type is a number.
//
// Every one of these goes through `fixture::lowered`, which lowers and then
// holds every body to `verify` and `verify_order`. So a test below that looks
// at one instruction still says the whole body is well formed -- which matters
// more here than in most places, because this is the pass where a wrong number
// is not a wrong shape: a field read four bytes into a structure whose second
// field begins at eight reads half of one thing and half of another, and every
// pass after it is happy.
//
// The tests are written as the numbers themselves for that reason. "It lowers"
// is not the property; "the offset is eight" is.

use super::super::fixture::*;
use super::*;

fn held(p: &MIRProgram, name: &str) -> Vec<MIRInstKind> {
    kinds(body_of(p, name))
}

fn has(p: &MIRProgram, name: &str, want: impl Fn(&MIRInstKind) -> bool) -> bool {
    held(p, name).iter().any(want)
}

// ---- The straight cases ----------------------------------------------------

#[test]
fn a_body_is_named_by_the_symbol_it_compiles_to() {
    let p = lowered("fn f(): i32 { 1 }\n");
    assert!(p.bodies.iter().all(|body| body.symbol.starts_with("__F")), "{:#?}",
        p.bodies.iter().map(|b| &b.symbol).collect::<Vec<_>>());
}

// Over parameters and not over literals: `gir::opt` folds `1 + 2` before this
// pass ever sees it, so an addition that survives to here is one whose operands
// were not both known.
#[test]
fn an_addition_is_one_instruction() {
    let p = lowered("fn f(a: i32, b: i32): i32 { a + b }\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::Add, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// The one thing a lowering has to decide about an operator: the source has one
// `/` and the machine has two, and the operands' type says which.
#[test]
fn a_signed_division_and_an_unsigned_one_are_two_instructions() {
    let signed = lowered("fn f(a: i32, b: i32): i32 { a / b }\n");
    let unsigned = lowered("fn f(a: u32, b: u32): u32 { a / b }\n");
    assert!(
        has(&signed, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::SDiv, .. })),
        "{:#?}",
        held(&signed, "1f")
    );
    assert!(
        has(&unsigned, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::UDiv, .. })),
        "{:#?}",
        held(&unsigned, "1f")
    );
}

// And the same for an ordering, which is the other place signedness is not a
// detail: -1 is less than 1 and is greater than it read the other way.
#[test]
fn a_signed_ordering_and_an_unsigned_one_are_two_instructions() {
    let signed = lowered("fn f(a: i32, b: i32): bool { a < b }\n");
    let unsigned = lowered("fn f(a: u32, b: u32): bool { a < b }\n");
    assert!(has(&signed, "1f", |k| matches!(k, MIRInstKind::Cmp { op: MIRCmpOp::SLt, .. })));
    assert!(has(&unsigned, "1f", |k| matches!(k, MIRInstKind::Cmp { op: MIRCmpOp::ULt, .. })));
}

// Equality is one instruction however the operands are signed: the bits are the
// bits. That it is *not* doubled is as much of the rule as that the orderings
// are.
#[test]
fn equality_is_one_instruction_for_both() {
    let signed = lowered("fn f(a: i32, b: i32): bool { a == b }\n");
    let unsigned = lowered("fn f(a: u32, b: u32): bool { a == b }\n");
    assert!(has(&signed, "1f", |k| matches!(k, MIRInstKind::Cmp { op: MIRCmpOp::Eq, .. })));
    assert!(has(&unsigned, "1f", |k| matches!(k, MIRInstKind::Cmp { op: MIRCmpOp::Eq, .. })));
}

#[test]
fn a_float_gets_the_floating_instructions() {
    let p = lowered("fn f(a: f64, b: f64): f64 { a + b }\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::FAdd, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// A shift brings in noughts or brings in the sign, and which is wanted is the
// operand's signedness rather than the shift's.
#[test]
fn shifting_right_follows_the_operands_signedness() {
    let signed = lowered("fn f(a: i32, b: i32): i32 { a >> b }\n");
    let unsigned = lowered("fn f(a: u32, b: u32): u32 { a >> b }\n");
    assert!(has(&signed, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::AShr, .. })));
    assert!(has(&unsigned, "1f", |k| matches!(k, MIRInstKind::Bin { op: MIRBinOp::LShr, .. })));
}

// ---- Literals --------------------------------------------------------------

#[test]
fn a_boolean_is_a_nought_or_a_one() {
    let p = lowered("fn f(): bool { true }\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Const(MIRConst::Int(1)))),
        "{:#?}",
        held(&p, "1f")
    );
}

// The one literal that does not fit in an instruction. The bytes go in the
// pool, and what stands where the literal was is a pair saying where they are
// and how many there are.
#[test]
fn a_string_goes_in_the_pool_and_leaves_a_symbol_behind() {
    let p = lowered("fn f(): str { \"hi\" }\n");
    assert_eq!(p.pool.len(), 1, "{:#?}", p.pool);
    assert_eq!(p.pool[0].bytes, b"hi".to_vec());
    let name = p.pool[0].symbol.clone();
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Symbol(held) if *held == name)),
        "{:#?}",
        held(&p, "1f")
    );
}

// One entry for two literals that say the same thing: the bytes of "hi" are the
// bytes of "hi", and two copies would be two copies in the object file.
#[test]
fn one_string_written_twice_is_one_entry() {
    let p = lowered("fn f(): str { \"hi\" }\nfn g(): str { \"hi\" }\n");
    assert_eq!(p.pool.len(), 1, "{:#?}", p.pool);
}

// ---- Reaching into things --------------------------------------------------

// The whole reason `mir::layout` exists: the field's *number* is gone and what
// is left is how many bytes along it is. A byte then a word puts the word at
// eight, not at one.
#[test]
fn a_field_becomes_the_offset_the_layout_worked_out() {
    let p = lowered(
        "struct Pair { a: i8, b: i64 }\n\
         fn f(p: Pair): i64 { p.b }\n",
    );
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Offset { bytes: 8, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

#[test]
fn the_first_field_is_at_the_beginning() {
    let p = lowered(
        "struct Pair { a: i8, b: i64 }\n\
         fn f(p: Pair): i8 { p.a }\n",
    );
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Offset { bytes: 0, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// An index is not known until it runs, so it is a scale rather than an offset
// -- and the scale is the element's stride, which is what keeps element two
// from starting in the middle of element one.
#[test]
fn an_index_becomes_a_scale_of_the_elements_stride() {
    let p = lowered("fn f(xs: i32[4], i: i32): i32 { xs[i] }\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Scaled { scale: 4, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

#[test]
fn a_wider_element_is_a_wider_scale() {
    let p = lowered("fn f(xs: i64[4], i: i32): i64 { xs[i] }\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Scaled { scale: 8, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// A load says how many bytes it is reading, because there is no type left to
// ask. Reading an `i8` reads one byte and not eight.
#[test]
fn a_load_carries_the_width_it_reads() {
    let p = lowered(
        "struct Pair { a: i8, b: i64 }\n\
         fn f(p: Pair): i8 { p.a }\n",
    );
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Load { bytes: 1, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// ---- Building things -------------------------------------------------------

// A structure is not a thing a register holds, so it is room in the frame and
// a store per field.
#[test]
fn a_struct_literal_is_room_and_a_store_for_each_field() {
    let p = lowered(
        "struct Pair { a: i32, b: i32 }\n\
         fn f(): Pair { Pair { a: 1, b: 2 } }\n",
    );
    let body = body_of(&p, "1f");
    assert!(!body.frame.is_empty(), "it needs room");
    assert!(
        count(body, |k| matches!(k, MIRInstKind::Store { .. })) >= 2,
        "{:#?}",
        kinds(body)
    );
}

// An enum is a tag and then the payload, and the number in the tag is the one
// the checker gave the variant rather than one invented here.
#[test]
fn a_variant_writes_the_number_the_checker_gave_it() {
    let p = lowered(
        "enum Colour { Red, Green, Blue }\n\
         fn f(): Colour { Colour::Green }\n",
    );
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Const(MIRConst::Int(1)))),
        "{:#?}",
        held(&p, "1f")
    );
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Store { bytes: 1, .. })),
        "three variants fit in a byte: {:#?}",
        held(&p, "1f")
    );
}

// ---- Calls -----------------------------------------------------------------

#[test]
fn a_call_to_a_declaration_names_its_symbol() {
    let p = lowered("fn g(): i32 { 1 }\nfn f(): i32 { g() }\n");
    assert!(
        has(&p, "1f", |k| matches!(
            k,
            MIRInstKind::Call { to: MIRCallee::Symbol(name), .. } if name.contains("1g")
        )),
        "{:#?}",
        held(&p, "1f")
    );
}

// A generic reaches the instance and not the declaration, which is what `mono`
// worked the name out for.
#[test]
fn a_call_to_a_generic_names_the_instance() {
    let p = lowered("fn id<T>(x: T): T { x }\nfn f(): i32 { id(1) }\n");
    let called: Vec<String> = held(&p, "1f")
        .iter()
        .filter_map(|k| match k {
            MIRInstKind::Call { to: MIRCallee::Symbol(name), .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert!(!called.is_empty(), "{:#?}", held(&p, "1f"));
    assert!(
        called.iter().all(|name| p.bodies.iter().any(|b| b.symbol == *name)),
        "a call to a body that is not there: {:#?} against {:#?}",
        called,
        p.bodies.iter().map(|b| &b.symbol).collect::<Vec<_>>()
    );
}

// ---- The graph -------------------------------------------------------------

// The blocks and the edges are the SIR's, unchanged. What changes is what is
// written in them.
#[test]
fn a_branch_is_still_a_branch() {
    let p = lowered("fn f(a: i32): i32 { if a > 0 { 1 } else { 2 } }\n");
    let body = body_of(&p, "1f");
    assert!(
        body.blocks.iter().any(|b| matches!(b.term, MIRTerm::Branch { .. })),
        "{:#?}",
        body.blocks.iter().map(|b| &b.term).collect::<Vec<_>>()
    );
}

// A phi at the top of a loop reads a value made at the bottom of it, so the
// register it names has to exist before the block that makes it is walked --
// which is why every register is made up front.
#[test]
fn a_loop_keeps_its_phis_and_they_name_registers_that_exist() {
    let p = lowered(
        "fn f(n: i32): i32 {\n\
         \x20   var t = 0\n\
         \x20   var i = 0\n\
         \x20   while i < n { t = t + i\n i = i + 1 }\n\
         \x20   t\n\
         }\n",
    );
    let body = body_of(&p, "1f");
    for block in &body.blocks {
        for phi in &block.phis {
            for (_, reg) in &phi.edges {
                assert!(*reg < body.regs.len(), "a phi names %{} and there are {}", reg, body.regs.len());
            }
        }
    }
}

#[test]
fn a_return_carries_what_it_returns() {
    let p = lowered("fn f(): i32 { 1 }\n");
    let body = body_of(&p, "1f");
    assert!(
        body.blocks.iter().any(|b| matches!(b.term, MIRTerm::Return(Some(_)))),
        "{:#?}",
        body.blocks.iter().map(|b| &b.term).collect::<Vec<_>>()
    );
}

// ---- What every body has to be ---------------------------------------------

// The parameters are filled by the caller and made by no instruction, which is
// the one register with no def site -- and `verify` has to have been told.
#[test]
fn the_parameters_are_registers_of_the_body() {
    let p = lowered("fn f(a: i32, b: i32): i32 { a + b }\n");
    let body = body_of(&p, "1f");
    assert_eq!(body.params.len(), 2);
    assert!(body.params.iter().all(|&reg| reg < body.regs.len()));
}

// Nothing here knows how many registers a machine has -- that is
// `mir::regalloc`'s -- so a body leaves this pass wanting as many as it wants.
#[test]
fn a_body_may_want_more_registers_than_a_machine_has() {
    let p = lowered(
        "fn f(a: i32): i32 { a + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 \
         + 14 + 15 + 16 + 17 + 18 + 19 + 20 + 21 + 22 + 23 + 24 + 25 }\n",
    );
    let body = body_of(&p, "1f");
    assert!(body.regs.len() > machine().ints.len(), "{} registers", body.regs.len());
}

// ---- What the runtime is told ----------------------------------------------

// A `str` is fat everywhere in the compiler -- `layout` says two words and
// `indirect` therefore says a register holding one holds its address -- so a
// literal has to build the pair. One that made only the pointer would be the
// one `str` in the language with no length beside it.
#[test]
fn a_string_literal_builds_a_pointer_and_a_length() {
    let p = lowered("fn f(): str { \"hello\" }\n");
    let kinds = held(&p, "1f");
    assert!(
        kinds.iter().any(|k| matches!(k, MIRInstKind::Const(MIRConst::Int(5)))),
        "the length is not written: {:#?}",
        kinds
    );
    assert_eq!(
        kinds.iter().filter(|k| matches!(k, MIRInstKind::Store { .. })).count(),
        2,
        "a pointer and a length are two stores: {:#?}",
        kinds
    );
}

fn calls(p: &MIRProgram, name: &str, want: &str) -> Vec<Vec<MIRRegId>> {
    held(p, name)
        .iter()
        .filter_map(|k| match k {
            MIRInstKind::Call { to: MIRCallee::Symbol(held), args } if held == want => {
                Some(args.clone())
            }
            _ => None,
        })
        .collect()
}

fn shapes(p: &MIRProgram) -> Vec<String> {
    p.pool
        .iter()
        .map(|held| held.symbol.clone())
        .filter(|held| held.starts_with("__T"))
        .collect()
}

// The whole reason a descriptor exists: `__rt_map_insert` is one symbol for
// every `K` in the program, and the register the key arrives in says nothing
// about what is in it.
#[test]
fn a_map_is_made_with_a_descriptor_for_its_key_and_its_value() {
    let p = lowered(
        "struct Map<K, V> {}\n\
         fn f(a: i32, b: i64) { let m = {a: b} }\n",
    );
    let made = calls(&p, "1f", "__rt_map_new");
    assert_eq!(made.len(), 1, "{:#?}", held(&p, "1f"));
    assert_eq!(made[0].len(), 2, "a key and a value");
    let held = shapes(&p);
    assert!(held.contains(&"__T3i32".to_string()), "{:?}", held);
    assert!(held.contains(&"__T3i64".to_string()), "{:?}", held);
}

#[test]
fn a_set_is_made_with_a_descriptor_for_its_element() {
    let p = lowered("struct Set<T> {}\nfn f(a: i32) { let s = {a} }\n");
    let made = calls(&p, "1f", "__rt_set_new");
    assert_eq!(made.len(), 1);
    assert_eq!(made[0].len(), 1);
    assert!(shapes(&p).contains(&"__T3i32".to_string()));
}

// A descriptor is under the type's own name and not a number, so two bodies
// wanting the same type name the same thing -- otherwise the pool would hold
// the same bytes twice and a linker would keep both.
#[test]
fn two_bodies_wanting_one_type_name_one_descriptor() {
    let p = lowered(
        "struct Set<T> {}\n\
         fn f(a: i32) { let s = {a} }\n\
         fn g(a: i32) { let s = {a} }\n",
    );
    assert_eq!(shapes(&p), vec!["__T3i32".to_string()]);
}

// The handle is one word. Where a library declares `Map` with fields, the type
// is indirect and the register holds an address by convention -- so the handle
// goes into a slot rather than being read as one.
#[test]
fn a_handle_goes_into_a_slot_where_the_type_is_indirect() {
    let p = lowered(
        "struct Set<T> {\n    pub h: i64,\n}\n\
         fn f(a: i32) { let s = {a} }\n",
    );
    let kinds = held(&p, "1f");
    let at = kinds
        .iter()
        .position(|k| matches!(k, MIRInstKind::Call { to: MIRCallee::Symbol(h), .. }
            if h == "__rt_set_new"))
        .expect("a call");
    assert!(
        kinds[at..].iter().any(|k| matches!(k, MIRInstKind::Frame(_))),
        "the handle was not given room: {:#?}",
        kinds
    );
}

// ---- The write barrier -----------------------------------------------------

// A pointer written through an address that is not in this frame goes through
// the collector, or the marker and the program between them can hide an
// object.
#[test]
fn a_pointer_written_outside_the_frame_goes_through_the_barrier() {
    let p = lowered(
        "struct Node {\n    pub n: i32,\n}\n\
         fn f(xs: &(*Node)[], i: i32, n: *Node) { xs[i] = n }\n",
    );
    assert_eq!(calls(&p, "1f", "__rt_write").len(), 1, "{:#?}", held(&p, "1f"));
}

// And one written into this frame does not. That is not an optimisation: a
// stack is scanned once and left black, and what makes that sound is the
// deletion half of the barrier, which does not depend on seeing stack writes.
#[test]
fn a_pointer_written_into_the_frame_is_a_plain_store() {
    let p = lowered(
        "struct Node {\n    pub n: i32,\n}\n\
         fn f(a: *Node) { var b = a }\n",
    );
    assert!(calls(&p, "1f", "__rt_write").is_empty(), "{:#?}", held(&p, "1f"));
}

// A number is not a pointer, so nothing about it can be hidden from a marker
// and the barrier would be a call per assignment buying nothing.
#[test]
fn a_number_written_anywhere_is_a_plain_store() {
    let p = lowered(
        "struct Node {\n    pub n: i32,\n}\n\
         fn f(xs: &i32[], i: i32, v: i32) { xs[i] = v }\n",
    );
    assert!(calls(&p, "1f", "__rt_write").is_empty(), "{:#?}", held(&p, "1f"));
}

// ---- What a closure keeps --------------------------------------------------

// The environment is the collector's, and described: every word of it is an
// address. Before there was a shape to pass it was room nothing ever freed.
#[test]
fn a_closures_environment_is_collected_and_described() {
    let p = lowered("fn f(a: i32): i32 { let g = |x: i32| x + a\n    g(1) }\n");
    let made: Vec<Vec<MIRRegId>> = p
        .bodies
        .iter()
        .flat_map(|body| {
            body.blocks.iter().flat_map(|b| b.insts.iter()).filter_map(|inst| match &inst.kind {
                MIRInstKind::Call { to: MIRCallee::Symbol(h), args }
                    if h == "__rt_gc_alloc" =>
                {
                    Some(args.clone())
                }
                _ => None,
            })
        })
        .collect();
    assert_eq!(made.len(), 1, "an environment is asked for once");
    assert_eq!(made[0].len(), 2, "how many bytes, and what is in them");
    assert!(
        p.pool.iter().any(|held| held.symbol.starts_with("__Tenv")),
        "{:?}",
        p.pool.iter().map(|h| &h.symbol).collect::<Vec<_>>()
    );
}

// ---- Where the elements are ------------------------------------------------

// An array *is* its elements; a run is a pointer to them. A run indexed off
// its own address would read the pointer and the length as the first two
// elements, which is a wrong answer that looks like an answer.
#[test]
fn indexing_a_run_reads_where_its_elements_are_first() {
    let p = lowered("fn f(xs: &i32[], i: i32): i32 { xs[i] }\n");
    let kinds = held(&p, "1f");
    let at = kinds
        .iter()
        .position(|k| matches!(k, MIRInstKind::Scaled { .. }))
        .expect("an index");
    assert!(
        kinds[..at].iter().any(|k| matches!(k, MIRInstKind::Load { .. })),
        "the elements were not looked up: {:#?}",
        kinds
    );
}

#[test]
fn indexing_an_array_reads_nothing_first() {
    let p = lowered("fn f(xs: i32[4], i: i32): i32 { xs[i] }\n");
    let kinds = held(&p, "1f");
    let at = kinds
        .iter()
        .position(|k| matches!(k, MIRInstKind::Scaled { .. }))
        .expect("an index");
    assert!(
        !kinds[..at].iter().any(|k| matches!(k, MIRInstKind::Load { .. })),
        "an array is its own elements: {:#?}",
        kinds
    );
}

// ---- Reading and writing through a pointer -----------------------------------

// `deref p` is a read out of memory and has to be one all the way down.
//
// It began as a `Unary`, which type-checked and ran and was wrong the moment
// anything optimised it: `sir::opt::share` folds two identical unary
// instructions into one, because an operator over the same operand gives the
// same answer twice. That is true of `-x` and false of what is at an address.
// So the shape is asserted here rather than the behaviour, because the
// behaviour was right until a pass looked at it.
#[test]
fn reading_through_a_pointer_is_a_load() {
    let p = lowered("fn f(p: ptr i32): i32 {\n    unsafe let v = deref p\n    v\n}\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Load { .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// And writing through one is a store to what it holds -- not to a slot holding
// it, which is the same mistake the write side of a place made everywhere
// before `sir::lower::base_of`.
#[test]
fn writing_through_a_pointer_is_a_store_to_what_it_holds() {
    let p = lowered("fn f(p: ptr i32, v: i32) {\n    unsafe deref p = v\n}\n");
    let kinds = held(&p, "1f");
    assert!(
        kinds.iter().any(|k| matches!(k, MIRInstKind::Store { .. })),
        "{:#?}",
        kinds
    );
    assert!(
        !kinds.iter().any(|k| matches!(k, MIRInstKind::Frame(_))),
        "the value went into the frame instead of through the pointer: {:#?}",
        kinds
    );
}

// A pointer is indexed by the stride of what it points at. It is asked before
// anything is stripped off the type, because stripping a `ptr T` leaves a `T`
// and a `T` is not what the stride is of -- which gave every `Vec<T>` a stride
// of a word, so a `Vec<i32>` read every other element and half of the one
// after it.
#[test]
fn a_pointer_is_indexed_by_the_stride_of_what_it_points_at() {
    let p = lowered("fn f(p: ptr i32, i: i64): i32 {\n    unsafe let v = p[i]\n    v\n}\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Scaled { scale: 4, .. })),
        "{:#?}",
        held(&p, "1f")
    );
    let p = lowered("fn f(p: ptr i64, i: i64): i64 {\n    unsafe let v = p[i]\n    v\n}\n");
    assert!(
        has(&p, "1f", |k| matches!(k, MIRInstKind::Scaled { scale: 8, .. })),
        "{:#?}",
        held(&p, "1f")
    );
}

// And it is indexed off what it holds rather than off where it is held, which
// is the same thing being said as for a run: `p` *is* the address of element
// zero.
#[test]
fn indexing_a_pointer_reads_nothing_first() {
    let p = lowered("fn f(p: ptr i32, i: i64): i32 {\n    unsafe let v = p[i]\n    v\n}\n");
    let kinds = held(&p, "1f");
    let at = kinds
        .iter()
        .position(|k| matches!(k, MIRInstKind::Scaled { .. }))
        .expect("an index");
    assert!(
        !kinds[..at].iter().any(|k| matches!(k, MIRInstKind::Load { .. })),
        "a pointer already is where its elements are: {:#?}",
        kinds
    );
}

// ---- A register holding an address is the width of one -----------------------

// The type on an `*Addr` value is the type of the place it addresses, so
// sizing its register by that type sizes it by the wrong thing. It went unseen
// while every place with an address was a structure -- `indirect` gives those
// a word anyway -- and `p[i] = v` on a `ptr i32` is the first place a *small*
// type is reached by address. The register came out four bytes, and four bytes
// is three quarters of an address.
#[test]
fn a_register_made_to_hold_an_address_is_a_whole_address_wide() {
    let p = lowered(
        "fn f(p: ptr i32, i: i64, v: i32) {\n    unsafe p[i] = v\n}\n",
    );
    let body = body_of(&p, "1f");
    let word = crate::mir::machine::X86_64.word;
    for (at, inst) in body.blocks.iter().flat_map(|b| b.insts.iter()).enumerate() {
        let Some(def) = inst.def else { continue };
        if !matches!(
            inst.kind,
            MIRInstKind::Frame(_) | MIRInstKind::Offset { .. } | MIRInstKind::Scaled { .. }
        ) {
            continue;
        }
        assert_eq!(
            body.regs[def].bytes, word,
            "instruction {} makes an address in {} bytes",
            at, body.regs[def].bytes
        );
    }
}

// ---- A fn named as a value -----------------------------------------------

// A `fn` is fat: where the code is, and where the captures are
// (`mir::layout`). A closure builds both words, and a plain fn named as a
// value has to build them too -- everything that reads a fn value reads the
// first word *out* of it, so a bare code address read that way hands back the
// first eight bytes of the machine code and calls them.
//
// Nothing caught it because a call of a fn known here names the symbol
// directly. It takes a fn value that reached its caller through a parameter or
// a field, which is what a comparator is.
#[test]
fn a_fn_named_as_a_value_is_built_as_the_pair_a_fn_value_is() {
    let p = lowered(
        "fn inc(x: i64): i64 {\n    x + 1\n}\n         fn dec(x: i64): i64 {\n    x - 1\n}\n         fn pick(b: bool): fn(i64): i64 {\n    if b { inc } else { dec }\n}\n",
    );
    let kinds = held(&p, "4pick");
    assert!(
        kinds.iter().any(|k| matches!(k, MIRInstKind::Frame(_))),
        "no room was taken for the pair: {:#?}",
        kinds
    );
    // Both words written: the code, and the environment there is none of.
    let stores = kinds.iter().filter(|k| matches!(k, MIRInstKind::Store { .. })).count();
    assert!(stores >= 4, "the two arms write two words each: {:#?}", kinds);
}

// ---- A name that stands for somewhere --------------------------------------

// A global named as a value is a read *through* the symbol and not the symbol.
// It used to be the symbol, so every global in the language read as its own
// address. (A `const` no longer reaches here at all -- `sema` puts its value
// where the name was, which is what a compile-time constant is.)
#[test]
fn a_global_named_as_a_value_is_read_through() {
    let p = lowered("var G: i64 = 7\nfn f(): i64 {\n    G\n}\n");
    let kinds = held(&p, "1f");
    let at = kinds
        .iter()
        .position(|k| matches!(k, MIRInstKind::Symbol(_)))
        .expect("the global's name");
    assert!(
        kinds[at + 1..].iter().any(|k| matches!(k, MIRInstKind::Load { .. })),
        "the address was handed back instead of what is at it: {:#?}",
        kinds
    );
}

// ---- Answering with something too big for a register -------------------------

// A value held by its address is held in somebody's frame, and a body that
// answered with one of its own would answer with an address that dies at the
// epilogue. It did: `ret` handed back a `lea` of a local slot, and the caller
// read whatever was there next.
//
// So the room is the caller's, handed over in front of the written arguments.
#[test]
fn a_body_that_answers_with_an_aggregate_takes_the_room_for_it() {
    let p = lowered(
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n",
    );
    let body = body_of(&p, "2mk");
    assert_eq!(body.params.len(), 2, "one written parameter and the room");
}

// And it copies its answer there rather than handing back where it built it.
#[test]
fn the_answer_is_copied_into_the_room_the_caller_gave() {
    let p = lowered(
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n",
    );
    let body = body_of(&p, "2mk");
    let kinds = kinds(body);
    assert!(
        kinds.iter().any(|k| matches!(k, MIRInstKind::Copy { .. })),
        "nothing is copied out: {:#?}",
        kinds
    );
    // What it answers with is the room, which is its first parameter.
    let room = body.params[0];
    let back = body.blocks.iter().find_map(|b| match b.term {
        MIRTerm::Return(held) => held,
        _ => None,
    });
    assert_eq!(back, Some(room), "it answers with something that is not the room");
}

// A body whose answer fits a register takes nothing extra, or every call in a
// program would carry an argument for nothing.
#[test]
fn a_body_that_answers_with_a_number_takes_no_room() {
    let p = lowered("fn f(n: i64): i64 { n }\n");
    assert_eq!(body_of(&p, "1f").params.len(), 1);
}

// The caller's side: it makes the room and hands it over.
#[test]
fn a_call_that_answers_with_an_aggregate_hands_over_room() {
    let p = lowered(
        "struct P {\n    pub a: i64,\n    pub b: i64,\n}\n\
         fn mk(n: i64): P {\n    P { a: n, b: n }\n}\n\
         fn f(n: i64): i64 {\n    let p = mk(n)\n    p.a\n}\n",
    );
    let body = body_of(&p, "1f");
    let held: Vec<usize> = kinds(body)
        .iter()
        .filter_map(|k| match k {
            MIRInstKind::Call { args, .. } => Some(args.len()),
            _ => None,
        })
        .collect();
    assert_eq!(held, vec![2], "the room and the written argument");
    assert!(!body.frame.is_empty(), "the room is a slot of the caller's frame");
}
