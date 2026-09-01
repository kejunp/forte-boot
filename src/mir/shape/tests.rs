// Which words a type's descriptor calls pointers, and where each field of one
// sits.
//
// Two halves of this project read these bytes and neither can check the other:
// `fortec_rt::shape` reads offset 24 for the kind and offset 32 for the map,
// and if this wrote them anywhere else nothing would say so until a collector
// followed a number. So the offsets are asserted as numbers here, and the same
// numbers are asserted from the far side in `runtime/src/shape/tests.rs`.
//
// The types are built straight into a `TTIRProgram`, for the reason
// `layout/tests.rs` gives one file over: going through the checker would put
// the checker under test as well, and what is wanted is a declaration with
// known fields.

use crate::tir::tir_nodes::{TIRAttrs, TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::*;

use super::super::machine;
use super::*;

// ---- Types by hand ---------------------------------------------------------

// The same builder `layout/tests.rs` has, for the same reason.
struct Held {
    p: TTIRProgram,
}

impl Held {
    fn new() -> Held {
        Held { p: TTIRProgram::default() }
    }

    fn intern(&mut self, ty: Ty) -> TyId {
        self.p.types.push(ty);
        self.p.types.len() - 1
    }

    fn prim(&mut self, p: TIRPrim) -> TyId {
        self.intern(Ty::Prim(p))
    }

    fn i32(&mut self) -> TyId {
        self.prim(TIRPrim::I32)
    }

    fn i64(&mut self) -> TyId {
        self.prim(TIRPrim::I64)
    }

    fn refer(&mut self, inner: TyId) -> TyId {
        self.intern(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner })
    }

    fn pointer(&mut self, inner: TyId) -> TyId {
        self.intern(Ty::Ptr(inner))
    }

    fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    fn strukt(&mut self, name: &str, fields: &[TyId]) -> TyId {
        let fields = fields
            .iter()
            .enumerate()
            .map(|(at, &ty)| TTIRFieldDecl {
                vis:   TIRVis::Unwritten,
                attrs: TIRAttrs::default(),
                name:  format!("f{}", at),
                ty,
            })
            .collect();
        let item = self.item(TTIRItemKind::Struct {
            vis: TIRVis::Unwritten,
            attrs: TIRAttrs::default(),
            name: name.to_string(),
            generics: Vec::new(),
            fields,
        });
        self.intern(Ty::Named { item, args: Vec::new(), regions: Vec::new() })
    }

    fn enom(&mut self, name: &str, payloads: &[Vec<TyId>]) -> TyId {
        let variants = payloads
            .iter()
            .enumerate()
            .map(|(at, payload)| TTIRVariant {
                attrs:   TIRAttrs::default(),
                name:    format!("V{}", at),
                payload: if payload.is_empty() {
                    TTIRPayload::None
                } else {
                    TTIRPayload::Tuple(payload.clone())
                },
                value:   at as i64,
            })
            .collect();
        let item = self.item(TTIRItemKind::Enum {
            vis: TIRVis::Unwritten,
            attrs: TIRAttrs::default(),
            name: name.to_string(),
            generics: Vec::new(),
            variants,
        });
        self.intern(Ty::Named { item, args: Vec::new(), regions: Vec::new() })
    }
}

// Pinned rather than the host's, so that a word count asserted here is the
// same count wherever the tests are run.
fn described(h: &Held, ty: TyId) -> Vec<u8> {
    let mut layouts = Layouts::new(&h.p, machine::X86_64);
    describe(&mut layouts, &h.p, machine::X86_64, ty).expect("a descriptor")
}

fn word(held: &[u8], at: usize) -> usize {
    usize::from_le_bytes(held[at..at + 8].try_into().expect("eight bytes"))
}

fn points(held: &[u8], at: usize) -> bool {
    let words = word(held, 16);
    at < words && held[HEADER + at / 8] >> (at % 8) & 1 == 1
}

fn any(held: &[u8]) -> bool {
    held[HEADER..].iter().any(|byte| *byte != 0)
}

// ---- The offsets -----------------------------------------------------------

// The contract, as numbers. Both halves are compiled separately and nothing
// checks that they agree.
#[test]
fn every_field_is_at_the_offset_the_runtime_reads_it_from() {
    let mut h = Held::new();
    let ty = h.i64();
    let held = described(&h, ty);
    assert_eq!(word(&held, 0), 8, "the size is at nought");
    assert_eq!(word(&held, 8), 8, "the alignment is at eight");
    assert_eq!(word(&held, 16), 1, "how many words is at sixteen");
    assert_eq!(held[24], Kind::Signed as u8, "the kind is at twenty-four");
    assert_eq!(held[25], 0, "whether it is indirect is at twenty-five");
    assert_eq!(HEADER, 32, "and the map begins at thirty-two");
}

#[test]
fn the_map_begins_on_a_word() {
    assert_eq!(HEADER % 8, 0);
}

// ---- What holds a pointer --------------------------------------------------

#[test]
fn a_number_holds_no_pointer() {
    let mut h = Held::new();
    for p in [TIRPrim::I8, TIRPrim::U64, TIRPrim::F64, TIRPrim::Bool, TIRPrim::Char] {
        let ty = h.prim(p);
        assert!(!any(&described(&h, ty)), "{:?}", p);
    }
}

#[test]
fn a_reference_and_a_pointer_are_each_one_pointer() {
    let mut h = Held::new();
    let inner = h.i32();
    for ty in [h.refer(inner), h.pointer(inner)] {
        let held = described(&h, ty);
        assert_eq!(word(&held, 16), 1);
        assert!(points(&held, 0));
    }
}

// A string is a pointer and a length, and only the first of the two is an
// address.
#[test]
fn a_string_names_its_first_word_and_not_its_second() {
    let mut h = Held::new();
    let ty = h.prim(TIRPrim::Str);
    let held = described(&h, ty);
    assert_eq!(word(&held, 16), 2);
    assert!(points(&held, 0));
    assert!(!points(&held, 1), "the length is a number");
}

// ---- Structures ------------------------------------------------------------

// The one that matters: a structure of a number and a reference names the
// second word and not the first.
#[test]
fn a_structure_names_the_words_that_are_references() {
    let mut h = Held::new();
    let (n, i) = (h.i64(), h.i32());
    let r = h.refer(i);
    let ty = h.strukt("Node", &[n, r]);
    let held = described(&h, ty);
    assert_eq!(word(&held, 0), 16);
    assert!(!points(&held, 0), "the number");
    assert!(points(&held, 1), "the reference");
}

#[test]
fn a_structure_of_numbers_names_nothing_and_is_never_scanned() {
    let mut h = Held::new();
    let (a, b) = (h.i64(), h.i32());
    let ty = h.strukt("Plain", &[a, b]);
    assert!(!any(&described(&h, ty)));
}

// A reference three fields deep is still a reference, and it has to come out
// at the offset the field is really at.
#[test]
fn a_pointer_inside_a_nested_structure_is_found_at_its_own_offset() {
    let mut h = Held::new();
    let i = h.i32();
    let n = h.i64();
    let r = h.refer(i);
    let inner = h.strukt("Inner", &[n, r]);
    let ty = h.strukt("Outer", &[n, inner]);
    let held = described(&h, ty);
    assert_eq!(word(&held, 0), 24);
    assert!(!points(&held, 0));
    assert!(!points(&held, 1), "the inner structure's number");
    assert!(points(&held, 2), "the inner structure's reference");
}

// Padding is not a pointer, and a byte followed by a word is where a naive
// count of fields would put the reference one word too early.
#[test]
fn padding_before_a_field_does_not_move_it() {
    let mut h = Held::new();
    let b = h.prim(TIRPrim::I8);
    let i = h.i32();
    let r = h.refer(i);
    let ty = h.strukt("Padded", &[b, r]);
    let held = described(&h, ty);
    assert_eq!(word(&held, 0), 16, "a byte, seven of padding, and a word");
    assert!(!points(&held, 0));
    assert!(points(&held, 1));
}

// ---- Arrays and tuples -----------------------------------------------------

#[test]
fn every_element_of_an_array_of_references_is_named() {
    let mut h = Held::new();
    let i = h.i32();
    let r = h.refer(i);
    let ty = h.intern(Ty::Array { elem: r, len: 4 });
    let held = described(&h, ty);
    assert_eq!(word(&held, 16), 4);
    for at in 0..4 {
        assert!(points(&held, at), "element {}", at);
    }
}

// The case the walk is written to avoid: a million elements holding nothing
// should not be a million walks to say so.
#[test]
fn an_array_of_numbers_names_nothing() {
    let mut h = Held::new();
    let n = h.i64();
    let ty = h.intern(Ty::Array { elem: n, len: 100_000 });
    assert!(!any(&described(&h, ty)));
}

#[test]
fn a_tuple_names_the_parts_that_are_references() {
    let mut h = Held::new();
    let i = h.i32();
    let n = h.i64();
    let r = h.refer(i);
    let ty = h.intern(Ty::Tuple(vec![n, r, n]));
    let held = described(&h, ty);
    assert!(!points(&held, 0));
    assert!(points(&held, 1));
    assert!(!points(&held, 2));
}

// ---- Enums -----------------------------------------------------------------

// The union over the variants, which the header argues for: which variant is
// in there is in the tag, and reading the tag would make the map a program.
#[test]
fn an_enum_names_every_word_that_is_a_pointer_in_any_variant() {
    let mut h = Held::new();
    let i = h.i32();
    let n = h.i64();
    let r = h.refer(i);
    // One variant holds a number where the other holds a reference.
    let ty = h.enom("Either", &[vec![n], vec![r]]);
    let held = described(&h, ty);
    assert!(any(&held), "one of the two variants holds a reference");
}

#[test]
fn an_enum_of_numbers_names_nothing() {
    let mut h = Held::new();
    let n = h.i64();
    let i = h.i32();
    let ty = h.enom("Plain", &[vec![n], vec![i], Vec::new()]);
    assert!(!any(&described(&h, ty)));
}

// ---- The kind --------------------------------------------------------------

#[test]
fn every_primitive_gets_the_kind_its_bytes_mean() {
    let mut h = Held::new();
    let cases = [
        (TIRPrim::I32, Kind::Signed),
        (TIRPrim::I8, Kind::Signed),
        (TIRPrim::U64, Kind::Unsigned),
        (TIRPrim::Bool, Kind::Unsigned),
        (TIRPrim::Char, Kind::Unsigned),
        (TIRPrim::F32, Kind::Float),
        (TIRPrim::Str, Kind::Str),
    ];
    for (p, want) in cases {
        let ty = h.prim(p);
        assert_eq!(described(&h, ty)[24], want as u8, "{:?}", p);
    }
}

#[test]
fn a_reference_is_a_pointer_and_a_structure_is_its_bytes() {
    let mut h = Held::new();
    let i = h.i32();
    let r = h.refer(i);
    assert_eq!(described(&h, r)[24], Kind::Pointer as u8);
    let s = h.strukt("Held", &[i]);
    assert_eq!(described(&h, s)[24], Kind::Opaque as u8);
}

// ---- Indirect --------------------------------------------------------------

// Which has to agree with `Lowerer::indirect`, or the runtime reads an
// argument the caller did not write.
#[test]
fn what_arrives_by_address_says_so_and_what_does_not_does_not() {
    let mut h = Held::new();
    let i = h.i32();
    assert_eq!(described(&h, i)[25], 0, "a number is itself");
    let r = h.refer(i);
    assert_eq!(described(&h, r)[25], 0, "so is an address");
    let s = h.strukt("Wide", &[i, i, i]);
    assert_eq!(described(&h, s)[25], 1, "a structure is its address");
    let t = h.prim(TIRPrim::Str);
    assert_eq!(described(&h, t)[25], 1, "and so is anything fat");
}

// ---- A closure's environment -----------------------------------------------

#[test]
fn an_environment_is_that_many_words_and_all_of_them_pointers() {
    let held = environment(3, machine::X86_64);
    assert_eq!(word(&held, 0), 24);
    assert_eq!(word(&held, 8), 8);
    assert_eq!(word(&held, 16), 3);
    for at in 0..3 {
        assert!(points(&held, at), "word {}", at);
    }
    assert_eq!(held[25], 1, "it is reached by its address");
}

#[test]
fn an_environment_with_nothing_in_it_is_still_a_descriptor() {
    let held = environment(0, machine::X86_64);
    assert_eq!(word(&held, 16), 0);
    assert!(!any(&held));
    assert!(held.len() >= HEADER);
}

// ---- Names -----------------------------------------------------------------

// Two bodies wanting the same type have to name the same thing, or the pool
// would hold the same bytes twice under two names and a linker would keep
// both.
#[test]
fn a_type_is_named_after_its_spelling() {
    let mut h = Held::new();
    let i = h.i32();
    let n = h.i64();
    let m = crate::sema::names::Mangler::new(&h.p);
    assert_eq!(symbol(&m, &h.p, i), "__T3i32");
    assert_ne!(symbol(&m, &h.p, i), symbol(&m, &h.p, n));
}
