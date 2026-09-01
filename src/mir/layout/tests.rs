// Where the bytes go, checked against declarations written by hand.
//
// A layout is the one thing here that can be wrong without anything looking
// wrong: a field read four bytes from the start of a structure whose second
// field begins at eight reads half of one thing and half of another, and every
// pass downstream is happy. So these are written as the offsets themselves and
// not as "it works" -- the number is the answer, and the number is what is
// asserted.
//
// The types are built straight into a `TTIRProgram` rather than through
// `gir::fixture`, for the reason that fixture gives one level up: going through
// the checker would put the checker under test as well, and what is wanted here
// is a declaration with known fields and nothing else.

use crate::tir::tir_nodes::{TIRAttrs, TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::*;

use super::super::machine;
use super::*;

// A type arena and the declarations that reach into it.
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

    fn i8(&mut self) -> TyId {
        self.prim(TIRPrim::I8)
    }

    fn i16(&mut self) -> TyId {
        self.prim(TIRPrim::I16)
    }

    fn i32(&mut self) -> TyId {
        self.prim(TIRPrim::I32)
    }

    fn i64(&mut self) -> TyId {
        self.prim(TIRPrim::I64)
    }

    fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    // A structure whose fields are the types given, in that order.
    fn structure(&mut self, name: &str, fields: &[TyId]) -> TTIRItemId {
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
        self.item(TTIRItemKind::Struct {
            vis: TIRVis::Unwritten,
            attrs: TIRAttrs::default(),
            name: name.to_string(),
            generics: Vec::new(),
            fields,
        })
    }

    // The same, but taking one type parameter, so that `T` may be laid out
    // against whatever the use hands it.
    fn generic(&mut self, name: &str, fields: &[TyId]) -> TTIRItemId {
        let at = self.structure(name, fields);
        if let TTIRItemKind::Struct { generics, .. } = &mut self.p.items[at].kind {
            *generics = vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }];
        }
        at
    }

    // An enum, each variant given as its payload and the number the checker
    // would have worked out for it.
    fn enumeration(&mut self, name: &str, variants: &[(Vec<TyId>, i64)]) -> TTIRItemId {
        let variants = variants
            .iter()
            .enumerate()
            .map(|(at, (payload, value))| TTIRVariant {
                attrs:   TIRAttrs::default(),
                name:    format!("V{}", at),
                payload: if payload.is_empty() {
                    TTIRPayload::None
                } else {
                    TTIRPayload::Tuple(payload.clone())
                },
                value:   *value,
            })
            .collect();
        self.item(TTIRItemKind::Enum {
            vis: TIRVis::Unwritten,
            attrs: TIRAttrs::default(),
            name: name.to_string(),
            generics: Vec::new(),
            variants,
        })
    }

    fn named(&mut self, item: TTIRItemId, args: Vec<TyId>) -> TyId {
        self.intern(Ty::Named { item, args, regions: Vec::new() })
    }
}

// Pinned rather than the host's, so that an offset asserted here is the same
// offset wherever the tests are run.
fn laid(h: &Held) -> Layouts<'_> {
    Layouts::new(&h.p, machine::X86_64)
}

// ---- The primitives --------------------------------------------------------

#[test]
fn a_primitive_is_as_wide_as_its_name_says() {
    let mut h = Held::new();
    let (a, b, c, d) = (h.i8(), h.i16(), h.i32(), h.i64());
    let mut l = laid(&h);
    assert_eq!(l.bytes(a), Some(1));
    assert_eq!(l.bytes(b), Some(2));
    assert_eq!(l.bytes(c), Some(4));
    assert_eq!(l.bytes(d), Some(8));
    assert_eq!(l.align(d), Some(8), "and is aligned to itself");
}

// A `char` is one Unicode scalar value however few of them are used, which is
// four bytes and not one.
#[test]
fn a_char_is_four_bytes_and_a_bool_is_one() {
    let mut h = Held::new();
    let (c, b) = (h.prim(TIRPrim::Char), h.prim(TIRPrim::Bool));
    let mut l = laid(&h);
    assert_eq!(l.bytes(c), Some(4));
    assert_eq!(l.bytes(b), Some(1));
}

#[test]
fn null_and_never_take_no_room() {
    let mut h = Held::new();
    let (n, v) = (h.prim(TIRPrim::Null), h.prim(TIRPrim::Never));
    let mut l = laid(&h);
    assert_eq!(l.of(n).map(|held| held.shape), Some(Shape::Empty));
    assert_eq!(l.bytes(n), Some(0));
    assert_eq!(l.bytes(v), Some(0));
}

// ---- What is a pointer, and what is two ------------------------------------

#[test]
fn a_reference_a_pointer_and_a_gc_handle_are_one_word() {
    let mut h = Held::new();
    let inner = h.i32();
    let r = h.intern(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner });
    let p = h.intern(Ty::Ptr(inner));
    let g = h.intern(Ty::GC(inner));
    let mut l = laid(&h);
    for ty in [r, p, g] {
        assert_eq!(l.bytes(ty), Some(8));
        assert_eq!(l.of(ty).map(|held| held.shape), Some(Shape::Scalar));
    }
}

// A run has no length in its type, so the length travels with the pointer.
#[test]
fn a_run_a_string_and_a_fn_value_are_two_words() {
    let mut h = Held::new();
    let elem = h.i32();
    let run = h.intern(Ty::Run(elem));
    let str_ = h.prim(TIRPrim::Str);
    let f = h.intern(Ty::Fn {
        uses:      crate::tir::tir_nodes::TIRFnUses::Reads,
        params:    Vec::new(),
        ret:       elem,
        is_unsafe: false,
    });
    let mut l = laid(&h);
    for ty in [run, str_, f] {
        assert_eq!(l.bytes(ty), Some(16), "a pointer and one more word");
        assert_eq!(l.align(ty), Some(8));
        assert_eq!(l.of(ty).map(|held| held.shape), Some(Shape::Fat));
    }
}

// ---- Structures ------------------------------------------------------------

// The narrow field is written first and stays first, so the wide one is pushed
// to the next offset its own alignment allows and the seven bytes between are
// left alone. Reordering would save them and is not done -- see the header.
#[test]
fn a_byte_before_a_word_leaves_the_padding_where_it_falls() {
    let mut h = Held::new();
    let (a, b) = (h.i8(), h.i64());
    let item = h.structure("Pair", &[a, b]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.field(ty, 0), Some(0));
    assert_eq!(l.field(ty, 1), Some(8), "the word cannot begin at one");
    assert_eq!(l.bytes(ty), Some(16));
    assert_eq!(l.align(ty), Some(8), "the widest field's");
}

// The same two fields the other way round need no padding between them, which
// is the saving that reordering would have found. That the two differ is the
// point: the order written is the order laid out.
#[test]
fn the_order_written_is_the_order_laid_out() {
    let mut h = Held::new();
    let (a, b) = (h.i8(), h.i64());
    let wide_first = h.structure("Wide", &[b, a]);
    let ty = h.named(wide_first, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.field(ty, 0), Some(0), "the word");
    assert_eq!(l.field(ty, 1), Some(8), "and the byte after it");
    assert_eq!(l.bytes(ty), Some(16), "rounded up so a run of them stays aligned");
}

#[test]
fn a_structure_with_no_fields_takes_no_room() {
    let mut h = Held::new();
    let item = h.structure("Nothing", &[]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.bytes(ty), Some(0));
    assert_eq!(l.align(ty), Some(1));
    assert_eq!(l.of(ty).map(|held| held.shape), Some(Shape::Empty));
}

// A structure inside a structure is laid out whole and aligned as a whole, so
// the inner one's own alignment reaches the outer one.
#[test]
fn a_nested_structure_carries_its_alignment_outwards() {
    let mut h = Held::new();
    let (byte, word) = (h.i8(), h.i64());
    let inner = h.structure("Inner", &[byte, word]);
    let inner_ty = h.named(inner, Vec::new());
    let outer = h.structure("Outer", &[byte, inner_ty]);
    let outer_ty = h.named(outer, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.bytes(inner_ty), Some(16));
    assert_eq!(l.field(outer_ty, 0), Some(0), "the byte");
    assert_eq!(l.field(outer_ty, 1), Some(8), "and the inner one, on its own alignment");
    assert_eq!(l.bytes(outer_ty), Some(24));
    assert_eq!(l.align(outer_ty), Some(8), "which came from inside");
}

// A tuple is a structure whose fields are numbered rather than named, and
// nothing here tells the two apart.
#[test]
fn a_tuple_is_laid_out_as_a_structure_is() {
    let mut h = Held::new();
    let (a, b) = (h.i8(), h.i64());
    let tuple = h.intern(Ty::Tuple(vec![a, b]));
    let item = h.structure("Same", &[a, b]);
    let named = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.of(tuple).map(|held| held.shape), l.of(named).map(|held| held.shape));
    assert_eq!(l.bytes(tuple), l.bytes(named));
}

// ---- Runs of one thing -----------------------------------------------------

#[test]
fn an_array_is_its_length_times_the_stride() {
    let mut h = Held::new();
    let elem = h.i32();
    let array = h.intern(Ty::Array { elem, len: 8 });
    let mut l = laid(&h);
    assert_eq!(l.bytes(array), Some(32));
    assert_eq!(l.align(array), Some(4), "the element's");
    assert_eq!(
        l.of(array).map(|held| held.shape),
        Some(Shape::Elements { stride: 4, len: 8 })
    );
}

// The stride is the size rounded up to the alignment, which is what an index is
// multiplied by. For a structure the two are already equal -- the rounding
// happened when it was laid out -- and that is worth pinning, because a stride
// that disagreed with the size is how neighbouring elements overlap.
#[test]
fn an_array_of_structures_steps_by_the_whole_structure() {
    let mut h = Held::new();
    let (byte, word) = (h.i8(), h.i64());
    let item = h.structure("Pair", &[byte, word]);
    let ty = h.named(item, Vec::new());
    let array = h.intern(Ty::Array { elem: ty, len: 3 });
    let mut l = laid(&h);
    assert_eq!(l.stride(ty), Some(16));
    assert_eq!(l.bytes(array), Some(48));
}

#[test]
fn an_empty_array_takes_no_room() {
    let mut h = Held::new();
    let elem = h.i32();
    let array = h.intern(Ty::Array { elem, len: 0 });
    let mut l = laid(&h);
    assert_eq!(l.bytes(array), Some(0));
}

// ---- Enums -----------------------------------------------------------------

// Three variants fit in a byte, so the tag is a byte -- and the payload begins
// at the first offset its own alignment allows, not immediately after the tag.
#[test]
fn an_enum_is_a_tag_and_then_the_widest_variant() {
    let mut h = Held::new();
    let word = h.i64();
    let item = h.enumeration("E", &[(vec![], 0), (vec![word], 1), (vec![], 2)]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.tag(ty), Some(1), "three variants need one byte");
    assert_eq!(l.payload(ty, 1, 0), Some(8), "the word waits for its alignment");
    assert_eq!(l.bytes(ty), Some(16));
    assert_eq!(l.align(ty), Some(8));
}

// Every variant's payload begins at the same offset, which is what lets the
// address be worked out before the discriminant has been tested.
#[test]
fn every_variant_begins_at_the_same_offset() {
    let mut h = Held::new();
    let (a, b) = (h.i32(), h.i32());
    let item = h.enumeration("E", &[(vec![a], 0), (vec![b, a], 1)]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.payload(ty, 0, 0), l.payload(ty, 1, 0), "one place to start");
    let first = l.payload(ty, 1, 0).expect("a payload");
    assert_eq!(l.payload(ty, 1, 1), Some(first + 4), "and the second beside it");
}

#[test]
fn a_variant_with_no_payload_has_no_offsets() {
    let mut h = Held::new();
    let word = h.i64();
    let item = h.enumeration("E", &[(vec![], 0), (vec![word], 1)]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.payload(ty, 0, 0), None);
    assert_eq!(l.payload(ty, 1, 0), Some(8));
}

// The tag widens to hold what the checker gave the variants, which is not the
// same as counting them: two variants numbered 0 and 1000 do not fit in a byte.
#[test]
fn the_tag_is_as_wide_as_the_numbers_the_checker_gave() {
    let mut h = Held::new();
    let small = h.enumeration("Small", &[(vec![], 0), (vec![], 255)]);
    let big = h.enumeration("Big", &[(vec![], 0), (vec![], 1000)]);
    let huge = h.enumeration("Huge", &[(vec![], 0), (vec![], 1 << 40)]);
    let (a, b, c) =
        (h.named(small, Vec::new()), h.named(big, Vec::new()), h.named(huge, Vec::new()));
    let mut l = laid(&h);
    assert_eq!(l.tag(a), Some(1));
    assert_eq!(l.tag(b), Some(2));
    assert_eq!(l.tag(c), Some(8));
}

// A written discriminant may be negative, and a byte holding -1 has to be a
// signed one -- so 200 and -1 together no longer fit where 200 alone did.
#[test]
fn a_negative_discriminant_makes_the_tag_signed() {
    let mut h = Held::new();
    let unsigned = h.enumeration("U", &[(vec![], 0), (vec![], 200)]);
    let signed = h.enumeration("S", &[(vec![], -1), (vec![], 200)]);
    let (a, b) = (h.named(unsigned, Vec::new()), h.named(signed, Vec::new()));
    let mut l = laid(&h);
    assert_eq!(l.tag(a), Some(1), "0 to 200 is a byte");
    assert_eq!(l.tag(b), Some(2), "-1 to 200 is not");
}

#[test]
fn an_enum_with_no_variants_takes_no_room() {
    let mut h = Held::new();
    let item = h.enumeration("Nothing", &[]);
    let ty = h.named(item, Vec::new());
    let mut l = laid(&h);
    assert_eq!(l.bytes(ty), Some(0));
}

// ---- Type parameters -------------------------------------------------------

// The `None` the header is about, and the only one that is not a mistake: a
// parameter with nothing standing in for it. `mir::mono` is what leaves none.
#[test]
fn a_type_parameter_with_nothing_standing_in_has_no_layout() {
    let mut h = Held::new();
    let param = h.intern(Ty::Param { name: "T".to_string(), index: 0 });
    let mut l = laid(&h);
    assert_eq!(l.of(param), None);
}

// Reached through a use that says what it is, the same parameter has one.
#[test]
fn a_type_parameter_is_laid_out_as_what_the_use_handed_it() {
    let mut h = Held::new();
    let param = h.intern(Ty::Param { name: "T".to_string(), index: 0 });
    let byte = h.i8();
    let item = h.generic("Held", &[param]);
    let of_word = {
        let word = h.i64();
        h.named(item, vec![word])
    };
    let of_byte = h.named(item, vec![byte]);
    let mut l = laid(&h);
    assert_eq!(l.bytes(of_word), Some(8));
    assert_eq!(l.bytes(of_byte), Some(1));
}

// The same `TyId` laid out against two arguments is two answers, so neither may
// be cached under it -- which is what the empty-environment condition in
// `of_in` is for. Asking in the other order gives the other answer.
#[test]
fn two_uses_of_one_generic_do_not_share_an_answer() {
    let mut h = Held::new();
    let param = h.intern(Ty::Param { name: "T".to_string(), index: 0 });
    let item = h.generic("Held", &[param]);
    let byte = h.i8();
    let word = h.i64();
    let of_byte = h.named(item, vec![byte]);
    let of_word = h.named(item, vec![word]);
    let mut l = laid(&h);
    assert_eq!(l.bytes(of_word), Some(8));
    assert_eq!(l.bytes(of_byte), Some(1), "and the first did not answer for the second");
    assert_eq!(l.bytes(of_word), Some(8), "still");
}

// ---- What has no size at all -----------------------------------------------

// A structure that holds one of itself is infinitely large. The walk would look
// for the size forever, so the types being worked out are kept and one that
// comes round again is refused.
#[test]
fn a_type_that_holds_itself_has_no_layout() {
    let mut h = Held::new();
    let item = h.item(TTIRItemKind::Struct {
        vis: TIRVis::Unwritten,
        attrs: TIRAttrs::default(),
        name: "Loop".to_string(),
        generics: Vec::new(),
        fields: Vec::new(),
    });
    let ty = h.named(item, Vec::new());
    if let TTIRItemKind::Struct { fields, .. } = &mut h.p.items[item].kind {
        *fields = vec![TTIRFieldDecl {
            vis:   TIRVis::Unwritten,
            attrs: TIRAttrs::default(),
            name:  "me".to_string(),
            ty,
        }];
    }
    let mut l = laid(&h);
    assert_eq!(l.of(ty), None);
}

// Holding a *pointer* to one of itself is the ordinary way to write a list, and
// it is finite: the pointer is a word whatever it points at.
#[test]
fn a_type_that_points_at_itself_is_one_word_of_it() {
    let mut h = Held::new();
    let item = h.item(TTIRItemKind::Struct {
        vis: TIRVis::Unwritten,
        attrs: TIRAttrs::default(),
        name: "List".to_string(),
        generics: Vec::new(),
        fields: Vec::new(),
    });
    let ty = h.named(item, Vec::new());
    let next = h.intern(Ty::Ptr(ty));
    let value = h.i32();
    if let TTIRItemKind::Struct { fields, .. } = &mut h.p.items[item].kind {
        *fields = vec![
            TTIRFieldDecl {
                vis:   TIRVis::Unwritten,
                attrs: TIRAttrs::default(),
                name:  "value".to_string(),
                ty:    value,
            },
            TTIRFieldDecl {
                vis:   TIRVis::Unwritten,
                attrs: TIRAttrs::default(),
                name:  "next".to_string(),
                ty:    next,
            },
        ];
    }
    let mut l = laid(&h);
    assert_eq!(l.field(ty, 0), Some(0));
    assert_eq!(l.field(ty, 1), Some(8), "the pointer, on its own alignment");
    assert_eq!(l.bytes(ty), Some(16));
}

// Neither survives a program the checker accepted, so reaching one means
// something upstream let a refused program through.
#[test]
fn a_hole_and_an_error_have_no_layout() {
    let mut h = Held::new();
    let hole = h.intern(Ty::Var(0));
    let wrong = h.intern(Ty::Error);
    let mut l = laid(&h);
    assert_eq!(l.of(hole), None);
    assert_eq!(l.of(wrong), None);
}
