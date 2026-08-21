// What a fn is compiled to. The TTIR is built by hand here for the reason
// `cfg::fixture` builds one by hand: `sema` is what would produce a TTIR from
// source, and it is not written.

use super::*;
use crate::tir::tir_nodes::{TIRAttrs, TIRFnAttrs, TIRInline};
use crate::tir::ttir_nodes::{TTIRItem, TTIRProgram};

// A program under construction, with the handful of types a symbol names.
struct Suite {
    p: TTIRProgram,
}

impl Suite {
    fn new() -> Suite {
        Suite { p: TTIRProgram::default() }
    }

    fn ty(&mut self, ty: Ty) -> TyId {
        // Deduplicated, as the checker's own arena is: two `i32`s are one
        // entry, so a handle comparison is a type comparison.
        if let Some(i) = self.p.types.iter().position(|held| *held == ty) {
            return i;
        }
        self.p.types.push(ty);
        self.p.types.len() - 1
    }

    fn prim(&mut self, prim: TIRPrim) -> TyId {
        self.ty(Ty::Prim(prim))
    }

    fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    // A fn of `params`, returning `null`, named `name`.
    fn func(&mut self, name: &str, params: Vec<TyId>) -> TTIRItemId {
        let ret = self.prim(TIRPrim::Null);
        let ty = self.ty(Ty::Fn { params, ret, is_unsafe: false });
        self.item(TTIRItemKind::Fn(TTIRFn {
            vis:       TIRVis::Pub,
            attrs:     attrs(None),
            is_const:  false,
            is_unsafe: false,
            name:      name.to_string(),
            symbol:    String::new(),
            ty,
            params:    Vec::new(),
            ret,
            body:      None,
        }))
    }

    fn strukt(&mut self, name: &str) -> TTIRItemId {
        self.item(TTIRItemKind::Struct {
            vis:    TIRVis::Pub,
            attrs:  TIRAttrs::default(),
            name:   name.to_string(),
            fields: Vec::new(),
        })
    }

    // The symbol of the fn at `id`, with the program's roots as given.
    fn symbol_of(&mut self, id: TTIRItemId, roots: Vec<TTIRItemId>) -> String {
        self.p.roots = roots;
        let m = Mangler::new(&self.p);
        let TTIRItemKind::Fn(f) = &self.p.items[id].kind else { panic!("not a fn") };
        m.symbol(f, id, &self.p)
    }

    fn spell_of(&mut self, ty: TyId, roots: Vec<TTIRItemId>) -> String {
        self.p.roots = roots;
        Mangler::new(&self.p).spell(ty, &self.p)
    }
}

fn attrs(symbol: Option<&str>) -> TIRFnAttrs {
    TIRFnAttrs {
        common:   TIRAttrs::default(),
        symbol:   symbol.map(str::to_string),
        must_use: false,
        inline:   TIRInline::Unwritten,
        is_test:  false,
    }
}

// The one the prose spells out: `add` of two i32 is `3add3i323i32`. Each part
// is its length and then its characters, and the return type is not a part --
// nothing tells two fns apart by what they give back.
#[test]
fn the_example_the_prose_gives() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let add = s.func("add", vec![i32, i32]);
    assert_eq!(s.symbol_of(add, vec![add]), "3add3i323i32");
}

// The length is what makes it unambiguous, so nothing is escaped: an `_` in a
// name is a character like any other, and two names that would run together
// under a separator do not run together under a length.
#[test]
fn nothing_has_to_be_escaped() {
    let mut s = Suite::new();
    let f = s.func("my_fn_2", Vec::new());
    assert_eq!(s.symbol_of(f, vec![f]), "7my_fn_2");

    // `ab` then `c` and `a` then `bc` are four characters either way, and the
    // two symbols still differ.
    let mut s = Suite::new();
    let one = s.func("ab", Vec::new());
    let two = s.func("a", Vec::new());
    assert_eq!(s.symbol_of(one, vec![one]), "2ab");
    assert_eq!(s.symbol_of(two, vec![two]), "1a");
}

// Two fns that share a name are told apart by what they take.
#[test]
fn a_shared_name_is_told_apart_by_the_parameters() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let str = s.prim(TIRPrim::Str);
    let a = s.func("show", vec![i32]);
    let b = s.func("show", vec![str]);
    let c = s.func("show", vec![i32, i32]);
    let roots = vec![a, b, c];
    assert_eq!(s.symbol_of(a, roots.clone()), "4show3i32");
    assert_eq!(s.symbol_of(b, roots.clone()), "4show3str");
    assert_eq!(s.symbol_of(c, roots), "4show3i323i32");
}

// `%symbol("malloc")` is the exact name and not a part of one: nothing outside
// the language can predict a mangling, which is why a call out to C wants this.
#[test]
fn a_symbol_attribute_is_the_whole_name() {
    let mut s = Suite::new();
    let u64 = s.prim(TIRPrim::U64);
    let f = s.func("malloc", vec![u64]);
    let TTIRItemKind::Fn(held) = &mut s.p.items[f].kind else { panic!() };
    held.attrs = attrs(Some("malloc"));
    assert_eq!(s.symbol_of(f, vec![f]), "malloc");
}

// A namespace nests a module inside the one it is written in, so its name is a
// segment like any other -- and one fn in two namespaces is two symbols.
#[test]
fn a_namespace_is_a_segment() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let inner = s.func("area", vec![i32]);
    let ns = s.item(TTIRItemKind::Namespace {
        vis:   TIRVis::Pub,
        attrs: TIRAttrs::default(),
        name:  "shapes".to_string(),
        items: vec![inner],
    });
    assert_eq!(s.symbol_of(inner, vec![ns]), "6shapes4area3i32");
}

#[test]
fn namespaces_nest() {
    let mut s = Suite::new();
    let f = s.func("go", Vec::new());
    let inner = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "b".to_string(), items: vec![f],
    });
    let outer = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "a".to_string(), items: vec![inner],
    });
    assert_eq!(s.symbol_of(f, vec![outer]), "1a1b2go");
}

// A method's segments are the impl it is written in. `impl Buf` and
// `impl Show for Buf` may both hold a `len`, and only the trait tells them
// apart -- so the trait is a segment where there is one.
#[test]
fn a_method_is_named_by_the_impl_it_is_in() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new() });

    let bare = s.func("len", Vec::new());
    let imp = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: None, members: vec![bare],
    });

    let shown = s.func("len", Vec::new());
    let show = s.item(TTIRItemKind::Trait {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "Show".to_string(), members: Vec::new(),
    });
    let for_show = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: Some(show), members: vec![shown],
    });

    let roots = vec![buf, imp, show, for_show];
    assert_eq!(s.symbol_of(bare, roots.clone()), "3Buf3len");
    assert_eq!(s.symbol_of(shown, roots.clone()), "3Buf4Show3len");
    // The two differ, which is the whole point of the trait being there.
    assert_ne!(s.symbol_of(bare, roots.clone()), s.symbol_of(shown, roots));
}

// ---- Spelling a type ------------------------------------------------------

#[test]
fn every_type_has_a_spelling() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let u8 = s.prim(TIRPrim::U8);
    let str = s.prim(TIRPrim::Str);
    let null = s.prim(TIRPrim::Null);

    let cases: Vec<(Ty, &str)> = vec![
        (Ty::Prim(TIRPrim::Never), "never"),
        (Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: i32 }, "&i32"),
        (Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: i32 }, "*i32"),
        (Ty::Ptr(u8), "ptr u8"),
        (Ty::GC(str), "gc str"),
        (Ty::Array { elem: i32, len: 8 }, "i32[8]"),
        (Ty::Run(i32), "i32[]"),
        (Ty::Tuple(vec![i32, str]), "(i32,str)"),
        (Ty::Fn { params: vec![i32], ret: null, is_unsafe: false }, "fn(i32):null"),
        (Ty::Fn { params: vec![i32], ret: null, is_unsafe: true }, "unsafe fn(i32):null"),
        // By its place and not its name: `f<T>` and `f<U>` are one function
        // written twice, and a caller cannot tell them apart either.
        (Ty::Param { name: "T".to_string(), index: 0 }, "$0"),
    ];
    for (ty, want) in cases {
        let id = s.ty(ty.clone());
        assert_eq!(s.spell_of(id, Vec::new()), want, "{:?}", ty);
    }
}

// A named type is spelled where it was declared, so two modules may each hold
// a `Point` and the two are not one symbol.
#[test]
fn a_named_type_carries_where_it_was_declared() {
    let mut s = Suite::new();
    let bare = s.strukt("Point");
    let nested = s.strukt("Point");
    let ns = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "shapes".to_string(), items: vec![nested],
    });
    let a = s.ty(Ty::Named { item: bare, args: Vec::new() });
    let b = s.ty(Ty::Named { item: nested, args: Vec::new() });
    let roots = vec![bare, ns];
    assert_eq!(s.spell_of(a, roots.clone()), "Point");
    assert_eq!(s.spell_of(b, roots), "shapes::Point");
}

// The arguments are the type's and not the declaration's, so `Vec<i32>` and
// `Vec<str>` are two spellings of one struct -- and two symbols.
#[test]
fn a_generic_type_carries_its_arguments() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let str = s.prim(TIRPrim::Str);
    let vec = s.strukt("Vec");
    let map = s.strukt("Map");

    let of_i32 = s.ty(Ty::Named { item: vec, args: vec![i32] });
    let nested = s.ty(Ty::Named { item: map, args: vec![str, of_i32] });
    let roots = vec![vec, map];
    assert_eq!(s.spell_of(of_i32, roots.clone()), "Vec<i32>");
    assert_eq!(s.spell_of(nested, roots.clone()), "Map<str,Vec<i32>>");

    // And in a symbol it is one part, however many characters it runs to.
    let f = s.func("take", vec![nested]);
    let mut roots = roots;
    roots.push(f);
    assert_eq!(s.symbol_of(f, roots), "4take17Map<str,Vec<i32>>");
}

// A `%symbol` name is handed over exactly, so it is what the linker sees --
// which is what makes a symbol the mangler could not have produced reachable.
#[test]
fn a_mangled_name_and_a_given_one_do_not_collide() {
    let mut s = Suite::new();
    let f = s.func("malloc", Vec::new());
    let mangled = s.symbol_of(f, vec![f]);
    assert_eq!(mangled, "6malloc");
    assert_ne!(mangled, "malloc");
}
