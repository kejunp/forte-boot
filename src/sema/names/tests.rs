// What a fn is compiled to. The TTIR is built by hand here for the reason
// `cfg::fixture` builds one by hand: `sema` is what would produce a TTIR from
// source, and it is not written.

use super::*;
use crate::tir::tir_nodes::{TIRAttrs, TIRFnAttrs, TIRInline};
use crate::tir::ttir_nodes::{TTIRItem, TTIRModule, TTIRProgram};

// A program under construction, with the handful of types a symbol names.
struct Suite {
    p: TTIRProgram,
    // The file these declarations stand in; empty unless a test says.
    module: Vec<String>,
}

impl Suite {
    fn new() -> Suite {
        Suite { p: TTIRProgram::default(), module: Vec::new() }
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
            generics:  Vec::new(),
            wheres:    Vec::new(),
            ty,
            params:    Vec::new(),
            ret,
            body:      None,
        }))
    }

    fn strukt(&mut self, name: &str) -> TTIRItemId {
        self.item(TTIRItemKind::Struct {
            generics: Vec::new(),
            wheres: Vec::new(),
            vis:    TIRVis::Pub,
            attrs:  TIRAttrs::default(),
            name:   name.to_string(),
            fields: Vec::new(),
        })
    }

    // The symbol of the fn at `id`, with the program's roots as given.
    fn symbol_of(&mut self, id: TTIRItemId, roots: Vec<TTIRItemId>) -> String {
        let module = self.module.clone();
        self.p.modules = vec![TTIRModule { path: module, roots: roots }];
        let m = Mangler::new(&self.p);
        let TTIRItemKind::Fn(f) = &self.p.items[id].kind else { panic!("not a fn") };
        m.symbol(f, id, &self.p)
    }

    fn spell_of(&mut self, ty: TyId, roots: Vec<TTIRItemId>) -> String {
        let module = self.module.clone();
        self.p.modules = vec![TTIRModule { path: module, roots: roots }];
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

// The one the prose spells out: `add` of two i32 is `__F3add3i323i32`. Each
// part is its length and then its characters, and the return type is not a
// part -- nothing tells two fns apart by what they give back.
#[test]
fn the_example_the_prose_gives() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let add = s.func("add", vec![i32, i32]);
    assert_eq!(s.symbol_of(add, vec![add]), "__F3add3i323i32");
}

// The whole of the format in one name: the prefix, where it is declared, its
// own name, and one part for each parameter. `foo` in the namespace
// `namespaces`, of an i32 and a `mytype`.
#[test]
fn the_whole_format_in_one_name() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let mytype = s.strukt("mytype");
    let mytype_ty = s.ty(Ty::Named { item: mytype, args: Vec::new() });
    let foo = s.func("foo", vec![i32, mytype_ty]);
    let ns = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "namespaces".to_string(), items: vec![foo],
    });
    assert_eq!(
        s.symbol_of(foo, vec![mytype, ns]),
        "__F10namespaces3foo3i326mytype"
    );
}

// The length is what makes it unambiguous, so nothing is escaped: an `_` in a
// name is a character like any other, and two names that would run together
// under a separator do not run together under a length.
#[test]
fn nothing_has_to_be_escaped() {
    let mut s = Suite::new();
    let f = s.func("my_fn_2", Vec::new());
    assert_eq!(s.symbol_of(f, vec![f]), "__F7my_fn_2");

    // `ab` then `c` and `a` then `bc` are four characters either way, and the
    // two symbols still differ.
    let mut s = Suite::new();
    let one = s.func("ab", Vec::new());
    let two = s.func("a", Vec::new());
    assert_eq!(s.symbol_of(one, vec![one]), "__F2ab");
    assert_eq!(s.symbol_of(two, vec![two]), "__F1a");
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
    assert_eq!(s.symbol_of(a, roots.clone()), "__F4show3i32");
    assert_eq!(s.symbol_of(b, roots.clone()), "__F4show3str");
    assert_eq!(s.symbol_of(c, roots), "__F4show3i323i32");
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
    assert_eq!(s.symbol_of(inner, vec![ns]), "__F6shapes4area3i32");
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
    assert_eq!(s.symbol_of(f, vec![outer]), "__F1a1b2go");
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
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: None, members: vec![bare],
    });

    let shown = s.func("len", Vec::new());
    let show = s.item(TTIRItemKind::Trait {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "Show".to_string(), members: Vec::new(),
    });
    let for_show = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: Some(show), members: vec![shown],
    });

    let roots = vec![buf, imp, show, for_show];
    assert_eq!(s.symbol_of(bare, roots.clone()), "__F3Buf3len");
    assert_eq!(s.symbol_of(shown, roots.clone()), "__F3Buf4Show3len");
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
    assert_eq!(s.symbol_of(f, roots), "__F4take17Map<str,Vec<i32>>");
}

// A `%symbol` name is handed over exactly, so it is what the linker sees --
// which is what makes a symbol the mangler could not have produced reachable.
#[test]
fn a_mangled_name_and_a_given_one_do_not_collide() {
    let mut s = Suite::new();
    let f = s.func("malloc", Vec::new());
    let mangled = s.symbol_of(f, vec![f]);
    assert_eq!(mangled, "__F6malloc");
    assert_ne!(mangled, "malloc");
}

// A file is a module, so it is a segment like a namespace. Two files each
// holding an `area` are two symbols, which is what the segment is for.
#[test]
fn a_file_is_a_segment_like_a_namespace() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);
    let area = s.func("area", vec![i32]);
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![area] }];

    // The same declaration, read as one file and then as another.
    let mut symbols = Vec::new();
    for file in ["shapes", "boxes"] {
        s.p.modules = vec![TTIRModule { path: vec![file.to_string()], roots: vec![area] }];
        let m = Mangler::new(&s.p);
        let TTIRItemKind::Fn(f) = &s.p.items[area].kind else { panic!() };
        symbols.push(m.symbol(f, area, &s.p));
    }
    assert_eq!(symbols, vec!["__F6shapes4area3i32", "__F5boxes4area3i32"]);
}

// A file in a directory is a module inside a module, so its segments nest the
// way a namespace's do -- and a namespace inside it goes on the end.
#[test]
fn a_nested_file_and_a_namespace_are_one_run_of_segments() {
    let mut s = Suite::new();
    let clamp = s.func("clamp", Vec::new());
    let ns = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "limits".to_string(), items: vec![clamp],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![ns] }];
    s.p.modules[0].path = vec!["a".to_string(), "b".to_string(), "deep".to_string()];
    let m = Mangler::new(&s.p);
    let TTIRItemKind::Fn(f) = &s.p.items[clamp].kind else { panic!() };
    assert_eq!(m.symbol(f, clamp, &s.p), "__F1a1b4deep6limits5clamp");
}

// ---- The symbol table -----------------------------------------------------

// Everything a program declares, by the name the linker sees. Keyed by the
// symbol and not by the name for the reason mangling exists: two `add`s are
// two entries and one word in the source.
#[test]
fn the_table_is_keyed_by_symbol() {
    let mut s = Suite::new();
    s.module = vec!["shapes".to_string()];
    let i32 = s.prim(TIRPrim::I32);
    let f64 = s.prim(TIRPrim::F64);
    let addi = s.func("add", vec![i32, i32]);
    let addf = s.func("add", vec![f64, f64]);
    let point = s.strukt("Point");
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![addi, addf, point] }];

    let table = SymbolTable::of(&s.p);
    let keys: Vec<&String> = table.sorted().into_iter().map(|(k, _)| k).collect();
    assert_eq!(
        keys,
        vec![
            "__F6shapes3add3f643f64",
            "__F6shapes3add3i323i32",
            "__S6shapes5Point",
        ]
    );
    assert!(table.clashes().is_empty());

    // The entry is what the name turned out to be.
    let Some(Info::Function { params, is_unsafe, .. }) =
        table.get("__F6shapes3add3i323i32")
    else {
        panic!("{:?}", table.get("__F6shapes3add3i323i32"))
    };
    assert_eq!(params.len(), 2);
    assert!(!is_unsafe);
    assert!(matches!(table.get("__S6shapes5Point"), Some(Info::Struct { .. })));
}

// A letter per kind, so a struct and a fn of one name in one module are two
// symbols rather than one entry overwriting the other.
#[test]
fn each_kind_of_declaration_gets_its_own_letter() {
    let mut s = Suite::new();
    let i32 = s.prim(TIRPrim::I32);

    let f = s.func("thing", Vec::new());
    let st = s.strukt("thing");
    let en = s.item(TTIRItemKind::Enum {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "thing".to_string(), variants: Vec::new(),
    });
    let tr = s.item(TTIRItemKind::Trait {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "thing".to_string(), members: Vec::new(),
    });
    let co = s.item(TTIRItemKind::Const {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "thing".to_string(), ty: i32, value: 0,
    });
    let gl = s.item(TTIRItemKind::Global {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), intro: TIRIntro::Var,
        name: TIRBinding::Name("thing".to_string()), ty: i32, init: None,
    });
    let ns = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "thing".to_string(), items: Vec::new(),
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![f, st, en, tr, co, gl, ns] }];

    let table = SymbolTable::of(&s.p);
    let keys: Vec<&String> = table.sorted().into_iter().map(|(k, _)| k).collect();
    assert_eq!(
        keys,
        vec!["__C5thing", "__E5thing", "__F5thing", "__G5thing",
             "__N5thing", "__S5thing", "__T5thing"]
    );
    // A `var` is the mutable half of the pair, and a `const` says so instead.
    assert!(matches!(table.get("__G5thing"), Some(Info::Variable { is_mut: true, .. })));
    assert!(matches!(table.get("__C5thing"), Some(Info::Variable { is_const: true, .. })));
}

// An impl declares no name of its own -- it is reached through the type it is
// written for -- so nothing in the table stands for one. Its members do.
#[test]
fn an_impl_is_not_in_the_table_but_its_methods_are() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new() });
    let len = s.func("len", Vec::new());
    let imp = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: None, members: vec![len],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![buf, imp] }];

    let table = SymbolTable::of(&s.p);
    let keys: Vec<&String> = table.sorted().into_iter().map(|(k, _)| k).collect();
    assert_eq!(keys, vec!["__F3Buf3len", "__S3Buf"]);
}

// The impl's segment says the type, and the segments in front already say the
// module: `impl Point` inside `shapes` is `6shapes5Point` and not
// `6shapes13shapes::Point`. A type from elsewhere keeps its path, which is what
// tells an `impl other::Buf` from an `impl Buf`.
#[test]
fn an_impl_does_not_repeat_the_module_it_is_in() {
    let mut s = Suite::new();
    s.module = vec!["shapes".to_string()];
    let here = s.strukt("Point");
    let here_ty = s.ty(Ty::Named { item: here, args: Vec::new() });
    let mine = s.func("norm", Vec::new());
    let imp = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: here_ty, of: None, members: vec![mine],
    });

    let away = s.strukt("Buf");
    let away_ty = s.ty(Ty::Named { item: away, args: Vec::new() });
    let theirs = s.func("len", Vec::new());
    let imp2 = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: away_ty, of: None, members: vec![theirs],
    });
    let other = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "other".to_string(), items: vec![away],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![here, imp, other, imp2] }];

    let m = Mangler::new(&s.p);
    assert_eq!(m.symbol_of(mine, &s.p).as_deref(), Some("__F6shapes5Point4norm"));
    assert_eq!(
        m.symbol_of(theirs, &s.p).as_deref(),
        Some("__F6shapes10other::Buf3len")
    );
}

// An alias is a name in a scope and nothing to compile, so it gets no letter
// and stands in no symbol table -- while a struct of the same name does.
#[test]
fn a_type_alias_is_not_a_symbol() {
    let mut s = Suite::new();
    s.module = vec!["shapes".to_string()];
    let i32 = s.prim(TIRPrim::I32);
    let alias = s.item(TTIRItemKind::TypeAlias {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "Count".to_string(), generics: Vec::new(), wheres: Vec::new(), ty: i32,
    });
    let point = s.strukt("Count");
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![alias, point] }];

    let table = SymbolTable::of(&s.p);
    let keys: Vec<&String> = table.sorted().into_iter().map(|(k, _)| k).collect();
    assert_eq!(keys, vec!["__S6shapes5Count"]);
}
