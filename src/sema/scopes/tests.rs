// What a program's scopes hold. The TTIR is built by hand, `sema` being the
// pass that would build one from source and not written.

use super::*;
use crate::tir::tir_nodes::{TIRAttrs, TIRFnAttrs, TIRInline, TIRIntro, TIRPrim, TIRVis};
use crate::tir::ttir_nodes::*;

struct Suite {
    p: TTIRProgram,
}

impl Suite {
    fn new() -> Suite {
        let mut p = TTIRProgram::default();
        p.types.push(Ty::Prim(TIRPrim::I32));
        p.types.push(Ty::Prim(TIRPrim::Null));
        p.types.push(Ty::Prim(TIRPrim::F64));
        Suite { p }
    }

    const I32: TyId = 0;
    const NULL: TyId = 1;
    const F64: TyId = 2;

    fn item(&mut self, kind: TTIRItemKind) -> TTIRItemId {
        self.p.items.push(TTIRItem { kind, line: 1, col: 1 });
        self.p.items.len() - 1
    }

    fn ty(&mut self, ty: Ty) -> TyId {
        if let Some(i) = self.p.types.iter().position(|held| *held == ty) {
            return i;
        }
        self.p.types.push(ty);
        self.p.types.len() - 1
    }

    fn expr(&mut self, kind: TTIRExprKind) -> TTIRExprId {
        self.p.exprs.push(TTIRExpr { kind, ty: Self::NULL, line: 1, col: 1 });
        self.p.exprs.len() - 1
    }

    // A body holding `locals` and the statements given.
    fn body(&mut self, locals: Vec<(&str, TyId, TIRIntro)>, stmts: Vec<TTIRStmt>) -> TTIRBodyId {
        let value = self.expr(TTIRExprKind::Block { stmts, tail: None });
        self.p.bodies.push(TTIRBody {
            locals: locals
                .into_iter()
                .map(|(name, ty, intro)| TTIRLocal {
                    name: TIRBinding::Name(name.to_string()),
                    ty,
                    intro,
                })
                .collect(),
            value,
        });
        self.p.bodies.len() - 1
    }

    fn func(&mut self, name: &str, params: Vec<TyId>, body: Option<TTIRBodyId>) -> TTIRItemId {
        let ty = self.ty(Ty::Fn { params, ret: Self::NULL, is_unsafe: false });
        let slots = body.map(|b| (0..self.p.bodies[b].locals.len()).collect()).unwrap_or_default();
        self.item(TTIRItemKind::Fn(TTIRFn {
            vis:       TIRVis::Pub,
            attrs:     TIRFnAttrs {
                common:   TIRAttrs::default(),
                symbol:   None,
                must_use: false,
                inline:   TIRInline::Unwritten,
                is_test:  false,
            },
            is_const:  false,
            is_unsafe: false,
            name:      name.to_string(),
            symbol:    String::new(),
            generics:  Vec::new(),
            ty,
            params:    slots,
            ret:       Self::NULL,
            body,
        }))
    }

    fn strukt(&mut self, name: &str) -> TTIRItemId {
        self.item(TTIRItemKind::Struct {
            generics: Vec::new(),
            vis: TIRVis::Pub, attrs: TIRAttrs::default(),
            name: name.to_string(), fields: Vec::new(),
        })
    }

    fn global(&mut self, name: &str, intro: TIRIntro) -> TTIRItemId {
        self.item(TTIRItemKind::Global {
            vis: TIRVis::Pub, attrs: TIRAttrs::default(), intro,
            name: TIRBinding::Name(name.to_string()), ty: Self::I32, init: None,
        })
    }
}

// The names one scope holds, for reading back.
fn names(s: &Scopes, at: ScopeId) -> Vec<String> {
    s.sorted(at).into_iter().map(|(n, _)| n.clone()).collect()
}

// A file is the outermost scope, and what it declares stands in it.
#[test]
fn the_module_scope_holds_what_the_file_declares() {
    let mut s = Suite::new();
    let f = s.func("main", Vec::new(), None);
    let p = s.strukt("Point");
    let g = s.global("count", TIRIntro::Var);
    s.p.roots = vec![f, p, g];

    let scopes = Scopes::of(&s.p, &["shapes".to_string()]);
    let root = scopes.root();
    assert_eq!(scopes.kind(root), ScopeKind::Module);
    assert_eq!(names(&scopes, root), vec!["Point", "count", "main"]);
    // And each carries the way to its own entry in the symbol table.
    let found = scopes.look_up(root, "Point");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].symbol.as_deref(), Some("__S6shapes5Point"));
}

// Two fns of one name are two answers to one question: they are told apart by
// what they take, which is a fact about the entries and not about the scope.
#[test]
fn one_name_may_hold_several_declarations() {
    let mut s = Suite::new();
    let a = s.func("add", vec![Suite::I32, Suite::I32], None);
    let b = s.func("add", vec![Suite::F64, Suite::F64], None);
    s.p.roots = vec![a, b];

    let scopes = Scopes::of(&s.p, &[]);
    let found = scopes.look_up(scopes.root(), "add");
    assert_eq!(found.len(), 2);
    let mut symbols: Vec<&str> = found.iter().filter_map(|e| e.symbol.as_deref()).collect();
    symbols.sort();
    assert_eq!(symbols, vec!["__F3add3f643f64", "__F3add3i323i32"]);
}

// A fn is a scope, and its parameters and every slot of its body stand in it.
// A block opens none: the TTIR has settled which slot a name means already.
#[test]
fn a_fn_holds_its_parameters_and_its_slots() {
    let mut s = Suite::new();
    let body = s.body(
        vec![
            ("n", Suite::I32, TIRIntro::Let),
            ("total", Suite::I32, TIRIntro::Var),
        ],
        Vec::new(),
    );
    let f = s.func("sum", vec![Suite::I32], Some(body));
    s.p.roots = vec![f];

    let scopes = Scopes::of(&s.p, &[]);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(scopes.kind(inner), ScopeKind::Function);
    assert_eq!(names(&scopes, inner), vec!["n", "total"]);
    // `var` is the half of the pair that may be assigned again.
    assert!(matches!(
        scopes.look_up(inner, "total")[0].info,
        Info::Variable { is_mut: true, .. }
    ));
    // A local is not a thing the linker names.
    assert!(scopes.look_up(inner, "n")[0].symbol.is_none());
}

// Looked for from the inside out: the innermost scope that has the name
// answers, and the ones around it are not asked.
#[test]
fn a_local_hides_a_global_of_the_same_name() {
    let mut s = Suite::new();
    let body = s.body(vec![("count", Suite::I32, TIRIntro::Let)], Vec::new());
    let f = s.func("go", Vec::new(), Some(body));
    let g = s.global("count", TIRIntro::Var);
    s.p.roots = vec![g, f];

    let scopes = Scopes::of(&s.p, &[]);
    let root = scopes.root();
    let inner = scopes.opened_by(f).expect("a fn opens a scope");

    // The global says `var` and has a symbol; the local says neither.
    assert!(matches!(
        scopes.look_up(root, "count")[0].info,
        Info::Variable { is_mut: true, .. }
    ));
    assert!(scopes.look_up(root, "count")[0].symbol.is_some());
    assert!(scopes.look_up(inner, "count")[0].symbol.is_none());
    // The one it hid is still there to be found where it was written.
    assert_eq!(scopes.here(inner, "count").len(), 1);
    assert_eq!(scopes.here(root, "count").len(), 1);
}

// What is not in the innermost scope is looked for in the one around it.
#[test]
fn a_name_is_found_in_the_scope_around() {
    let mut s = Suite::new();
    let body = s.body(vec![("n", Suite::I32, TIRIntro::Let)], Vec::new());
    let f = s.func("go", Vec::new(), Some(body));
    let p = s.strukt("Point");
    s.p.roots = vec![p, f];

    let scopes = Scopes::of(&s.p, &[]);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(scopes.look_up(inner, "Point").len(), 1);
    assert!(scopes.here(inner, "Point").is_empty());
    assert!(scopes.look_up(inner, "nothing").is_empty());
}

// A namespace nests a module inside the one it is written in, so what it holds
// is its own and not the module's.
#[test]
fn a_namespace_is_a_scope_of_its_own() {
    let mut s = Suite::new();
    let max = s.item(TTIRItemKind::Const {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "MAX".to_string(), ty: Suite::I32, value: 0,
    });
    let ns = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "limits".to_string(), items: vec![max],
    });
    s.p.roots = vec![ns];

    let scopes = Scopes::of(&s.p, &[]);
    let root = scopes.root();
    let inner = scopes.opened_by(ns).expect("a namespace opens a scope");
    assert_eq!(scopes.kind(inner), ScopeKind::Namespace);
    // The namespace's name is in the module; what is inside it is not.
    assert_eq!(names(&scopes, root), vec!["limits"]);
    assert_eq!(names(&scopes, inner), vec!["MAX"]);
    assert!(scopes.look_up(root, "MAX").is_empty());
    // And from inside, the module around it still answers.
    assert_eq!(scopes.look_up(inner, "limits").len(), 1);
}

// An impl declares no name of its own and its members are reached through the
// type, so they stand in a scope of the impl's and not in the module's.
#[test]
fn an_impl_holds_its_methods_and_declares_no_name() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new() });
    let len = s.func("len", Vec::new(), None);
    let imp = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: None, members: vec![len],
    });
    s.p.roots = vec![buf, imp];

    let scopes = Scopes::of(&s.p, &[]);
    let root = scopes.root();
    let inner = scopes.opened_by(imp).expect("an impl opens a scope");
    assert_eq!(scopes.kind(inner), ScopeKind::Impl);
    assert_eq!(names(&scopes, root), vec!["Buf"]);
    assert_eq!(names(&scopes, inner), vec!["len"]);
}

// A declaration written in a block is a declaration like any other: it stands
// in the fn's scope, since the block opens none, and it is named after the fn
// it was written in.
#[test]
fn a_declaration_in_a_body_stands_in_the_fn_that_holds_it() {
    let mut s = Suite::new();
    let helper = s.func("helper", vec![Suite::I32], None);
    let value = s.expr(TTIRExprKind::Block {
        stmts: vec![TTIRStmt::Item(helper)],
        tail:  None,
    });
    s.p.bodies.push(TTIRBody { locals: Vec::new(), value });
    let body = s.p.bodies.len() - 1;
    let outer = s.func("outer", Vec::new(), Some(body));
    s.p.roots = vec![outer];

    let scopes = Scopes::of(&s.p, &["shapes".to_string()]);
    let root = scopes.root();
    let inner = scopes.opened_by(outer).expect("a fn opens a scope");
    assert_eq!(names(&scopes, root), vec!["outer"]);
    assert_eq!(names(&scopes, inner), vec!["helper"]);
    // Named after the fn it is in, the way a method is named after its impl.
    assert_eq!(
        scopes.look_up(inner, "helper")[0].symbol.as_deref(),
        Some("__F6shapes5outer6helper3i32")
    );
}

// A scope may be built by hand as well as walked out of a program: the pass
// that brings imported names in has nowhere else to put them.
#[test]
fn a_scope_can_be_added_to_by_hand() {
    let mut scopes = Scopes::new();
    let root = scopes.root();
    scopes.bind(
        root,
        "circle".to_string(),
        Entry {
            info:   Info::Function {
                generics:  Vec::new(),
                params:    Vec::new(),
                ret:       None,
                is_const:  false,
                is_unsafe: false,
            },
            symbol: Some("__F6shapes6circle".to_string()),
            line:   1,
            col:    1,
        },
    );
    assert_eq!(scopes.look_up(root, "circle").len(), 1);
    assert_eq!(scopes.len(), 1);
}

// ---- Generic parameters ---------------------------------------------------

// A parameter names a type without being one, and it is a name in the scope its
// declaration opened -- which is what lets the `T` of a signature be looked up
// like anything else.
#[test]
fn a_fn_holds_its_generic_parameters() {
    let mut s = Suite::new();
    let ord = s.strukt("Ord");
    let ord_ty = s.ty(Ty::Named { item: ord, args: Vec::new() });
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 1 });
    let body = s.body(vec![("x", t, TIRIntro::Let)], Vec::new());
    let f = s.func("first", vec![t], Some(body));
    let TTIRItemKind::Fn(held) = &mut s.p.items[f].kind else { panic!() };
    held.generics = vec![
        TTIRGeneric::Life { name: "a".to_string(), region: 0, bounds: vec![1] },
        TTIRGeneric::Type { name: "T".to_string(), bounds: vec![ord_ty] },
    ];
    s.p.roots = vec![ord, f];

    let scopes = Scopes::of(&s.p, &[]);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(names(&scopes, inner), vec!["T", "a", "x"]);

    // Its place in the list is what `Ty::Param` names it by, so a `T` found
    // here and a `T` standing in the signature are known to be the same one.
    let Info::TypeParam { index, bounds } = &scopes.look_up(inner, "T")[0].info else {
        panic!("{:?}", scopes.look_up(inner, "T"))
    };
    assert_eq!(*index, 1);
    assert_eq!(bounds, &vec![ord_ty]);

    // A lifetime is a name in a scope too, which is what a `'a: 'b` needs.
    let Info::Lifetime { region, bounds, .. } = &scopes.look_up(inner, "a")[0].info else {
        panic!()
    };
    assert_eq!(*region, 0);
    assert_eq!(bounds, &vec![1]);

    // Neither is a thing the linker names.
    assert!(scopes.look_up(inner, "T")[0].symbol.is_none());
}

// A struct and an enum hold no name that is looked up, and both take generic
// parameters -- so each opens a scope holding nothing else.
#[test]
fn a_struct_and_an_enum_hold_their_parameters() {
    let mut s = Suite::new();
    let st = s.strukt("Stack");
    let TTIRItemKind::Struct { generics, .. } = &mut s.p.items[st].kind else { panic!() };
    *generics = vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }];

    let en = s.item(TTIRItemKind::Enum {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: vec![TTIRGeneric::Type { name: "E".to_string(), bounds: Vec::new() }],
        name: "Maybe".to_string(), variants: Vec::new(),
    });
    s.p.roots = vec![st, en];

    let scopes = Scopes::of(&s.p, &[]);
    assert_eq!(names(&scopes, scopes.root()), vec!["Maybe", "Stack"]);
    let inside_st = scopes.opened_by(st).expect("a struct opens a scope");
    let inside_en = scopes.opened_by(en).expect("an enum opens a scope");
    assert_eq!(scopes.kind(inside_st), ScopeKind::Struct);
    assert_eq!(scopes.kind(inside_en), ScopeKind::Enum);
    assert_eq!(names(&scopes, inside_st), vec!["T"]);
    assert_eq!(names(&scopes, inside_en), vec!["E"]);
    // And neither leaks into the module around it.
    assert!(scopes.look_up(scopes.root(), "T").is_empty());
}

// An impl's parameters are every method's: the `T` of `impl<T> Stack<T>` stands
// in each of their signatures, so a method finds it in the scope around.
#[test]
fn an_impls_parameters_reach_its_methods() {
    let mut s = Suite::new();
    let stack = s.strukt("Stack");
    let stack_ty = s.ty(Ty::Named { item: stack, args: Vec::new() });
    let push = s.func("push", Vec::new(), None);
    let imp = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        ty: stack_ty, of: None, members: vec![push],
    });
    s.p.roots = vec![stack, imp];

    let scopes = Scopes::of(&s.p, &[]);
    let inside_impl = scopes.opened_by(imp).expect("an impl opens a scope");
    let inside_fn = scopes.opened_by(push).expect("a fn opens a scope");
    assert_eq!(names(&scopes, inside_impl), vec!["T", "push"]);
    // The method has none of its own and finds the impl's from where it stands.
    assert!(scopes.here(inside_fn, "T").is_empty());
    assert_eq!(scopes.look_up(inside_fn, "T").len(), 1);
}

// A parameter of the fn hides one of the impl, as any inner name hides an
// outer one -- and whether that should be *written* is the checker's rule.
#[test]
fn a_fns_parameter_hides_the_impls() {
    let mut s = Suite::new();
    let buf = s.strukt("Buf");
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new() });
    let m = s.func("take", Vec::new(), None);
    let TTIRItemKind::Fn(held) = &mut s.p.items[m].kind else { panic!() };
    held.generics = vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }];
    let imp = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        ty: buf_ty, of: None, members: vec![m],
    });
    s.p.roots = vec![buf, imp];

    let scopes = Scopes::of(&s.p, &[]);
    let inside_fn = scopes.opened_by(m).expect("a fn opens a scope");
    assert_eq!(scopes.here(inside_fn, "T").len(), 1);
    assert_eq!(scopes.look_up(inside_fn, "T").len(), 1);
    // Both are there, each where it was written.
    let inside_impl = scopes.opened_by(imp).expect("an impl opens a scope");
    assert_eq!(scopes.here(inside_impl, "T").len(), 1);
}
