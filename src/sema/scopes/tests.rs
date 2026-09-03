// What a program's scopes hold. The TTIR is built by hand, `sema` being the
// pass that builds one from source, which these do not go through.

use super::*;
use crate::sema::names::{Access, Payload};
use crate::tir::tir_nodes::{
    TIRFnUses,TIRAttrs, TIRFnAttrs, TIRInline, TIRIntro, TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::*;

struct Suite {
    p: TTIRProgram,
    // The file these declarations stand in; empty unless a test says.
    module: Vec<String>,
}

impl Suite {
    fn new() -> Suite {
        let mut p = TTIRProgram::default();
        p.types.push(Ty::Prim(TIRPrim::I32));
        p.types.push(Ty::Prim(TIRPrim::Null));
        p.types.push(Ty::Prim(TIRPrim::F64));
        Suite { p, module: Vec::new() }
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
                    line: 1,
                    col: 1,
                })
                .collect(),
            value,
        });
        self.p.bodies.len() - 1
    }

    fn func(&mut self, name: &str, params: Vec<TyId>, body: Option<TTIRBodyId>) -> TTIRItemId {
        let ty = self.ty(Ty::Fn { uses: TIRFnUses::Reads, params, ret: Self::NULL, is_unsafe: false });
        // Every slot of the body stands for a parameter here, which is enough
        // for what these tests ask; a real fn names its own.
        let slots: Vec<TTIRParam> = body
            .map(|b| {
                self.p.bodies[b]
                    .locals
                    .iter()
                    .enumerate()
                    .map(|(i, local)| TTIRParam { name: local.name.clone(), slot: Some(i) })
                    .collect()
            })
            .unwrap_or_default();
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
            generics:  Vec::new(),
            wheres:    Vec::new(),
            ty,
            params:    slots,
            ret:       Self::NULL,
            outlives:  Vec::new(),
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

// The one file's scope. `root()` is the suite, which holds no names of its own
// -- there is nothing above a suite to name.
fn module_scope(s: &Scopes) -> ScopeId {
    s.modules().next().expect("a module").1
}

// The names one scope holds, for reading back.
fn names(s: &Scopes, at: ScopeId) -> Vec<String> {
    s.sorted(at).into_iter().map(|(n, _)| n.clone()).collect()
}

// A file is the outermost scope, and what it declares stands in it.
#[test]
fn the_module_scope_holds_what_the_file_declares() {
    let mut s = Suite::new();
    s.module = vec!["shapes".to_string()];
    let f = s.func("main", Vec::new(), None);
    let p = s.strukt("Point");
    let g = s.global("count", TIRIntro::Var);
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![f, p, g] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![a, b] }];

    let scopes = Scopes::of(&s.p);
    let found = scopes.look_up(module_scope(&scopes), "add");
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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![f] }];

    let scopes = Scopes::of(&s.p);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(scopes.kind(inner), ScopeKind::Function);
    assert_eq!(names(&scopes, inner), vec!["n", "total"]);
    // `var` is the half of the pair that may be assigned again.
    assert!(matches!(
        scopes.look_up(inner, "total")[0].info,
        Info::Variable { access: Access { is_mut: true, .. }, .. }
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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![g, f] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");

    // The global says `var` and has a symbol; the local says neither.
    assert!(matches!(
        scopes.look_up(root, "count")[0].info,
        Info::Variable { access: Access { is_mut: true, .. }, .. }
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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![p, f] }];

    let scopes = Scopes::of(&s.p);
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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![ns] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
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
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new(), regions: Vec::new() });
    let len = s.func("len", Vec::new(), None);
    let imp = s.item(TTIRItemKind::Impl {
        generics: Vec::new(),
        wheres: Vec::new(),
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        ty: buf_ty, of: None, members: vec![len],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![buf, imp] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
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
    s.module = vec!["shapes".to_string()];
    let helper = s.func("helper", vec![Suite::I32], None);
    let value = s.expr(TTIRExprKind::Block {
        stmts: vec![TTIRStmt::Item(helper)],
        tail:  None,
    });
    s.p.bodies.push(TTIRBody { locals: Vec::new(), value });
    let body = s.p.bodies.len() - 1;
    let outer = s.func("outer", Vec::new(), Some(body));
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![outer] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
    let inner = scopes.opened_by(outer).expect("a fn opens a scope");
    assert_eq!(names(&scopes, root), vec!["outer"]);
    assert_eq!(names(&scopes, inner), vec!["helper"]);
    // Named after the fn it is in, the way a method is named after its impl.
    assert_eq!(
        scopes.look_up(inner, "helper")[0].symbol.as_deref(),
        Some("__F6shapes5outer6helper3i32")
    );
}

// What a file's imports brought in stands in that file's scope, so a name
// written by hand and a name imported are looked up the same way afterwards.
// The resolver knows which module each came from; this is where that lands.
#[test]
fn an_imported_name_stands_in_the_scope_that_imported_it() {
    let mut scopes = Scopes::new();
    let root = scopes.root();
    let at = scopes.open(root, ScopeKind::Module);
    scopes.bind_imports(
        at,
        &[Binding {
            name: "circle".to_string(),
            home: std::path::PathBuf::from("shapes.ft"),
            path: vec!["circle".to_string()],
            glob: false,
            via:  0,
            line: 1,
            col:  8,
        }],
    );

    let found = scopes.look_up(at, "circle");
    assert_eq!(found.len(), 1);
    let Info::Import { home, path } = &found[0].info else { panic!("{:?}", found) };
    assert!(home.ends_with("shapes.ft"));
    assert_eq!(path, &vec!["circle".to_string()]);
    // The name here has no symbol; what it names may have one of its own.
    assert!(found[0].symbol.is_none());
    // And it is where the import was written.
    assert_eq!((found[0].line, found[0].col), (1, 8));
}

// ---- Generic parameters ---------------------------------------------------

// A parameter names a type without being one, and it is a name in the scope its
// declaration opened -- which is what lets the `T` of a signature be looked up
// like anything else.
#[test]
fn a_fn_holds_its_generic_parameters() {
    let mut s = Suite::new();
    let ord = s.strukt("Ord");
    let ord_ty = s.ty(Ty::Named { item: ord, args: Vec::new(), regions: Vec::new() });
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 1 });
    let body = s.body(vec![("x", t, TIRIntro::Let)], Vec::new());
    let f = s.func("first", vec![t], Some(body));
    let TTIRItemKind::Fn(held) = &mut s.p.items[f].kind else { panic!() };
    held.generics = vec![
        TTIRGeneric::Life { name: "a".to_string(), region: 0, bounds: vec![1] },
        // A trait and a region at once: `<T: Ord + 'a>` is both, and one list
        // holds either because one colon writes both.
        TTIRGeneric::Type {
            name:   "T".to_string(),
            bounds: vec![TTIRBound::Trait(ord_ty), TTIRBound::Life(0)],
        },
    ];
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![ord, f] }];

    let scopes = Scopes::of(&s.p);
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(names(&scopes, inner), vec!["T", "a", "x"]);

    // Its place in the list is what `Ty::Param` names it by, so a `T` found
    // here and a `T` standing in the signature are known to be the same one.
    let Info::TypeParam { index, bounds } = &scopes.look_up(inner, "T")[0].info else {
        panic!("{:?}", scopes.look_up(inner, "T"))
    };
    assert_eq!(*index, 1);
    assert_eq!(bounds, &vec![TTIRBound::Trait(ord_ty), TTIRBound::Life(0)]);

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
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![st, en] }];

    let scopes = Scopes::of(&s.p);
    assert_eq!(names(&scopes, module_scope(&scopes)), vec!["Maybe", "Stack"]);
    let inside_st = scopes.opened_by(st).expect("a struct opens a scope");
    let inside_en = scopes.opened_by(en).expect("an enum opens a scope");
    assert_eq!(scopes.kind(inside_st), ScopeKind::Struct);
    assert_eq!(scopes.kind(inside_en), ScopeKind::Enum);
    assert_eq!(names(&scopes, inside_st), vec!["T"]);
    assert_eq!(names(&scopes, inside_en), vec!["E"]);
    // And neither leaks into the module around it.
    assert!(scopes.look_up(module_scope(&scopes), "T").is_empty());
}

// An impl's parameters are every method's: the `T` of `impl<T> Stack<T>` stands
// in each of their signatures, so a method finds it in the scope around.
#[test]
fn an_impls_parameters_reach_its_methods() {
    let mut s = Suite::new();
    let stack = s.strukt("Stack");
    let stack_ty = s.ty(Ty::Named { item: stack, args: Vec::new(), regions: Vec::new() });
    let push = s.func("push", Vec::new(), None);
    let imp = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        wheres: Vec::new(),
        ty: stack_ty, of: None, members: vec![push],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![stack, imp] }];

    let scopes = Scopes::of(&s.p);
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
    let buf_ty = s.ty(Ty::Named { item: buf, args: Vec::new(), regions: Vec::new() });
    let m = s.func("take", Vec::new(), None);
    let TTIRItemKind::Fn(held) = &mut s.p.items[m].kind else { panic!() };
    held.generics = vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }];
    let imp = s.item(TTIRItemKind::Impl {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        wheres: Vec::new(),
        ty: buf_ty, of: None, members: vec![m],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![buf, imp] }];

    let scopes = Scopes::of(&s.p);
    let inside_fn = scopes.opened_by(m).expect("a fn opens a scope");
    assert_eq!(scopes.here(inside_fn, "T").len(), 1);
    assert_eq!(scopes.look_up(inside_fn, "T").len(), 1);
    // Both are there, each where it was written.
    let inside_impl = scopes.opened_by(imp).expect("an impl opens a scope");
    assert_eq!(scopes.here(inside_impl, "T").len(), 1);
}

// A `where` predicate about a parameter is folded into that parameter's
// bounds, since `fn f<T: Ord>` and `fn f<T> where T: Ord` say the same thing.
// What is left is every predicate with no parameter to fold into: one about a
// type that was built rather than declared, and one about two regions.
#[test]
fn a_where_clause_keeps_what_no_parameter_can_hold() {
    let mut s = Suite::new();
    let ord = s.strukt("Ord");
    let ord_ty = s.ty(Ty::Named { item: ord, args: Vec::new(), regions: Vec::new() });
    let show = s.strukt("Show");
    let show_ty = s.ty(Ty::Named { item: show, args: Vec::new(), regions: Vec::new() });
    let vec = s.strukt("Vec");
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 0 });
    let vec_t = s.ty(Ty::Named { item: vec, args: vec![t], regions: Vec::new() });

    let f = s.func("go", vec![t], None);
    let TTIRItemKind::Fn(held) = &mut s.p.items[f].kind else { panic!() };
    // `fn go<T: Ord>(x: T) where Vec<T>: Show, 'a: 'b`
    held.generics = vec![TTIRGeneric::Type {
        name:   "T".to_string(),
        bounds: vec![TTIRBound::Trait(ord_ty)],
    }];
    held.wheres = vec![
        TTIRWherePred {
            subject: TTIRSubject::Type(vec_t),
            bounds:  vec![TTIRBound::Trait(show_ty)],
        },
        TTIRWherePred {
            subject: TTIRSubject::Region(0),
            bounds:  vec![TTIRBound::Life(1)],
        },
    ];
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![ord, show, vec, f] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
    let Info::Function { generics, wheres, .. } = &scopes.look_up(root, "go")[0].info else {
        panic!()
    };
    // The parameter's own bound stayed where it was folded.
    assert_eq!(generics.len(), 1);
    assert!(matches!(
        &generics[0],
        TTIRGeneric::Type { bounds, .. } if bounds == &vec![TTIRBound::Trait(ord_ty)]
    ));
    // And the two with nowhere to fold are here, in the order written.
    assert_eq!(wheres.len(), 2);
    assert_eq!(wheres[0].subject, TTIRSubject::Type(vec_t));
    assert_eq!(wheres[0].bounds, vec![TTIRBound::Trait(show_ty)]);
    assert_eq!(wheres[1].subject, TTIRSubject::Region(0));
    assert_eq!(wheres[1].bounds, vec![TTIRBound::Life(1)]);

    // A `where` names nothing, so it puts nothing in the scope.
    let inner = scopes.opened_by(f).expect("a fn opens a scope");
    assert_eq!(names(&scopes, inner), vec!["T"]);
}

// ---- Type aliases ---------------------------------------------------------

// An alias makes no new type, so what it is is the type it names -- and the
// name in front of that type is what a reader wrote, so it is in scope like
// anything else. It takes parameters too, and those are its own.
#[test]
fn a_type_alias_is_a_name_for_the_type_it_follows() {
    let mut s = Suite::new();
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 0 });
    let pair = s.ty(Ty::Tuple(vec![t, t]));
    let alias = s.item(TTIRItemKind::TypeAlias {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "Pair".to_string(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        wheres: Vec::new(),
        ty: pair,
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![alias] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
    assert_eq!(names(&scopes, root), vec!["Pair"]);

    let entry = &scopes.look_up(root, "Pair")[0];
    let Info::TypeAlias { generics, ty, .. } = &entry.info else { panic!("{:?}", entry) };
    // The type it names, followed: nothing here is an alias any more.
    assert_eq!(*ty, pair);
    assert_eq!(generics.len(), 1);

    // It makes no code, so the linker never names it.
    assert!(entry.symbol.is_none());

    // Its parameter is its own, and stands in the scope it opened.
    let inner = scopes.opened_by(alias).expect("an alias opens a scope");
    assert_eq!(scopes.kind(inner), ScopeKind::TypeAlias);
    assert_eq!(names(&scopes, inner), vec!["T"]);
    assert!(scopes.look_up(root, "T").is_empty());
}

// A variant is reached through its enum -- `Color::Red` walks into the enum's
// scope exactly as `limits::MAX` walks into a namespace's. So the variants are
// the enum's own names, and `Red` on its own is not in the module around it.
#[test]
fn an_enum_holds_its_variants() {
    let mut s = Suite::new();
    let en = s.item(TTIRItemKind::Enum {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        generics: Vec::new(),
        name: "Color".to_string(),
        variants: vec![
            TTIRVariant {
                attrs: TIRAttrs::default(), name: "Red".to_string(),
                payload: TTIRPayload::None, value: 0,
            },
            TTIRVariant {
                attrs: TIRAttrs::default(), name: "Shade".to_string(),
                payload: TTIRPayload::Tuple(vec![Suite::I32]), value: 1,
            },
            TTIRVariant {
                attrs: TIRAttrs::default(), name: "Blue".to_string(),
                payload: TTIRPayload::None, value: 4,
            },
        ],
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![en] }];

    let scopes = Scopes::of(&s.p);
    let root = module_scope(&scopes);
    let inner = scopes.opened_by(en).expect("an enum opens a scope");
    assert_eq!(names(&scopes, root), vec!["Color"]);
    assert_eq!(names(&scopes, inner), vec!["Blue", "Red", "Shade"]);
    // `Red` on its own is not in the module: an import is what brings one in.
    assert!(scopes.look_up(root, "Red").is_empty());

    // Each knows the enum it belongs to, what it carries, and what it is worth.
    let Info::Variant { of, payload, value } = &scopes.look_up(inner, "Shade")[0].info else {
        panic!()
    };
    assert_eq!(of, "Color");
    assert_eq!(payload, &Payload::Tuple(vec![Suite::I32]));
    assert_eq!(*value, 1);
    // Written or counted, every variant has a value.
    let Info::Variant { value, .. } = &scopes.look_up(inner, "Blue")[0].info else { panic!() };
    assert_eq!(*value, 4);
    // And a variant is reached through its enum, which is what the linker names.
    assert!(scopes.look_up(inner, "Red")[0].symbol.is_none());
}

// A signature is declared as fully as a body is, so its parameters keep the
// names they were written with: `params` are the fn's own, not a body's slots.
#[test]
fn a_signature_keeps_its_parameter_names() {
    let mut s = Suite::new();
    let sig = s.func("show", vec![Suite::I32, Suite::F64], None);
    let TTIRItemKind::Fn(held) = &mut s.p.items[sig].kind else { panic!() };
    held.params = vec![
        TTIRParam { name: TIRBinding::Name("width".to_string()), slot: None },
        TTIRParam { name: TIRBinding::Discard, slot: None },
    ];
    assert!(held.body.is_none());
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![sig] }];

    let scopes = Scopes::of(&s.p);
    let Info::Function { params, .. } = &scopes.look_up(module_scope(&scopes), "show")[0].info else {
        panic!()
    };
    assert_eq!(params[0].0, "width");
    // `_` binds nothing on purpose, and is no name a caller may write.
    assert_eq!(params[1].0, "_");
    assert_eq!(params[0].1, Some(Suite::I32));
    assert_eq!(params[1].1, Some(Suite::F64));
}

// Every kind of thing an `Info` can be, produced by one program. The point is
// not the program: it is that no variant is left that nothing builds, which is
// what a table with an unreachable case in it always turns out to be hiding.
#[test]
fn every_kind_of_info_is_built_by_something() {
    let mut s = Suite::new();

    // A type alias, with a parameter of its own.
    let t = s.ty(Ty::Param { name: "T".to_string(), index: 0 });
    let pair = s.ty(Ty::Tuple(vec![t, t]));
    let alias = s.item(TTIRItemKind::TypeAlias {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), name: "Pair".to_string(),
        generics: vec![TTIRGeneric::Type { name: "T".to_string(), bounds: Vec::new() }],
        wheres: Vec::new(), ty: pair,
    });

    // A struct, an enum with a variant, and a trait.
    let point = s.strukt("Point");
    let color = s.item(TTIRItemKind::Enum {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), name: "Color".to_string(),
        generics: Vec::new(),
        variants: vec![TTIRVariant {
            attrs: TIRAttrs::default(), name: "Red".to_string(),
            payload: TTIRPayload::None, value: 0,
        }],
    });
    let shown = s.func("show", Vec::new(), None);
    let show = s.item(TTIRItemKind::Trait {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), name: "Show".to_string(),
        generics: Vec::new(), wheres: Vec::new(), members: vec![shown],
    });

    // A fn with a lifetime parameter, a body, and a local in it.
    let body = s.body(vec![("n", Suite::I32, TIRIntro::Let)], Vec::new());
    let go = s.func("go", Vec::new(), Some(body));
    let TTIRItemKind::Fn(held) = &mut s.p.items[go].kind else { panic!() };
    held.generics = vec![TTIRGeneric::Life {
        name: "a".to_string(), region: 0, bounds: Vec::new(),
    }];

    // A const and a global, and a namespace holding the const.
    let max = s.item(TTIRItemKind::Const {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "MAX".to_string(), ty: Suite::I32, value: 0,
    });
    let limits = s.item(TTIRItemKind::Namespace {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "limits".to_string(), items: vec![max],
    });
    let count = s.global("count", TIRIntro::Var);
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![alias, point, color, show, go, limits, count] }];

    // Which variants turned up, anywhere in the tree.
    let mut scopes = Scopes::of(&s.p);
    // The one an import produces and a walk of one suite cannot.
    let module = module_scope(&scopes);
    scopes.bind_imports(
        module,
        &[Binding {
            name: "circle".to_string(),
            home: std::path::PathBuf::from("shapes.ft"),
            path: vec!["circle".to_string()],
            glob: false,
            via:  0,
            line: 1,
            col:  1,
        }],
    );
    let mut seen: Vec<&str> = Vec::new();
    for at in 0..scopes.len() {
        for (_, entries) in scopes.sorted(at) {
            for entry in entries {
                let what = match &entry.info {
                    Info::Variable { .. } => "Variable",
                    Info::Function { .. } => "Function",
                    Info::Struct { .. } => "Struct",
                    Info::Enum { .. } => "Enum",
                    Info::Variant { .. } => "Variant",
                    Info::Trait { .. } => "Trait",
                    Info::TypeAlias { .. } => "TypeAlias",
                    Info::Namespace(_) => "Namespace",
                    Info::Import { .. } => "Import",
                    Info::TypeParam { .. } => "TypeParam",
                    Info::Lifetime { .. } => "Lifetime",
                };
                if !seen.contains(&what) {
                    seen.push(what);
                }
            }
        }
    }
    seen.sort();
    assert_eq!(
        seen,
        vec!["Enum", "Function", "Import", "Lifetime", "Namespace", "Struct",
             "Trait", "TypeAlias", "TypeParam", "Variable", "Variant"]
    );
}

// A program is a suite and not a file, so several modules stand in it -- each
// with a scope of its own, all under the suite, which holds no names because
// there is nothing above a suite to name.
#[test]
fn a_suite_holds_a_scope_for_each_of_its_files() {
    let mut s = Suite::new();
    let here = s.func("area", vec![Suite::I32], None);
    let there = s.func("area", vec![Suite::I32], None);
    s.p.modules = vec![
        TTIRModule { path: vec!["shapes".to_string()], roots: vec![here] },
        TTIRModule { path: vec!["boxes".to_string()], roots: vec![there] },
    ];

    let scopes = Scopes::of(&s.p);
    assert_eq!(scopes.kind(scopes.root()), ScopeKind::Suite);
    assert!(scopes.sorted(scopes.root()).is_empty());

    let found: Vec<(&[String], ScopeId)> = scopes.modules().collect();
    assert_eq!(found.len(), 2);
    assert_eq!(found[0].0, ["shapes".to_string()]);
    assert_eq!(scopes.module(&["boxes".to_string()]), Some(found[1].1));

    // One name in two files is two declarations and two symbols, and neither
    // file can see the other's: an import is what reaches across.
    for (path, at) in found {
        assert_eq!(names(&scopes, at), vec!["area"]);
        let symbol = scopes.look_up(at, "area")[0].symbol.clone().expect("a symbol");
        assert!(symbol.contains(&path[0]), "{} is not in {}", path[0], symbol);
    }
    assert_ne!(
        scopes.look_up(scopes.module(&["shapes".to_string()]).unwrap(), "area")[0].symbol,
        scopes.look_up(scopes.module(&["boxes".to_string()]).unwrap(), "area")[0].symbol,
    );
}

// ---- What may be done with a name -----------------------------------------

// Four words and two questions that do not depend on each other. `let` and
// `var` say whether the binding may be assigned again; `&` and `*` say whether
// the place it refers to may be written into, and that is the reference's own
// business rather than the binding's.
#[test]
fn the_four_words_answer_two_questions() {
    let mut s = Suite::new();
    let i32 = Suite::I32;
    let read = s.ty(Ty::Ref { op: TIRRefOp::Imm, life: 0, inner: i32 });
    let write = s.ty(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: i32 });

    let body = s.body(
        vec![
            ("x", i32, TIRIntro::Let),
            ("n", i32, TIRIntro::Var),
            ("p", read, TIRIntro::Let),
            ("q", write, TIRIntro::Let),
            ("r", read, TIRIntro::Var),
        ],
        Vec::new(),
    );
    let f = s.func("go", Vec::new(), Some(body));
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![f] }];

    let scopes = Scopes::of(&s.p);
    let at = scopes.opened_by(f).expect("a fn opens a scope");
    let access = |name: &str| match &scopes.look_up(at, name)[0].info {
        Info::Variable { access, .. } => *access,
        other => panic!("{:?}", other),
    };

    // `let x: i32` -- read it, and that is all.
    assert!(!access("x").may_assign());
    assert!(!access("x").may_write_through());
    assert!(!access("x").is_reference());

    // `var n: i32` -- assign it, and a field or an element of it.
    assert!(access("n").may_assign());
    assert!(!access("n").may_write_through());

    // `let p: &i32` -- never re-aims, and writes into nothing.
    assert!(!access("p").may_assign());
    assert!(!access("p").may_write_through());
    assert!(access("p").is_reference());

    // `let q: *i32` -- never re-aims, and still writes into what it refers to.
    // This is the pair section 2 lays out: what a `let` fixes is the binding
    // and not the referent.
    assert!(!access("q").may_assign());
    assert!(access("q").may_write_through());

    // `var r: &i32` -- re-aims as often as you like, and writes into nothing.
    assert!(access("r").may_assign());
    assert!(!access("r").may_write_through());
}

// A global says the same thing a local does, and a constant is the one that is
// never assigned again whatever its type.
#[test]
fn a_global_and_a_constant_answer_the_same_two_questions() {
    let mut s = Suite::new();
    let i32 = Suite::I32;
    let write = s.ty(Ty::Ref { op: TIRRefOp::Mut, life: 0, inner: i32 });
    let counter = s.item(TTIRItemKind::Global {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), intro: TIRIntro::Var,
        name: TIRBinding::Name("counter".to_string()), ty: i32, init: None,
    });
    // `let` at file scope, of a `*` type: fixed binding, writes through.
    let held = s.item(TTIRItemKind::Global {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(), intro: TIRIntro::Let,
        name: TIRBinding::Name("held".to_string()), ty: write, init: None,
    });
    let max = s.item(TTIRItemKind::Const {
        vis: TIRVis::Pub, attrs: TIRAttrs::default(),
        name: "MAX".to_string(), ty: i32, value: 0,
    });
    let module = s.module.clone();
    s.p.modules = vec![TTIRModule { path: module, roots: vec![counter, held, max] }];

    let scopes = Scopes::of(&s.p);
    let at = module_scope(&scopes);
    let access = |name: &str| match &scopes.look_up(at, name)[0].info {
        Info::Variable { access, .. } => *access,
        other => panic!("{:?}", other),
    };
    assert!(access("counter").may_assign());
    assert!(!access("held").may_assign());
    assert!(access("held").may_write_through());
    assert!(!access("MAX").may_assign());
    assert!(!access("MAX").is_reference());
}
