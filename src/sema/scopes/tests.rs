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
            ty,
            params:    slots,
            ret:       Self::NULL,
            body,
        }))
    }

    fn strukt(&mut self, name: &str) -> TTIRItemId {
        self.item(TTIRItemKind::Struct {
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
