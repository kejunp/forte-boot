// Where a name is looked up.
//
// `names::SymbolTable` is keyed by the name the linker sees; this is keyed by
// the name the source wrote, and the two are the halves of what a resolver
// needs. A symbol is unique and a name is not -- two fns may share one and be
// told apart by what they take -- so a symbol reaches one entry and a name
// reaches however many were declared under it.
//
// Scopes nest, and a name is looked for from the inside out: the innermost
// scope that has it answers, and the outer ones are not asked. That is what
// makes a local shadow a global of the same name, and it is why the answer is a
// *list* only within one scope -- two `add`s in one module are two answers to
// one question, while an `add` in a fn and an `add` in the module around it are
// one answer and one thing hidden.
//
// A block opens no scope of its own. The TTIR has already settled which slot
// every name refers to -- a body's `locals` is one flat list, and a `Local` is
// an index into it -- so by here a fn is one scope and the braces inside it are
// spelling. That is the whole of what `sema` had to work out about them.

#![allow(dead_code)]

use std::collections::HashMap;

use crate::sema::names::{info_of, nested_items, Info, Mangler, Name};
use crate::tir::tir_nodes::TIRBinding;
use crate::tir::ttir_nodes::{TTIRGeneric, TTIRItemId, TTIRItemKind, TTIRProgram};

pub type ScopeId = usize;

// What opened a scope. Nothing here reads it yet; it is what a rule about where
// something may be written asks -- a receiver only in an impl, a `Self` only
// where there is one to mean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    // A file, which is a module (section 1). The outermost scope there is: the
    // suite above it holds no names of its own, only the files that do.
    Module,
    Namespace,
    Trait,
    Impl,
    // A struct and an enum open one too, and hold nothing but their generic
    // parameters: `T` is a name inside `struct S<T> { v: T }` and nowhere else.
    Struct,
    Enum,
    // A fn, holding its parameters and every slot of its body -- see the note
    // above about blocks.
    Function,
}

// One name in one scope, and the way from it to everything else: `symbol` is
// how a name reaches `SymbolTable`, and is `None` for what the linker never
// sees -- a local, a parameter, a generic parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Entry {
    pub info:   Info,
    pub symbol: Option<String>,
    pub line:   usize,
    pub col:    usize,
}

struct Scope {
    parent: Option<ScopeId>,
    kind:   ScopeKind,
    // Several under one name is an overload; see the note above about why that
    // is a list here and not across scopes.
    names:  HashMap<Name, Vec<Entry>>,
}

pub struct Scopes {
    scopes: Vec<Scope>,
    // The scope each item opened, for whatever wants to walk into a fn or a
    // namespace it has a handle to. `None` for an item that opens none.
    opened: Vec<Option<ScopeId>>,
}

impl Scopes {
    // An empty tree with nothing but the module scope at the root of it.
    pub fn new() -> Scopes {
        Scopes {
            scopes: vec![Scope {
                parent: None,
                kind:   ScopeKind::Module,
                names:  HashMap::new(),
            }],
            opened: Vec::new(),
        }
    }

    // Every scope a program opens, and every name in each. `at` is the module
    // the program was read at, which the symbols want -- see `Mangler::new`.
    pub fn of(p: &TTIRProgram, at: &[Name]) -> Scopes {
        let m = Mangler::new(p, at);
        let mut s = Scopes::new();
        s.opened = vec![None; p.items.len()];
        let root = s.root();
        s.items(&p.roots, root, p, &m);
        s
    }

    pub fn root(&self) -> ScopeId {
        0
    }

    pub fn open(&mut self, parent: ScopeId, kind: ScopeKind) -> ScopeId {
        self.scopes.push(Scope { parent: Some(parent), kind, names: HashMap::new() });
        self.scopes.len() - 1
    }

    pub fn bind(&mut self, at: ScopeId, name: Name, entry: Entry) {
        self.scopes[at].names.entry(name).or_default().push(entry);
    }

    pub fn kind(&self, at: ScopeId) -> ScopeKind {
        self.scopes[at].kind
    }

    pub fn parent(&self, at: ScopeId) -> Option<ScopeId> {
        self.scopes[at].parent
    }

    pub fn len(&self) -> usize {
        self.scopes.len()
    }

    // The scope `item` opened, where it opened one.
    pub fn opened_by(&self, item: TTIRItemId) -> Option<ScopeId> {
        self.opened.get(item).copied().flatten()
    }

    // What `name` refers to, seen from `at`. The innermost scope that has it
    // answers and the rest are not asked, so a local hides a global rather than
    // standing beside it; within that one scope every entry is an answer, since
    // two fns of one name are told apart by what they take and not by where
    // they are.
    pub fn look_up(&self, at: ScopeId, name: &str) -> &[Entry] {
        let mut here = Some(at);
        while let Some(id) = here {
            if let Some(found) = self.scopes[id].names.get(name) {
                return found;
            }
            here = self.scopes[id].parent;
        }
        &[]
    }

    // What this scope alone has, without asking the ones around it. What a
    // shadowing rule is written against.
    pub fn here(&self, at: ScopeId, name: &str) -> &[Entry] {
        self.scopes[at].names.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    // The names one scope holds, in order, for a report or a test: a `HashMap`
    // has an order and it is not one anybody chose.
    pub fn sorted(&self, at: ScopeId) -> Vec<(&Name, &Vec<Entry>)> {
        let mut out: Vec<(&Name, &Vec<Entry>)> = self.scopes[at].names.iter().collect();
        out.sort_by(|a, b| a.0.cmp(b.0));
        out
    }

    // ---- Building --------------------------------------------------------

    // Binds each item in `at`, and opens the scope any of them opens.
    fn items(&mut self, items: &[TTIRItemId], at: ScopeId, p: &TTIRProgram, m: &Mangler) {
        for &id in items {
            let item = &p.items[id];
            if let Some(name) = declared_name(id, p) {
                if let Some(info) = info_of(id, p) {
                    let entry = Entry {
                        info,
                        symbol: m.symbol_of(id, p),
                        line: item.line,
                        col: item.col,
                    };
                    self.bind(at, name, entry);
                }
            }
            self.inside(id, at, p, m);
        }
    }

    // The scope an item opens, and what stands in it.
    fn inside(&mut self, id: TTIRItemId, at: ScopeId, p: &TTIRProgram, m: &Mangler) {
        match &p.items[id].kind {
            TTIRItemKind::Namespace { items, .. } => {
                let inner = self.open(at, ScopeKind::Namespace);
                self.opened[id] = Some(inner);
                self.items(items, inner, p, m);
            }
            // Neither holds a name that is looked up, but both take generic
            // parameters, and a parameter is a name in the scope its
            // declaration opens -- which is why they open one at all.
            TTIRItemKind::Struct { generics, .. } => {
                let inner = self.open(at, ScopeKind::Struct);
                self.opened[id] = Some(inner);
                self.generics(generics, inner);
            }
            TTIRItemKind::Enum { generics, .. } => {
                let inner = self.open(at, ScopeKind::Enum);
                self.opened[id] = Some(inner);
                self.generics(generics, inner);
            }
            // A trait's members and an impl's are declared in it and reached
            // through it, so each is a scope of its own rather than a run of
            // names in the module around it.
            TTIRItemKind::Trait { generics, members, .. } => {
                let inner = self.open(at, ScopeKind::Trait);
                self.opened[id] = Some(inner);
                self.generics(generics, inner);
                self.items(members, inner, p, m);
            }
            TTIRItemKind::Impl { generics, members, .. } => {
                let inner = self.open(at, ScopeKind::Impl);
                self.opened[id] = Some(inner);
                // The impl's own, which every method in it can see: the `T` of
                // `impl<T> Stack<T>` stands in each of their signatures.
                self.generics(generics, inner);
                self.items(members, inner, p, m);
            }
            TTIRItemKind::Fn(f) => {
                let inner = self.open(at, ScopeKind::Function);
                self.opened[id] = Some(inner);
                self.generics(&f.generics, inner);

                // Every slot of the body, parameters among them: `params` are
                // locals like any other, and a body's list is flat.
                if let Some(body) = f.body {
                    for local in &p.bodies[body].locals {
                        let TIRBinding::Name(name) = &local.name else { continue };
                        self.bind(
                            inner,
                            name.clone(),
                            Entry {
                                info:   Info::Variable {
                                    ty:       Some(local.ty),
                                    is_mut:   matches!(
                                        local.intro,
                                        crate::tir::tir_nodes::TIRIntro::Var
                                    ),
                                    is_const: false,
                                },
                                // A local is not a thing the linker names.
                                symbol: None,
                                line:   p.items[id].line,
                                col:    p.items[id].col,
                            },
                        );
                    }
                }
                // A declaration written in a block stands in the fn's scope,
                // which is the one the block does not open.
                let nested = nested_items(f, p);
                self.items(&nested, inner, p, m);
            }
            _ => {}
        }
    }
}

// The parameters a declaration was written with, bound in the scope it opened.
// A parameter names a type without being one, and it is a name in a scope like
// any other -- which is what a `T` in a signature and a `'a: 'b` both need.
impl Scopes {
    fn generics(&mut self, generics: &[TTIRGeneric], at: ScopeId) {
        for (index, generic) in generics.iter().enumerate() {
            let (name, info) = match generic {
                TTIRGeneric::Type { name, bounds } => {
                    (name.clone(), Info::TypeParam { index, bounds: bounds.clone() })
                }
                TTIRGeneric::Life { name, region, bounds } => (
                    name.clone(),
                    Info::Lifetime { index, region: *region, bounds: bounds.clone() },
                ),
            };
            // A parameter is not a thing the linker names, and it stands where
            // it was declared rather than at a line of its own.
            self.bind(at, name, Entry { info, symbol: None, line: 0, col: 0 });
        }
    }
}

impl Default for Scopes {
    fn default() -> Scopes {
        Scopes::new()
    }
}

// The name an item is declared under, where it has one. An `impl` has none --
// it is reached through the type it is written for -- and a global bound to `_`
// was deliberately not given one.
fn declared_name(id: TTIRItemId, p: &TTIRProgram) -> Option<Name> {
    Some(match &p.items[id].kind {
        TTIRItemKind::Fn(f) => f.name.clone(),
        TTIRItemKind::Struct { name, .. }
        | TTIRItemKind::Enum { name, .. }
        | TTIRItemKind::Trait { name, .. }
        | TTIRItemKind::Namespace { name, .. }
        | TTIRItemKind::Const { name, .. } => name.clone(),
        TTIRItemKind::Global { name, .. } => match name {
            TIRBinding::Name(name) => name.clone(),
            _ => return None,
        },
        TTIRItemKind::Impl { .. } => return None,
    })
}

#[cfg(test)]
mod tests;
