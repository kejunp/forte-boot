// What a name turns out to be.
//
// `imports` settles which module a name comes from; this is what the name *is*
// once it has been found. Every name is here and not only the ones a module
// exports: a parameter, a loop variable and a name a pattern bound are all
// `Variable`, exactly as a `let` is, because a scope holds them the same way.
//
// One variant for each kind of thing that can be bound. What cannot be bound is
// not here -- a struct's field and a tuple's member are reached through a value
// and never stand on their own, and a macro's `$x` is spent by `expand` before
// this pass runs at all.
//
// A type is a `TyId`: a handle into the arena the checker is filling, which is
// the `types` of the `TTIRProgram` it is building. `Ty` in `tir::ttir_nodes` is
// what a type is here and in the typed tree both, so a name worked out in this
// table needs nothing done to it on the way into that tree. An `Option` is what
// says a type is not known yet, which is what the second spelling this module
// used to have was mostly for.

// The mangler and the tables it fills are called by tests and by `sema::scopes`
// and by nothing else yet: the pass that walks a resolved suite and emits from
// it is the one that will. The allow is for that, and comes off with it.
#![allow(dead_code)]

use std::collections::HashMap;
use std::path::PathBuf;

use crate::tir::tir_nodes::TIRFnUses;
use crate::tir::tir_nodes::{TIRBinding, TIRIntro, TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::{
    RegionId, TTIRBound, TTIRExprId, TTIRExprKind, TTIRFn, TTIRGeneric, TTIRItemId,
    TTIRItemKind, TTIRPayload, TTIRProgram, TTIRStmt, TTIRWherePred, Ty, TyId,
};

pub type Name = String;

#[derive(Debug, Clone, PartialEq)]
pub enum Info {
    // `let`, `var` and `const`, and every name bound the way one of those is: a
    // fn's parameter, a closure's, a `for`'s loop variable, the `self` of a
    // method, and a name a pattern bound in a match arm.
    //
    // `is_mut` is the `var` half of the pair `let` and `var` draw, and
    // `is_const` the value worked out at compile time -- the two are unrelated,
    // which is why they are two flags (section 2, <var_decl>).
    //
    // `gc` is not a flag here. It reaches the type, `Type::GC` being where it
    // lands, which is the question section 8 leaves open answered one way and
    // written down.
    Variable {
        ty:       Option<TyId>,
        // What may be done with it -- see `Access`.
        access:   Access,
        is_const: bool,
    },

    // A fn, wherever it was declared -- a file, a namespace, a trait, an impl.
    // A signature with no body is one of these too: what it is is the same
    // thing, and whether it has been written is the impl's business.
    //
    // `is_unsafe` has to be carried and cannot be worked out: an `unsafe fn` is
    // one whose caller has something to prove, the word is the whole of what
    // the checker has to go on, and a call to one has to stand inside an
    // `unsafe` statement (section 2).
    Function {
        generics:  Vec<TTIRGeneric>,
        // The predicates with no parameter to fold into -- see `TTIRWherePred`.
        wheres:    Vec<TTIRWherePred>,
        params:    Vec<(Name, Option<TyId>)>,
        ret:       Option<TyId>,
        is_const:  bool,
        is_unsafe: bool,
    },

    // A struct, and what it is made of.
    Struct {
        generics: Vec<TTIRGeneric>,
        fields:   Vec<Field>,
    },

    Enum {
        generics: Vec<TTIRGeneric>,
        variants: Vec<EnumVariant>,
    },

    // One variant of an enum, standing on its own. It is reached through the
    // enum -- `Color::Red` -- and an import may also bring the name in by
    // itself, which is what this is for; `of` is the enum it belongs to, since
    // by then there is nothing else left to say so.
    Variant {
        of:      Name,
        payload: Payload,
        // As on an `EnumVariant`: every variant has one whether it was written
        // or not.
        value:   i64,
    },

    // A trait, and the names it demands. The members are fns and nothing else,
    // so what is held is their names: what each one *is* is a `Function` of its
    // own, found in the trait's own scope.
    Trait {
        generics: Vec<TTIRGeneric>,
        wheres:   Vec<TTIRWherePred>,
        members:  Vec<Name>,
    },

    // `type Pair<T> = (T, T)`. A name for a type and not a type: it makes
    // nothing new, and once this has been followed there is nothing left of it
    // (section 2).
    TypeAlias {
        generics: Vec<TTIRGeneric>,
        wheres:   Vec<TTIRWherePred>,
        // What it names, followed. An alias makes no new type: this is the
        // type, and the alias is the name written in front of it.
        ty:       TyId,
    },

    // A name an import brought in. What it names is in another module and this
    // is the way to it -- the file it came from, and the path inside that file.
    // It stays a way and does not become the thing: resolving it wants the
    // other module's own table, and a module is read before the ones that
    // import it only where nothing is written in a circle.
    Import {
        home: PathBuf,
        path: Vec<Name>,
    },

    // A namespace, and a file besides -- a file is a module and a namespace
    // nests another inside the one it is written in, so the two are reached the
    // same way and there is one thing here for both (section 1). What it holds
    // is the names it declares; what each of those is, its own scope says.
    Namespace(Vec<Name>),

    // A generic parameter, the `T` of `fn f<T: Ord>`. It names a type without
    // being one, which is the whole of why it is not a `TypeAlias`: what it
    // stands for is settled at the call and not at the declaration.
    //
    // `index` is its place in the declaration's own list, which is what
    // `Ty::Param` names it by -- so a `T` found in a scope and a `T` standing in
    // a signature are known to be the same one.
    TypeParam {
        index:  usize,
        bounds: Vec<TTIRBound>,
    },

    // A lifetime parameter, the `'a` of `fn f<'a>`. The `~` was the lexer's and
    // the name is what is left, so it is a name in a scope like any other --
    // which is what a `'a: 'b` needs it to be. `region` is what a `&'a T` in
    // the signature points at, and `bounds` what it has to outlive.
    Lifetime {
        index:  usize,
        region: RegionId,
        bounds: Vec<RegionId>,
    },
}

// What may be done with a name. The language writes it with four words, and
// they answer two questions that do not depend on each other:
//
//     let  x: i32     read it, and that is all
//     var  x: i32     assign it, and assign a field or an element of it
//     let  p: &i32    never re-aims, and writes into nothing
//     let  p: *i32    never re-aims, and writes into what it refers to
//     var  p: &i32    re-aims as often as you like, and writes into nothing
//
// The last two are the pair section 2 lays out: what a `let` fixes is the
// binding and not the referent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Access {
    // `let` binds a name that is read and never written, `var` one that may be
    // assigned again. Mutability is the root binding's and writing reaches
    // through whatever is reached from it -- a field or an element of a `var`
    // may be assigned and one of a `let` may not -- so this is one answer for
    // the whole name and not one per place under it. There is no marking a
    // single field of a `let` writable, and none weakening one of a `var`.
    pub is_mut:  bool,
    // `&T` reads and `*T` writes, and which of the two is the reference's own
    // business rather than the binding's. `None` where the name is of no
    // reference type, and so refers to no other place to write into.
    pub through: Option<TIRRefOp>,
}

impl Access {
    // What the four words come to for a name of type `ty`. `is_mut` is the
    // intro's -- `let` or `var` -- and the rest is read off the type, that
    // being the one place a `&` or a `*` is written down.
    pub fn of(is_mut: bool, ty: TyId, types: &[Ty]) -> Access {
        let through = match &types[ty] {
            Ty::Ref { op, .. } => Some(*op),
            // A hole and an `Error` say nothing either way, and neither does a
            // type that is not a reference.
            _ => None,
        };
        Access { is_mut, through }
    }

    // Whether the name may be assigned again, and with it any field or element
    // reached from it.
    pub fn may_assign(&self) -> bool {
        self.is_mut
    }

    // Whether the place it refers to may be written into. A name of no
    // reference type refers to no other place, so the answer is no.
    pub fn may_write_through(&self) -> bool {
        matches!(self.through, Some(TIRRefOp::Mut))
    }

    // Whether it refers to another place at all, which is what tells
    // `let x: i32` from `let p: &i32`.
    pub fn is_reference(&self) -> bool {
        self.through.is_some()
    }
}

// One field of a struct. `vis` is the field's own, so a struct may be exported
// with fields that are not. Three answers and not a flag: `pub(suite)` is the
// middle one and a `bool` could not hold it (section 1).
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: Name,
    pub ty:   TyId,
    pub vis:  TIRVis,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub name:    Name,
    pub payload: Payload,
    // What it is worth. Every variant has one whether it was written or not --
    // `D = 4` says so and `A` is counted -- so it stands beside the payload
    // rather than being a fourth kind of one, as `TTIRVariant` has it.
    pub value:   i64,
}

// What a variant carries.
#[derive(Debug, Clone, PartialEq)]
pub enum Payload {
    // `A`
    None,
    // `B(i32, str)`, reached by number.
    Tuple(Vec<TyId>),
    // `C { x: i32 }`, reached by name.
    Named(Vec<Field>),
}
// ---- Mangling -------------------------------------------------------------
//
// The symbol a fn is compiled to. Every part is written as its length and then
// its characters -- `add` of two i32 is `3add3i323i32` (section 1) -- and the
// length is the whole of what keeps it unambiguous. Nothing is escaped: an `_`
// inside a name is a character like any other, where a separator between the
// parts would have had to reserve one, and a space or a `<` inside a type's
// spelling is no different.
//
// A symbol opens with `__F`, and the parts follow it: `foo` in the namespace
// `namespaces`, taking an i32 and a `mytype`, is
//
//     __F10namespaces3foo3i326mytype
//
// The two underscores are what nothing written in the language can begin with,
// so a mangled name cannot collide with one a `%symbol` gave or with anything
// on the other side of a foreign declaration; the `F` says a function, and
// leaves room for a letter for whatever else has to be named later.
//
// The parts, in order:
//
//   - where it is declared, one part per segment. A file is a module and a
//     namespace nests another inside it (section 1), so both are segments and
//     the file's come first: `area` at the top of `shapes.fc` is `6shapes4area`
//     and not `4area`, or two files could not each hold one. A method's segments
//     are the impl it is written in -- the type it is for, and the trait where
//     there is one, since `impl Buf` and `impl Show for Buf` may both hold a
//     `len` and only the trait tells the two apart.
//   - its own name.
//   - each parameter's type, spelled by `Mangler::spell`.
//
// The return type is not among them. Two fns may share a name and be told apart
// by what they take (section 1); nothing tells them apart by what they give
// back, so a return type in the symbol would only make one no call could work
// out. Nor is a lifetime: a region is worked out rather than written, and two
// fns differing in one are the same code.

// Built once for a program: where an item is declared is a fact about the
// program and not about the fn being named, and working it out per fn would be
// walking the whole tree for each of them.
// What a mangled name opens with: `__` because nothing written in the language
// may begin with it, so a mangled name collides with nothing a `%symbol` gave
// and with nothing on the other side of a foreign declaration -- and then a
// letter for the kind of thing being named, so a struct and a fn of one name in
// one module are two symbols.
//
// `None` for the three the linker never sees: an `impl`, which is reached
// through the type it is written for; a global bound to `_`, which was
// deliberately not named; and a type alias, which makes no new type and no
// code -- it is a name in a scope and nothing to compile.
fn prefix_of(kind: &TTIRItemKind) -> Option<&'static str> {
    Some(match kind {
        TTIRItemKind::Fn(_) => "__F",
        TTIRItemKind::Struct { .. } => "__S",
        TTIRItemKind::Enum { .. } => "__E",
        TTIRItemKind::Trait { .. } => "__T",
        TTIRItemKind::Namespace { .. } => "__N",
        TTIRItemKind::Const { .. } => "__C",
        TTIRItemKind::Global { name, .. } => match name {
            TIRBinding::Name(_) => "__G",
            _ => return None,
        },
        TTIRItemKind::Impl { .. } | TTIRItemKind::TypeAlias { .. } => return None,
    })
}

pub struct Mangler {
    // The segments each item is declared under, by item. Empty for an item at
    // the top of the root module, and for one nothing reaches.
    paths: Vec<Vec<Name>>,
}

impl Mangler {
    // Every module of the suite, each walked from its own path: a file is a
    // module and its name stands in front of everything it declares, so the
    // segments start there rather than empty.
    pub fn new(p: &TTIRProgram) -> Mangler {
        let mut m = Mangler { paths: vec![Vec::new(); p.items.len()] };
        for module in &p.modules {
            m.nest(&module.roots, &module.path, p);
        }
        m.members(p);
        m
    }

    // The symbol `f` is compiled to, `at` being the item it is.
    pub fn symbol(&self, f: &TTIRFn, at: TTIRItemId, p: &TTIRProgram) -> String {
        // `%symbol("malloc")` is the exact name and not a part of one. Nothing
        // outside the language can predict a mangling, which is the whole of
        // why a call out to C is written with this.
        if let Some(given) = &f.attrs.symbol {
            return given.clone();
        }

        let mut out = String::from("__F");
        for segment in &self.paths[at] {
            part(segment, &mut out);
        }
        part(&f.name, &mut out);
        // The parameters come from the fn's own type rather than from its
        // body: a signature has no body and is mangled like anything else.
        let Ty::Fn { params, .. } = &p.types[f.ty] else {
            panic!("`{}` has a type that is not a fn type", f.name)
        };
        for &ty in params {
            part(&self.spell(ty, p), &mut out);
        }
        out
    }

    // The symbol of any declaration, not just a fn. Everything but a fn is its
    // prefix, where it is declared, and its name: only a fn has parameters to
    // be told apart by, and only a fn may be given a name with `%symbol`.
    //
    // `None` where there is nothing to name -- an `impl`, or a global bound to
    // `_`. Neither is a thing the linker ever sees.
    pub fn symbol_of(&self, at: TTIRItemId, p: &TTIRProgram) -> Option<String> {
        let kind = &p.items[at].kind;
        if let TTIRItemKind::Fn(f) = kind {
            return Some(self.symbol(f, at, p));
        }
        let mut out = String::from(prefix_of(kind)?);
        for segment in &self.paths[at] {
            part(segment, &mut out);
        }
        part(&name_of(at, p), &mut out);
        Some(out)
    }

    // A type as one part of a symbol writes it. The language's own spelling,
    // with the whitespace it does not need taken out: it is one part however
    // many characters it runs to, so nothing inside it has to be told apart
    // from anything outside it.
    pub fn spell(&self, id: TyId, p: &TTIRProgram) -> String {
        match &p.types[id] {
            Ty::Prim(prim) => prim_name(*prim).to_string(),

            Ty::Named { item, args, .. } => {
                let mut out = self.paths[*item]
                    .iter()
                    .map(|s| format!("{}::", s))
                    .collect::<String>();
                out.push_str(&name_of(*item, p));
                if !args.is_empty() {
                    out.push('<');
                    out.push_str(&self.spell_all(args, p));
                    out.push('>');
                }
                out
            }

            // The region is left out on purpose -- see the note above.
            Ty::Ref { op, inner, .. } => {
                format!("{}{}", ref_op(*op), self.spell(*inner, p))
            }
            Ty::Ptr(inner) => format!("ptr {}", self.spell(*inner, p)),
            Ty::GC(inner) => format!("gc {}", self.spell(*inner, p)),

            Ty::Array { elem, len } => format!("{}[{}]", self.spell(*elem, p), len),
            Ty::Run(elem) => format!("{}[]", self.spell(*elem, p)),
            Ty::Tuple(members) => format!("({})", self.spell_all(members, p)),

            Ty::Fn { uses, params, ret, is_unsafe } => format!(
                "{}{}fn({}):{}",
                match uses {
                    TIRFnUses::Reads => "",
                    TIRFnUses::Writes => "var ",
                    TIRFnUses::Takes => "once ",
                },
                if *is_unsafe { "unsafe " } else { "" },
                self.spell_all(params, p),
                self.spell(*ret, p)
            ),

            // By its place and not by its name: `f<T>(x: T)` and `f<U>(x: U)`
            // are one function written twice, and a symbol that told them apart
            // would be telling apart what a caller cannot.
            Ty::Param { index, .. } => format!("${}", index),

            // Nothing is compiled out of a program that did not type, so a fn
            // being named can hold neither of these: a hole means the checker
            // never finished, and an `Error` means it finished and said no.
            Ty::Var(_) | Ty::Error => {
                panic!("a type that was never worked out reached the mangler")
            }
        }
    }

    fn spell_all(&self, ids: &[TyId], p: &TTIRProgram) -> String {
        ids.iter().map(|&i| self.spell(i, p)).collect::<Vec<_>>().join(",")
    }

    // ---- Where an item is declared ---------------------------------------

    // Down through the namespaces, and down through a fn's body besides: a
    // declaration may stand in a block (section 2), and one that does is a
    // declaration like any other -- so it is named after the fn it is written
    // in, the way a method is named after its impl.
    fn nest(&mut self, items: &[TTIRItemId], at: &[Name], p: &TTIRProgram) {
        for &id in items {
            self.paths[id] = at.to_vec();
            match &p.items[id].kind {
                TTIRItemKind::Namespace { name, items, .. } => {
                    let mut inner = at.to_vec();
                    inner.push(name.clone());
                    self.nest(items, &inner, p);
                }
                TTIRItemKind::Fn(f) => {
                    let nested = nested_items(f, p);
                    if nested.is_empty() {
                        continue;
                    }
                    let mut inner = at.to_vec();
                    inner.push(f.name.clone());
                    self.nest(&nested, &inner, p);
                }
                _ => {}
            }
        }
    }

    // A method is declared in an impl or a trait rather than in a namespace, so
    // its segments are that one's. Run after `nest`, which is what gives the
    // impl itself somewhere to stand and gives `spell` the paths it reads.
    fn members(&mut self, p: &TTIRProgram) {
        for id in 0..p.items.len() {
            let mut at = self.paths[id].clone();
            let members = match &p.items[id].kind {
                TTIRItemKind::Impl { ty, of, members, .. } => {
                    // The type's spelling, minus whatever of it the segments
                    // in front already say: an `impl Point` inside `shapes` is
                    // `6shapes5Point` and not `6shapes13shapes::Point`. A type
                    // from somewhere else keeps its path, which is what tells
                    // an `impl other::Buf` from an `impl Buf`.
                    let spelled = self.spell(*ty, p);
                    let here = at.iter().map(|s| format!("{}::", s)).collect::<String>();
                    at.push(match spelled.strip_prefix(&here) {
                        Some(rest) => rest.to_string(),
                        None => spelled,
                    });
                    if let Some(of) = of {
                        at.push(name_of(*of, p));
                    }
                    members
                }
                TTIRItemKind::Trait { name, members, .. } => {
                    at.push(name.clone());
                    members
                }
                _ => continue,
            };
            for &member in members {
                self.paths[member] = at.clone();
            }
        }
    }
}

// One part: how long it is, and then it.
fn part(text: &str, out: &mut String) {
    out.push_str(&text.chars().count().to_string());
    out.push_str(text);
}

// What an item is called. An `impl` has no name of its own -- it is reached
// through the type it is written for -- and nothing here asks one for it.
fn name_of(id: TTIRItemId, p: &TTIRProgram) -> String {
    match &p.items[id].kind {
        TTIRItemKind::Fn(f) => f.name.clone(),
        TTIRItemKind::Struct { name, .. }
        | TTIRItemKind::Enum { name, .. }
        | TTIRItemKind::Trait { name, .. }
        | TTIRItemKind::Namespace { name, .. }
        | TTIRItemKind::TypeAlias { name, .. }
        | TTIRItemKind::Const { name, .. } => name.clone(),
        TTIRItemKind::Global { name, .. } => match name {
            crate::tir::tir_nodes::TIRBinding::Name(name) => name.clone(),
            other => panic!("a global bound by {:?} was asked its name", other),
        },
        TTIRItemKind::Impl { .. } => panic!("an impl was asked for a name it has not got"),
    }
}

fn prim_name(prim: TIRPrim) -> &'static str {
    match prim {
        TIRPrim::I8 => "i8",
        TIRPrim::I16 => "i16",
        TIRPrim::I32 => "i32",
        TIRPrim::I64 => "i64",
        TIRPrim::I128 => "i128",
        TIRPrim::U8 => "u8",
        TIRPrim::U16 => "u16",
        TIRPrim::U32 => "u32",
        TIRPrim::U64 => "u64",
        TIRPrim::U128 => "u128",
        TIRPrim::F32 => "f32",
        TIRPrim::F64 => "f64",
        TIRPrim::Bool => "bool",
        TIRPrim::Char => "char",
        TIRPrim::Str => "str",
        TIRPrim::Null => "null",
        TIRPrim::Never => "never",
    }
}

fn ref_op(op: TIRRefOp) -> &'static str {
    match op {
        TIRRefOp::Imm => "&",
        TIRRefOp::Mut => "*",
    }
}

#[cfg(test)]
mod tests;

// ---- The symbol table -----------------------------------------------------
//
// What a program declares, by the name the linker sees: `symbol: Info`. One
// flat table and not a tree, because a symbol already carries where the thing
// was declared -- that is what the segments in front of it are for -- so
// nothing has to be walked into to find an entry.
//
// Keyed by the symbol and not by the name for the reason mangling exists at
// all: two fns may share a name and be told apart by what they take, so a table
// keyed by `add` could hold only one of them. `__F6shapes3add3i323i32` and
// `__F6shapes3add3f643f64` are two entries and one word in the source.
//
// What is *not* here is everything the linker never names: a local, a
// parameter, a generic parameter, a lifetime, an enum's variants. Those are
// what a scope holds, keyed by the name that was written, and a scope is the
// next thing to build.

pub struct SymbolTable {
    entries: HashMap<String, Info>,
    // Two declarations that mangled the same. It cannot happen from a program
    // the checker took -- two fns of one name and one parameter list is an
    // error where the second is written -- so anything in here is either that
    // error let through or the mangler having come apart, and the caller is
    // the one placed to say which.
    clashes: Vec<String>,
}

impl SymbolTable {
    // Every declaration in the suite.
    pub fn of(p: &TTIRProgram) -> SymbolTable {
        let m = Mangler::new(p);
        let mut table = SymbolTable { entries: HashMap::new(), clashes: Vec::new() };
        for id in 0..p.items.len() {
            let Some(symbol) = m.symbol_of(id, p) else { continue };
            let Some(info) = info_of(id, p) else { continue };
            if table.entries.insert(symbol.clone(), info).is_some() {
                table.clashes.push(symbol);
            }
        }
        table
    }

    pub fn get(&self, symbol: &str) -> Option<&Info> {
        self.entries.get(symbol)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &Info)> {
        self.entries.iter()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn clashes(&self) -> &[String] {
        &self.clashes
    }

    // The entries in symbol order, which is what a report or a test wants: a
    // `HashMap` has an order and it is not one anybody chose.
    pub fn sorted(&self) -> Vec<(&String, &Info)> {
        let mut out: Vec<(&String, &Info)> = self.entries.iter().collect();
        out.sort_by(|a, b| a.0.cmp(b.0));
        out
    }
}

// What one declaration is. `None` for an `impl`, which declares no name of its
// own, and for a global bound to `_`.
pub fn info_of(at: TTIRItemId, p: &TTIRProgram) -> Option<Info> {
    Some(match &p.items[at].kind {
        TTIRItemKind::Fn(f) => Info::Function {
            generics:  f.generics.clone(),
            wheres:    f.wheres.clone(),
            params:    params_of(f, p),
            ret:       Some(f.ret),
            is_const:  f.is_const,
            is_unsafe: f.is_unsafe,
        },
        TTIRItemKind::Struct { generics, fields, .. } => Info::Struct {
            generics: generics.clone(),
            fields:   fields.iter().map(field_of).collect(),
        },
        TTIRItemKind::Enum { generics, variants, .. } => Info::Enum {
            generics: generics.clone(),
            variants: variants
                .iter()
                .map(|v| EnumVariant {
                    name:    v.name.clone(),
                    payload: payload_of(&v.payload),
                    value:   v.value,
                })
                .collect(),
        },
        TTIRItemKind::Trait { generics, wheres, members, .. } => Info::Trait {
            generics: generics.clone(),
            wheres:   wheres.clone(),
            members:  members.iter().map(|&m| name_of(m, p)).collect(),
        },
        // An alias makes no new type, so what it is is the type it names and
        // the name written in front of it.
        TTIRItemKind::TypeAlias { generics, wheres, ty, .. } => Info::TypeAlias {
            generics: generics.clone(),
            wheres:   wheres.clone(),
            ty:       *ty,
        },
        TTIRItemKind::Namespace { items, .. } => {
            // The names it declares. What each one is, its own entry says --
            // holding them twice is what would let the two come apart.
            Info::Namespace(
                items
                    .iter()
                    .filter(|&&i| !matches!(p.items[i].kind, TTIRItemKind::Impl { .. }))
                    .map(|&i| name_of(i, p))
                    .collect(),
            )
        }
        // A constant is a name for a value worked out at compile time, which is
        // a `Variable` that says so rather than a kind of its own.
        TTIRItemKind::Const { ty, .. } => Info::Variable {
            ty:       Some(*ty),
            // A constant is never assigned again, whatever its type; a `&` or
            // a `*` in that type still says what may be written through it.
            access:   Access::of(false, *ty, &p.types),
            is_const: true,
        },
        TTIRItemKind::Global { intro, name, ty, .. } => {
            let TIRBinding::Name(_) = name else { return None };
            Info::Variable {
                ty:       Some(*ty),
                access:   Access::of(matches!(intro, TIRIntro::Var), *ty, &p.types),
                is_const: false,
            }
        }
        TTIRItemKind::Impl { .. } => return None,
    })
}

// A fn's parameters: the name each was declared with, and its type. The names
// are the fn's own and the types its `Ty::Fn`'s, each written down in one place
// only -- so a signature answers this as fully as a body does, having been
// declared just as fully.
fn params_of(f: &TTIRFn, p: &TTIRProgram) -> Vec<(Name, Option<TyId>)> {
    let Ty::Fn { params, .. } = &p.types[f.ty] else {
        panic!("`{}` has a type that is not a fn type", f.name)
    };
    params
        .iter()
        .enumerate()
        .map(|(i, &ty)| {
            let name = match f.params.get(i).map(|param| &param.name) {
                Some(TIRBinding::Name(name)) => name.clone(),
                // `_` binds nothing on purpose and a receiver is `self`, and
                // neither is a name a caller may write.
                _ => "_".to_string(),
            };
            (name, Some(ty))
        })
        .collect()
}

// What a variant carries, as this table spells it. Wanted in two places: an
// enum's own entry holds every variant, and a scope holds each on its own.
pub fn payload_of(payload: &TTIRPayload) -> Payload {
    match payload {
        TTIRPayload::None => Payload::None,
        TTIRPayload::Tuple(tys) => Payload::Tuple(tys.clone()),
        TTIRPayload::Named(fields) => Payload::Named(fields.iter().map(field_of).collect()),
    }
}

fn field_of(f: &crate::tir::ttir_nodes::TTIRFieldDecl) -> Field {
    Field { name: f.name.clone(), ty: f.ty, vis: f.vis }
}

// ---- Declarations written inside a body -----------------------------------

// The items declared in `f`'s body, in the order they were written. A block
// holds statements and one of them may be a declaration, so a fn, a struct or a
// namespace can stand inside another fn -- and every pass that walks the items
// of a program has to reach those too, or they are named by nothing and stand
// in no scope.
//
// One level: what is nested inside *those* is reached by asking them in turn,
// which is what `Mangler::nest` and `Scopes` both do.
pub fn nested_items(f: &TTIRFn, p: &TTIRProgram) -> Vec<TTIRItemId> {
    let Some(body) = f.body else { return Vec::new() };
    let mut out = Vec::new();
    walk_expr(p.bodies[body].value, p, &mut out);
    out
}

// Every `TTIRStmt::Item` under one expression. A block is an expression and
// expressions nest, so a declaration inside the `else` of an `if` inside a
// `while` is as reachable as one at the top of the body.
fn walk_expr(id: TTIRExprId, p: &TTIRProgram, out: &mut Vec<TTIRItemId>) {
    use TTIRExprKind::*;
    match &p.exprs[id].kind {
        Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    TTIRStmt::Item(item) => out.push(*item),
                    TTIRStmt::Let { init, .. } => {
                        for &e in init.iter() {
                            walk_expr(e, p, out);
                        }
                    }
                    TTIRStmt::Expr { expr, .. } => walk_expr(*expr, p, out),
                }
            }
            for &e in tail.iter() {
                walk_expr(e, p, out);
            }
        }

        If { cond, then, els } => {
            walk_expr(*cond, p, out);
            walk_expr(*then, p, out);
            for &e in els.iter() {
                walk_expr(e, p, out);
            }
        }
        While { cond, body } => {
            walk_expr(*cond, p, out);
            walk_expr(*body, p, out);
        }
        For { iter, body, .. } => {
            walk_expr(*iter, p, out);
            walk_expr(*body, p, out);
        }
        Match { scrutinee, arms } => {
            walk_expr(*scrutinee, p, out);
            for arm in arms {
                walk_expr(arm.body, p, out);
            }
        }
        // A closure's body is an expression like any other, and a declaration
        // may stand in it.
        Closure { body, .. } => walk_expr(*body, p, out),

        Field { base, .. } | TupleIndex { base, .. } | Cast(base) => walk_expr(*base, p, out),
        Unary { operand, .. } => walk_expr(*operand, p, out),
        Binary { lhs, rhs, .. } => {
            walk_expr(*lhs, p, out);
            walk_expr(*rhs, p, out);
        }
        Assign { place, value, .. } => {
            walk_expr(*place, p, out);
            walk_expr(*value, p, out);
        }
        Index { base, index } => {
            walk_expr(*base, p, out);
            walk_expr(*index, p, out);
        }
        Range { start, end, .. } => {
            for &e in start.iter().chain(end.iter()) {
                walk_expr(e, p, out);
            }
        }
        Call { callee, args } => {
            walk_expr(*callee, p, out);
            for &a in args {
                walk_expr(a, p, out);
            }
        }
        Method { recv, args, .. } => {
            walk_expr(*recv, p, out);
            for &a in args {
                walk_expr(a, p, out);
            }
        }
        ArrayLit(es)
        | TupleLit(es)
        | Set { elems: es, .. }
        | StructLit { fields: es, .. }
        | VariantLit { fields: es, .. } => {
            for &e in es {
                walk_expr(e, p, out);
            }
        }
        Map { entries, .. } => {
            for &(key, value) in entries {
                walk_expr(key, p, out);
                walk_expr(value, p, out);
            }
        }
        Return(e) | Break(e) => {
            for &e in e.iter() {
                walk_expr(e, p, out);
            }
        }

        // The leaves, and the one that already is an item.
        Literal(_) | Local(_) | Item(_) | SelfExpr | Continue => {}
    }
}
