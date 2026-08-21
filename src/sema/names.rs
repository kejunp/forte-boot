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

// Nothing constructs these yet: the pass that walks a scope and fills them in
// is the next one to write. The allow is theirs and comes off with it, as the
// one in `tir_nodes` comes off with the pass that reads the TIR.
#![allow(dead_code)]

use crate::tir::tir_nodes::{TIRPrim, TIRRefOp, TIRVis};
use crate::tir::ttir_nodes::{TTIRFn, TTIRItemId, TTIRItemKind, TTIRProgram, Ty, TyId};

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
        is_mut:   bool,
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
        generics:  Vec<Generic>,
        params:    Vec<(Name, Option<TyId>)>,
        ret:       Option<TyId>,
        is_const:  bool,
        is_unsafe: bool,
    },

    // A struct, and what it is made of.
    Struct {
        generics: Vec<Generic>,
        fields:   Vec<Field>,
    },

    Enum {
        generics: Vec<Generic>,
        variants: Vec<EnumVariant>,
    },

    // One variant of an enum, standing on its own. It is reached through the
    // enum -- `Color::Red` -- and an import may also bring the name in by
    // itself, which is what this is for; `of` is the enum it belongs to, since
    // by then there is nothing else left to say so.
    Variant {
        of:      Name,
        payload: Payload,
    },

    // A trait, and the names it demands. The members are fns and nothing else,
    // so what is held is their names: what each one *is* is a `Function` of its
    // own, found in the trait's own scope.
    Trait {
        generics: Vec<Generic>,
        members:  Vec<Name>,
    },

    // `type Pair<T> = (T, T)`. A name for a type and not a type: it makes
    // nothing new, and once this has been followed there is nothing left of it
    // (section 2).
    TypeAlias {
        generics: Vec<Generic>,
        ty:       TyId,
    },

    // A namespace, and a file besides -- a file is a module and a namespace
    // nests another inside the one it is written in, so the two are reached the
    // same way and there is one thing here for both (section 1). What it holds
    // is the names it declares; what each of those is, its own scope says.
    Namespace(Vec<Name>),

    // A generic parameter, the `T` of `fn f<T: Ord>`. It names a type without
    // being one, which is the whole of why it is not a `TypeAlias`: what it
    // stands for is settled at the call and not at the declaration.
    TypeParam {
        bounds: Vec<Name>,
    },

    // A lifetime parameter, the `'a` of `fn f<'a>`. The `~` was the lexer's and
    // the name is what is left, so it is a name in a scope like any other --
    // which is what a `'a: 'b` needs it to be.
    Lifetime {
        bounds: Vec<Name>,
    },
}

// A generic parameter as declared. The two kinds share one list because the
// grammar's does: `<'a, T: Show + 'a>` interleaves them, and whether that is
// allowed is a rule about a declaration rather than a shape a declaration has.
//
// A bound is a `Name` and not a `Type`: what stands on the right of the colon
// is a trait or a lifetime, and `Type` names neither.
#[derive(Debug, Clone, PartialEq)]
pub enum Generic {
    Type { name: Name, bounds: Vec<Name> },
    Life { name: Name, bounds: Vec<Name> },
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
}

// What a variant carries. Four and not three: `D = 4` carries no fields and is
// still not `None`, the number being the variant's own. One enum here says what
// the grammar spells as a payload hanging off an option, and leaves no fifth
// state for anything below to handle.
#[derive(Debug, Clone, PartialEq)]
pub enum Payload {
    // `A`
    None,
    // `B(i32, str)`, reached by number.
    Tuple(Vec<TyId>),
    // `C { x: i32 }`, reached by name.
    Named(Vec<Field>),
    // `D = 4`. The value is worked out at compile time, and there is nothing
    // here to hold one with yet -- see the note at the foot of this file.
    Discriminant,
}
// ---- What is still open ---------------------------------------------------
// Two things.
//
//   - A discriminant has nowhere to keep its value. `D = 4` is a <const_expr>
//     and evaluating one is the checker's, so `Payload::Discriminant` carries
//     nothing until there is something to carry -- a const value, which no pass
//     here produces yet.
//   - A `TyId` is a handle and nothing here owns the arena it points into. The
//     pass that fills these in owns it, and what it is filling is the `types`
//     of a `TTIRProgram`: one arena for the suite and not one per file, since
//     `Ty::Named` names an item of that same program and two files sharing a
//     type have to share the handle for it.

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
//     namespace nests another inside it (section 1), and a method's segments
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
// What every mangled name opens with: `__` because nothing written in the
// language may begin with it, and `F` because this one is a function.
const FN_PREFIX: &str = "__F";

pub struct Mangler {
    // The segments each item is declared under, by item. Empty for an item at
    // the top of the root module, and for one nothing reaches.
    paths: Vec<Vec<Name>>,
}

impl Mangler {
    pub fn new(p: &TTIRProgram) -> Mangler {
        let mut m = Mangler { paths: vec![Vec::new(); p.items.len()] };
        m.nest(&p.roots, &[], p);
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

        let mut out = String::from(FN_PREFIX);
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

    // A type as one part of a symbol writes it. The language's own spelling,
    // with the whitespace it does not need taken out: it is one part however
    // many characters it runs to, so nothing inside it has to be told apart
    // from anything outside it.
    pub fn spell(&self, id: TyId, p: &TTIRProgram) -> String {
        match &p.types[id] {
            Ty::Prim(prim) => prim_name(*prim).to_string(),

            Ty::Named { item, args } => {
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

            Ty::Fn { params, ret, is_unsafe } => format!(
                "{}fn({}):{}",
                if *is_unsafe { "unsafe " } else { "" },
                self.spell_all(params, p),
                self.spell(*ret, p)
            ),

            // By its place and not by its name: `f<T>(x: T)` and `f<U>(x: U)`
            // are one function written twice, and a symbol that told them apart
            // would be telling apart what a caller cannot.
            Ty::Param { index, .. } => format!("${}", index),

            // Nothing is compiled out of a program that did not type, so a fn
            // being named cannot hold one of these.
            Ty::Error => panic!("a type that was never worked out reached the mangler"),
        }
    }

    fn spell_all(&self, ids: &[TyId], p: &TTIRProgram) -> String {
        ids.iter().map(|&i| self.spell(i, p)).collect::<Vec<_>>().join(",")
    }

    // ---- Where an item is declared ---------------------------------------

    // Down through the namespaces, which is where a declaration can stand.
    fn nest(&mut self, items: &[TTIRItemId], at: &[Name], p: &TTIRProgram) {
        for &id in items {
            self.paths[id] = at.to_vec();
            if let TTIRItemKind::Namespace { name, items, .. } = &p.items[id].kind {
                let mut inner = at.to_vec();
                inner.push(name.clone());
                self.nest(items, &inner, p);
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
                    at.push(self.spell(*ty, p));
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
