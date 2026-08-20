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

use crate::tir::tir_nodes::TIRVis;
use crate::tir::ttir_nodes::TyId;

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
