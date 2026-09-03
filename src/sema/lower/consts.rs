// What a constant is worth, worked out where it is written.
//
// A `const` is the compile-time constant (§1), which is a promise about *when*
// its value is known rather than about what may be done with it. Nothing had
// been keeping that promise: `resolve` read a value off a const whose
// initialiser was written as a bare literal and read nothing off any other, so
// `const N: i64 = 42` folded and `const N: i64 = 6 * 7` did not -- and what did
// not fold was compiled into a reference to a symbol nobody defines, which the
// program only found out about at the link step. §8 called this out and asked
// for "an evaluator for <const_expr>, so a constant folds whatever it was
// written as". This is that.
//
// **It runs on the TIR and not the typed tree**, which is the one surprising
// thing here and is forced. `TTIRItemKind::Const` holds a `value` field that
// nothing fills, so by the time there are types there is no initialiser left
// to read; the expression is still in hand in `resolve`, and that is where
// this is called from. What comes back is a `TIRLit`, which is what
// `paths::const_lit` already knew how to put at a use.
//
// **The arithmetic is done in `i64` and `f64` and nowhere else.** A const has a
// declared type and the literal takes it on at the use, so what is worked out
// here is the value and not its width -- exactly as `const_lit`'s comment
// already says: "the type is the const's declared one and not the literal's".
// A value too big for what it was declared as is a question nothing in this
// compiler asks yet, of a const or of a plain literal, and asking it here alone
// would be answering it in one place out of two.
//
// **What is refused is refused by giving nothing back.** Every caller already
// has an answer for a const it cannot read -- a use stays a symbol -- so an
// evaluator that reported its own diagnostics would be reporting them for
// programs that are not wrong, only ones written with something this cannot
// yet do.

use crate::tir::tir_nodes::*;

use super::Lowerer;

// The three kinds of answer an operator here works on. A `TIRLit` holds
// strings and null besides, and neither is a thing arithmetic is done to.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl Value {
    fn lit(self) -> TIRLit {
        match self {
            Value::Int(n) => TIRLit::Int(n),
            Value::Float(n) => TIRLit::Float(n),
            Value::Bool(b) => TIRLit::Bool(b),
        }
    }
}

impl Lowerer<'_> {
    // A constant expression's value, or nothing where it is not one.
    //
    // `depth` is not a recursion guard for a cycle -- `const A = B` and
    // `const B = A` cannot both be in `self.consts` before either is worked
    // out, so a cycle simply fails to fold -- but for the expression itself,
    // which is a tree a person wrote and can be nested as deeply as they had
    // patience for.
    pub(super) fn const_value(&self, at: TIRExprId, depth: usize) -> Option<TIRLit> {
        Some(self.eval(at, depth)?.lit())
    }

    fn eval(&self, at: TIRExprId, depth: usize) -> Option<Value> {
        if depth > 64 {
            return None;
        }
        match &self.tir.exprs.get(at)?.kind {
            TIRExprKind::Literal { value, .. } => match value {
                TIRLit::Int(n) => Some(Value::Int(*n)),
                TIRLit::Float(n) => Some(Value::Float(*n)),
                TIRLit::Bool(b) => Some(Value::Bool(*b)),
                // A character is a number the moment it is operated on, and
                // `'a' as i64` is how one is written where a number is wanted.
                TIRLit::Char(c) => Some(Value::Int(*c as i64)),
                // A string is bytes and null is no news; neither is arithmetic.
                TIRLit::Str(_) | TIRLit::Null => None,
            },

            // A name standing for a const that is already worked out. Only
            // backwards: `self.consts` holds what has been read so far, so a
            // const naming one declared below it does not fold. That is the
            // declaration order a reader writes anyway, and the alternative is
            // a fixed point over the whole file to buy the other order.
            TIRExprKind::Name(path) => {
                let item = self.look(path.last()?)?;
                self.consts.get(&item).and_then(|held| match held {
                    TIRLit::Int(n) => Some(Value::Int(*n)),
                    TIRLit::Float(n) => Some(Value::Float(*n)),
                    TIRLit::Bool(b) => Some(Value::Bool(*b)),
                    TIRLit::Char(c) => Some(Value::Int(*c as i64)),
                    TIRLit::Str(_) | TIRLit::Null => None,
                })
            }

            TIRExprKind::Unary { op, operand } => {
                let held = self.eval(*operand, depth + 1)?;
                match (op, held) {
                    (TIRUnaryOp::Neg, Value::Int(n)) => Some(Value::Int(n.wrapping_neg())),
                    (TIRUnaryOp::Neg, Value::Float(n)) => Some(Value::Float(-n)),
                    // `!` is both the logical negation of a bool and the
                    // bitwise complement of an integer, which is how it is
                    // written everywhere else in the language.
                    (TIRUnaryOp::Not, Value::Bool(b)) => Some(Value::Bool(!b)),
                    (TIRUnaryOp::Not, Value::Int(n)) => Some(Value::Int(!n)),
                    // A reference, an address or a dereference is a place, and
                    // a place is exactly what a const has not got.
                    _ => None,
                }
            }

            TIRExprKind::Binary { op, lhs, rhs } => {
                let (a, b) = (self.eval(*lhs, depth + 1)?, self.eval(*rhs, depth + 1)?);
                binary(*op, a, b)
            }

            // A cast between numbers, which is the only cast a const can be
            // written with: the others reach a pointer or a reference.
            TIRExprKind::Cast { value, ty } => {
                let held = self.eval(*value, depth + 1)?;
                cast(held, self.prim_written(*ty)?)
            }

            _ => None,
        }
    }

    // The primitive a cast names, where it names one. A cast to anything else
    // -- a `ptr`, a reference, a named type -- is not something to fold.
    fn prim_written(&self, ty: TIRTypeId) -> Option<TIRPrim> {
        match &self.tir.types.get(ty)?.kind {
            TIRTypeKind::Prim(p) => Some(*p),
            _ => None,
        }
    }
}

// A cast's answer, which is a narrowing of the value and not of its width: what
// a `u8` holds is the checker's business and the literal that comes out of here
// carries the const's declared type anyway.
fn cast(held: Value, to: TIRPrim) -> Option<Value> {
    let number = match held {
        Value::Int(n) => n as f64,
        Value::Float(n) => n,
        Value::Bool(b) => f64::from(u8::from(b)),
    };
    match to {
        TIRPrim::F32 => Some(Value::Float(f64::from(number as f32))),
        TIRPrim::F64 => Some(Value::Float(number)),
        TIRPrim::Bool => Some(Value::Bool(number != 0.0)),
        TIRPrim::I8
        | TIRPrim::I16
        | TIRPrim::I32
        | TIRPrim::I64
        | TIRPrim::I128
        | TIRPrim::U8
        | TIRPrim::U16
        | TIRPrim::U32
        | TIRPrim::U64
        | TIRPrim::U128
        | TIRPrim::Char => Some(Value::Int(match held {
            Value::Int(n) => n,
            Value::Float(n) => n as i64,
            Value::Bool(b) => i64::from(b),
        })),
        TIRPrim::Str | TIRPrim::Null | TIRPrim::Never => None,
    }
}

// Two values and an operator.
//
// A division or a remainder by zero gives nothing back rather than a value.
// That is not this deciding what the program means: a const that divides by
// zero is a program with a mistake in it, and the mistake wants a diagnostic
// from whatever checks constants for range -- which does not exist yet. Folding
// it to something would be inventing an answer, and panicking here would take
// the compiler down over a line it could have carried on past.
fn binary(op: TIRBinOp, a: Value, b: Value) -> Option<Value> {
    // Bit patterns and shifts are integers only; a float has no bits to shift.
    if let (Value::Int(x), Value::Int(y)) = (a, b) {
        let held = match op {
            TIRBinOp::Add => Some(x.wrapping_add(y)),
            TIRBinOp::Sub => Some(x.wrapping_sub(y)),
            TIRBinOp::Mul => Some(x.wrapping_mul(y)),
            TIRBinOp::Div => (y != 0).then(|| x.wrapping_div(y)),
            TIRBinOp::Rem => (y != 0).then(|| x.wrapping_rem(y)),
            // A shift by more than the width is not folded rather than being
            // folded to nought: what a machine does with one differs between
            // the three here, and the answer a reader gets should not depend on
            // whether the compiler happened to fold it.
            TIRBinOp::Shl => (0..64).contains(&y).then(|| x.wrapping_shl(y as u32)),
            TIRBinOp::Shr => (0..64).contains(&y).then(|| x.wrapping_shr(y as u32)),
            TIRBinOp::BitAnd => Some(x & y),
            TIRBinOp::BitOr => Some(x | y),
            TIRBinOp::BitXor => Some(x ^ y),
            _ => None,
        };
        if let Some(held) = held {
            return Some(Value::Int(held));
        }
    }

    // The comparisons, which answer a bool whatever they were given.
    let ordered = |ord: std::cmp::Ordering| match op {
        TIRBinOp::Lt => Some(Value::Bool(ord.is_lt())),
        TIRBinOp::Gt => Some(Value::Bool(ord.is_gt())),
        TIRBinOp::Le => Some(Value::Bool(ord.is_le())),
        TIRBinOp::Ge => Some(Value::Bool(ord.is_ge())),
        _ => None,
    };
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => {
            if let TIRBinOp::Eq = op {
                return Some(Value::Bool(x == y));
            }
            if let TIRBinOp::Ne = op {
                return Some(Value::Bool(x != y));
            }
            if let Some(held) = ordered(x.cmp(&y)) {
                return Some(held);
            }
        }
        (Value::Bool(x), Value::Bool(y)) => {
            return match op {
                TIRBinOp::Eq => Some(Value::Bool(x == y)),
                TIRBinOp::Ne => Some(Value::Bool(x != y)),
                TIRBinOp::And => Some(Value::Bool(x && y)),
                TIRBinOp::Or => Some(Value::Bool(x || y)),
                TIRBinOp::Xor => Some(Value::Bool(x != y)),
                _ => None,
            };
        }
        _ => {}
    }

    // And the floats, where either side is one. An integer beside a float is
    // widened, which is what the checker will have made of the two anyway.
    let (x, y) = match (a, b) {
        (Value::Float(x), Value::Float(y)) => (x, y),
        (Value::Float(x), Value::Int(y)) => (x, y as f64),
        (Value::Int(x), Value::Float(y)) => (x as f64, y),
        _ => return None,
    };
    match op {
        TIRBinOp::Add => Some(Value::Float(x + y)),
        TIRBinOp::Sub => Some(Value::Float(x - y)),
        TIRBinOp::Mul => Some(Value::Float(x * y)),
        TIRBinOp::Div => Some(Value::Float(x / y)),
        TIRBinOp::Eq => Some(Value::Bool(x == y)),
        TIRBinOp::Ne => Some(Value::Bool(x != y)),
        // A comparison of two floats that are not ordered -- a NaN is beside
        // one of them -- is false, which is what every one of these machines
        // answers and what the language will have to answer too.
        TIRBinOp::Lt => Some(Value::Bool(x < y)),
        TIRBinOp::Gt => Some(Value::Bool(x > y)),
        TIRBinOp::Le => Some(Value::Bool(x <= y)),
        TIRBinOp::Ge => Some(Value::Bool(x >= y)),
        _ => None,
    }
}
