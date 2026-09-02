// What a value is worked out from: a literal, a name of a declaration, an
// operator over one or two of them, and a cast.
//
// The only thing here that takes any deciding is which instruction an operator
// becomes. The source has one `/`, one `>>` and one `<`; a machine has two of
// each, and which one is meant is the operands' type. That is settled here and
// written into the instruction, so nothing downstream ever has to find a type
// again to know what an instruction does -- which is the whole reason
// `MIRBinOp` is longer than `TIRBinOp`.

use crate::sir::sir_nodes::*;
use crate::tir::tir_nodes::{TIRBinOp, TIRLit, TIRRefOp, TIRUnaryOp};
use crate::tir::ttir_nodes::Ty;

use super::super::mir_nodes::*;
use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn value(&mut self, inst: &SIRInst, at: SIRBlockId, i: usize) {
        let (line, col) = (inst.line, inst.col);
        let Some(value) = inst.def else { return };
        let def = self.of(value);

        match &inst.kind {
            SIRInstKind::Literal(lit) => self.literal(def, lit, line, col),

            // A declaration named as a value. `mono` worked out which instance
            // that is, so what stands here is a symbol and the instruction is
            // the address of it.
            //
            // Unless the only thing done with it is call it, in which case the
            // call names the symbol and this address is read by nothing. The
            // register it was given is left unwritten, which is allowed: what
            // has to be made is what is read.
            SIRInstKind::Item(_) => {
                if self.only_called(value) {
                    return;
                }
                let name = self.symbol_at(at, i).unwrap_or_default();
                // A fn named as a value is the *pair* a fn value is, and not
                // the address of its code. `mir::layout` calls a `fn` fat --
                // where the code is, and where the captures are -- and a
                // closure builds both words (`calls::closure`). A plain fn has
                // no captures, so its second word is nothing, but the pair
                // still has to be there: everything that reads a fn value
                // reads the first word out of it, and a bare code address read
                // that way hands back the first eight bytes of the *machine
                // code* and calls them.
                //
                // Nothing caught it because a call of a fn known here is
                // inlined or named directly; it takes a fn value that reached
                // its caller through a parameter or a field, which is what a
                // comparator is.
                if matches!(self.made.ttir.types.get(self.ty_of(value)), Some(Ty::Fn { .. }))
                {
                    self.paired(def, name, line, col);
                    return;
                }
                self.making(def, MIRInstKind::Symbol(name), line, col);
            }

            // `self` is the first parameter and has been since the signature
            // was lowered. There is nothing to work out.
            SIRInstKind::SelfValue => match self.receiver() {
                Some(held) => self.making(def, MIRInstKind::Move(held), line, col),
                None => self.making(def, MIRInstKind::Undef, line, col),
            },

            SIRInstKind::Unary { op, operand } => {
                self.unary(def, *op, *operand, value, line, col)
            }

            SIRInstKind::Binary { op, lhs, rhs } => {
                self.binary(def, *op, *lhs, *rhs, line, col)
            }

            SIRInstKind::Cast(of) => {
                let from = self.ty_of(*of);
                let to = self.ty_of(value);
                let (from, to) = (self.scalar_of(from), self.scalar_of(to));
                let of = self.of(*of);
                self.making(def, MIRInstKind::Convert { of, from, to }, line, col);
            }

            _ => self.making(def, MIRInstKind::Undef, line, col),
        }
    }

    // ---- Literals ----------------------------------------------------------

    fn literal(&mut self, def: MIRRegId, lit: &TIRLit, line: usize, col: usize) {
        // The one literal that is not one instruction. `str` is fat -- a
        // pointer and a length -- everywhere else in the compiler, so a
        // literal that was only the pointer would be the one `str` in the
        // language with nothing beside it, and anything reading the length
        // would read whatever was next in the frame.
        if let TIRLit::Str(text) = lit {
            let text = text.clone();
            self.text(def, &text, line, col);
            return;
        }
        let kind = match lit {
            TIRLit::Int(n) => MIRInstKind::Const(MIRConst::Int(*n)),
            TIRLit::Float(n) => MIRInstKind::Const(MIRConst::Float(*n)),
            // A boolean is a nought or a one. Nothing downstream tells it from
            // a one-byte number, which is what makes `!` a comparison below
            // rather than a complement.
            TIRLit::Bool(b) => MIRInstKind::Const(MIRConst::Int(i64::from(*b))),
            // A `char` is a Unicode scalar value, which is a number.
            TIRLit::Char(c) => MIRInstKind::Const(MIRConst::Int(*c as i64)),
            // `null` carries no information, so any bits will do and nought is
            // the ones a reader expects.
            TIRLit::Null => MIRInstKind::Const(MIRConst::Int(0)),
            // Built above, because it is two stores and not one value.
            TIRLit::Str(_) => MIRInstKind::Undef,
        };
        self.making(def, kind, line, col);
    }

    // A string literal: the bytes in the pool, and a pair in the frame holding
    // where they are and how many there are.
    //
    // The pair and not just the pointer, because that is what a `str` is
    // everywhere else -- `layout` calls it fat and `indirect` therefore says a
    // register holding one holds its address. A literal that made only the
    // pointer would arrive at a map's key as a bare address while a `str` from
    // a variable arrived as a pair, and the two would not compare equal
    // however identical the characters were.
    fn text(&mut self, def: MIRRegId, held: &str, line: usize, col: usize) {
        let symbol = self.pooled(held.as_bytes().to_vec());
        let word = self.word();
        let name = format!("${}", self.frame_len());
        let slot = self.slot(name, word * 2, word);
        self.making(def, MIRInstKind::Frame(slot), line, col);

        let at = self.push(MIRInstKind::Symbol(symbol), line, col);
        self.effect(MIRInstKind::Store { to: def, value: at, bytes: word }, line, col);
        let len = self.push(MIRInstKind::Const(MIRConst::Int(held.len() as i64)), line, col);
        let second =
            self.push(MIRInstKind::Offset { base: def, bytes: word as i64 }, line, col);
        self.effect(MIRInstKind::Store { to: second, value: len, bytes: word }, line, col);
    }

    // ---- One operand -------------------------------------------------------

    fn unary(
        &mut self,
        def: MIRRegId,
        op: TIRUnaryOp,
        operand: SIRValueId,
        value: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(operand);
        let held = self.of(operand);
        match op {
            TIRUnaryOp::Neg => {
                let op = if self.floating(ty) { MIRUnOp::FNeg } else { MIRUnOp::Neg };
                self.making(def, MIRInstKind::Un { op, operand: held }, line, col);
            }
            // `!` over a boolean is "is it nought", and over an integer it is
            // every bit turned over. The two are different instructions and the
            // type is what says which -- a boolean holding 1 complemented would
            // be -2, which is not `false`.
            TIRUnaryOp::Not => {
                if self.is_bool(ty) {
                    let zero = self.push(MIRInstKind::Const(MIRConst::Int(0)), line, col);
                    self.making(
                        def,
                        MIRInstKind::Cmp { op: MIRCmpOp::Eq, lhs: held, rhs: zero },
                        line,
                        col,
                    );
                } else {
                    self.making(
                        def,
                        MIRInstKind::Un { op: MIRUnOp::Not, operand: held },
                        line,
                        col,
                    );
                }
            }
            // `&x` and `*x` both take a reference -- which of the two says how
            // much may be done through it, and that was `sema`'s question and
            // is settled. `addr x` is the same address as a `ptr`.
            //
            // All three are the address of a place, and the operand already is
            // one: anything whose address is taken is in a slot, which is what
            // `sir::promote` leaves behind. So taking it is naming it.
            TIRUnaryOp::Ref(TIRRefOp::Imm)
            | TIRUnaryOp::Ref(TIRRefOp::Mut)
            | TIRUnaryOp::Addr => {
                let _ = value;
                self.making(def, MIRInstKind::Move(held), line, col);
            }

            // `sir::lower` makes a `Load` of this and not a `Unary`, so
            // nothing reaches here from a compiled program -- see that file
            // for why it must not. A body built by hand still can, and what it
            // means is the same read.
            TIRUnaryOp::Deref => {
                let want = self.ty_of(value);
                self.take(def, held, want, line, col);
            }
        }
    }

    // ---- Two operands ------------------------------------------------------

    fn binary(
        &mut self,
        def: MIRRegId,
        op: TIRBinOp,
        lhs: SIRValueId,
        rhs: SIRValueId,
        line: usize,
        col: usize,
    ) {
        let ty = self.ty_of(lhs);
        let float = self.floating(ty);
        let signed = self.signed_ty(ty);
        let (a, b) = (self.of(lhs), self.of(rhs));

        if let Some(op) = compare(op, float, signed) {
            self.making(def, MIRInstKind::Cmp { op, lhs: a, rhs: b }, line, col);
            return;
        }
        let op = arithmetic(op, float, signed);
        self.making(def, MIRInstKind::Bin { op, lhs: a, rhs: b }, line, col);
    }

    fn is_bool(&mut self, ty: crate::tir::ttir_nodes::TyId) -> bool {
        matches!(
            crate::sir::target::prim(&self.made.ttir, ty),
            Some(crate::tir::tir_nodes::TIRPrim::Bool)
        )
    }
}

// The orderings, where the operator is one. Equality is one instruction over
// integers however they are signed -- the bits are the bits -- and the four
// orderings are two instructions each, which is the whole of the difference.
fn compare(op: TIRBinOp, float: bool, signed: bool) -> Option<MIRCmpOp> {
    use MIRCmpOp::*;
    use TIRBinOp as B;
    Some(match (op, float, signed) {
        (B::Eq, true, _) => FEq,
        (B::Ne, true, _) => FNe,
        (B::Lt, true, _) => FLt,
        (B::Le, true, _) => FLe,
        (B::Gt, true, _) => FGt,
        (B::Ge, true, _) => FGe,
        (B::Eq, false, _) => Eq,
        (B::Ne, false, _) => Ne,
        (B::Lt, false, true) => SLt,
        (B::Le, false, true) => SLe,
        (B::Gt, false, true) => SGt,
        (B::Ge, false, true) => SGe,
        (B::Lt, false, false) => ULt,
        (B::Le, false, false) => ULe,
        (B::Gt, false, false) => UGt,
        (B::Ge, false, false) => UGe,
        _ => return None,
    })
}

// And the rest. `And`, `Or` and `Xor` over booleans are the bitwise ones over a
// nought and a one, which is the same instruction and the reason the logical
// three are not separate here -- `&&` and `||` never reach this at all, having
// been branches since the GIR.
fn arithmetic(op: TIRBinOp, float: bool, signed: bool) -> MIRBinOp {
    use MIRBinOp::*;
    use TIRBinOp as B;
    match (op, float) {
        (B::Add, true) => FAdd,
        (B::Sub, true) => FSub,
        (B::Mul, true) => FMul,
        (B::Div, true) => FDiv,
        (B::Add, false) => Add,
        (B::Sub, false) => Sub,
        (B::Mul, false) => Mul,
        (B::Div, false) => {
            if signed {
                SDiv
            } else {
                UDiv
            }
        }
        (B::Rem, false) => {
            if signed {
                SRem
            } else {
                URem
            }
        }
        (B::Shl, _) => Shl,
        // Bringing in noughts or bringing in the sign, which is the operand's
        // signedness and not the shift's.
        (B::Shr, _) => {
            if signed {
                AShr
            } else {
                LShr
            }
        }
        (B::BitAnd, _) | (B::And, _) => And,
        (B::BitOr, _) | (B::Or, _) => Or,
        (B::BitXor, _) | (B::Xor, _) => Xor,
        // A float has no remainder instruction on either machine here, and the
        // orderings never reach this. Neither is a shape the checker makes.
        (B::Rem, true) => FDiv,
        (B::Eq, _) | (B::Ne, _) | (B::Lt, _) | (B::Le, _) | (B::Gt, _) | (B::Ge, _) => Add,
    }
}
