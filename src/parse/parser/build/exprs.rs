// Expressions: the precedence ladder, and everything that is an operand.
// One arm per rule, in the tables' order; `None` where the rule belongs to
// another group. See build.rs.

use super::*;

impl Parser {
    pub(super) fn build_exprs(
        &mut self,
        rule_id: tables::RuleId,
        c: &[ASTNodeId],
    ) -> Option<ASTNode> {
        Some(match rule_id {
            // ---- Type arguments ------------------------------------------
            // Built around a HOLE: what these are the arguments of reduces
            // after them, and `with_base` fills it in.
            // <type_args> -> GENERIC_LT <generic_arg_list> >
            373 => self.at(
                ASTNodeKind::TypeArgs { base: HOLE, args: self.list(c[1]) },
                c[0],
            ),
            // <postfix_op> -> <type_args>
            290 => self.pass(c[0]),

            // ---- Macros --------------------------------------------------
            // <macro_call> -> MACRO_NAME ( <arg_list_opt> )
            224 => {
                let name = self.text(c[0]);
                self.at(ASTNodeKind::MacroCall { name, args: self.list(c[2]) }, c[0])
            }
            // <primary> -> <macro_call>
            297 => self.pass(c[0]),
            // A `$x` is already its own leaf, in all three of the places it may
            // stand: an operand here, a base type, and a pattern.
            // <primary> -> MACRO_PARAM
            298 => self.pass(c[0]),

            // ---- Assignment ----------------------------------------------
            // <assign_op> -> =
            18 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Set)), c[0]),
            // <assign_op> -> +=
            19 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Add)), c[0]),
            // <assign_op> -> -=
            20 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Sub)), c[0]),
            // <assign_op> -> *=
            21 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Mul)), c[0]),
            // <assign_op> -> /=
            22 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Div)), c[0]),
            // <assign_op> -> &=
            23 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::And)), c[0]),
            // <assign_op> -> |=
            24 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Or)), c[0]),
            // <assign_op> -> ^=
            25 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Xor)), c[0]),
            // <assign_op> -> <<=
            26 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Shl)), c[0]),
            // <assign_op> -> >>=
            27 => self.at(ASTNodeKind::Mark(ASTMark::Assign(ASTAssignOp::Shr)), c[0]),
            // <assignment> -> <range_expr>
            28 => self.pass(c[0]),
            // <assignment> -> <range_expr> <assign_op> <value_expr>
            29 => {
                let op = assign_of(self.mark(c[1]));
                self.at(ASTNodeKind::Assign { op, target: c[0], value: c[2] }, c[0])
            }

            // ---- Ranges --------------------------------------------------
            // Either end may be missing, and the four rules below are the four
            // ways to write that.
            // <range_expr> -> <logical_or>
            324 => self.pass(c[0]),
            // <range_expr> -> <logical_or> <range_op>
            325 => {
                let op = range_of(self.mark(c[1]));
                self.at(ASTNodeKind::Range { op, start: Some(c[0]), end: None }, c[0])
            }
            // <range_expr> -> <logical_or> <range_op> <logical_or>
            326 => {
                let op = range_of(self.mark(c[1]));
                self.at(
                    ASTNodeKind::Range { op, start: Some(c[0]), end: Some(c[2]) },
                    c[0],
                )
            }
            // <range_expr> -> <range_op>
            327 => {
                let op = range_of(self.mark(c[0]));
                self.at(ASTNodeKind::Range { op, start: None, end: None }, c[0])
            }
            // <range_expr> -> <range_op> <logical_or>
            328 => {
                let op = range_of(self.mark(c[0]));
                self.at(ASTNodeKind::Range { op, start: None, end: Some(c[1]) }, c[0])
            }
            // <range_op> -> ..
            329 => self.at(ASTNodeKind::Mark(ASTMark::Range(ASTRangeOp::Exclusive)), c[0]),
            // <range_op> -> ..=
            330 => self.at(ASTNodeKind::Mark(ASTMark::Range(ASTRangeOp::Inclusive)), c[0]),
            // <range_pattern> -> <literal_pattern> <range_op> <literal_pattern>
            331 => {
                let op = range_of(self.mark(c[1]));
                self.at(ASTNodeKind::RangePat { op, lo: c[0], hi: c[2] }, c[0])
            }

            // ---- Logic ---------------------------------------------------
            // <logical_and> -> <equality>
            218 => self.pass(c[0]),
            // <logical_and> -> <logical_and> && <equality>
            219 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::And, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <logical_or> -> <logical_xor>
            220 => self.pass(c[0]),
            // <logical_or> -> <logical_or> || <logical_xor>
            221 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::Or, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <logical_xor> -> <logical_and>
            222 => self.pass(c[0]),
            // <logical_xor> -> <logical_xor> ^^ <logical_and>
            223 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::Xor, lhs: c[0], rhs: c[2] },
                c[0],
            ),

            // ---- Bitwise -------------------------------------------------
            // The operator is the rule rather than a mark of its own: there is
            // one spelling apiece, so there is nothing for a `<..._op>` rule to
            // tell the arm that the arm does not already know.
            // <bit_and> -> <shift>
            50 => self.pass(c[0]),
            // <bit_and> -> <bit_and> & <shift>
            51 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitAnd, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <bit_or> -> <bit_xor>
            52 => self.pass(c[0]),
            // <bit_or> -> <bit_or> | <bit_xor>
            53 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitOr, lhs: c[0], rhs: c[2] },
                c[0],
            ),
            // <bit_xor> -> <bit_and>
            54 => self.pass(c[0]),
            // <bit_xor> -> <bit_xor> ^ <bit_and>
            55 => self.at(
                ASTNodeKind::Binary { op: ASTBinOp::BitXor, lhs: c[0], rhs: c[2] },
                c[0],
            ),

            // ---- Equality ------------------------------------------------
            // <equality> -> <comparison>
            113 => self.pass(c[0]),
            // <equality> -> <equality> <equality_op> <comparison>
            114 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <equality_op> -> ==
            115 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Eq)), c[0]),
            // <equality_op> -> !=
            116 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Ne)), c[0]),

            // ---- Comparison ----------------------------------------------
            // <comparison> -> <bit_or>
            80 => self.pass(c[0]),
            // <comparison> -> <comparison> <comparison_op> <bit_or>
            81 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <comparison_op> -> <
            82 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Lt)), c[0]),
            // <comparison_op> -> >
            83 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Gt)), c[0]),
            // <comparison_op> -> <=
            84 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Le)), c[0]),
            // <comparison_op> -> >=
            85 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Ge)), c[0]),

            // ---- Shifts --------------------------------------------------
            // <shift> -> <additive>
            346 => self.pass(c[0]),
            // <shift> -> <shift> <shift_op> <additive>
            347 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <shift_op> -> <<
            348 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Shl)), c[0]),
            // <shift_op> -> >>
            349 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Shr)), c[0]),

            // ---- Arithmetic ----------------------------------------------
            // <additive> -> <multiplicative>
            2 => self.pass(c[0]),
            // <additive> -> <additive> <additive_op> <multiplicative>
            3 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <additive_op> -> +
            4 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Add)), c[0]),
            // <additive_op> -> -
            5 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Sub)), c[0]),

            // ---- Multiplication ------------------------------------------
            // <multiplicative> -> <cast>
            249 => self.pass(c[0]),
            // <multiplicative> -> <multiplicative> <multiplicative_op> <cast>
            250 => {
                let op = bin_of(self.mark(c[1]));
                self.at(ASTNodeKind::Binary { op, lhs: c[0], rhs: c[2] }, c[0])
            }
            // <multiplicative_op> -> *
            251 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Mul)), c[0]),
            // <multiplicative_op> -> /
            252 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Div)), c[0]),
            // <multiplicative_op> -> %
            253 => self.at(ASTNodeKind::Mark(ASTMark::Bin(ASTBinOp::Rem)), c[0]),

            // ---- Casts ---------------------------------------------------
            // <cast> -> <unary>
            64 => self.pass(c[0]),
            // <cast> -> <cast> as <cast_type>
            65 => self.at(ASTNodeKind::Cast { value: c[0], ty: c[2] }, c[0]),
            // <cast_base> -> <primitive_type>
            66 => self.pass(c[0]),
            // <cast_base> -> <qualified_name>
            // A name in a cast is a type, and a type names itself with `Named`
            // rather than with the `Name` an expression would have built.
            67 => self.at(ASTNodeKind::Named { path: self.path(c[0]), args: Vec::new() }, c[0]),
            // <cast_base> -> <grouped_type>
            68 => self.pass(c[0]),
            // <cast_base> -> <tuple_type>
            69 => self.pass(c[0]),
            // <cast_base> -> _
            70 => self.at(ASTNodeKind::Infer, c[0]),
            // <cast_type> -> <ref_op> <cast_type>
            // A cast names no lifetime: `<cast_type>` is the smaller language
            // of section 3, and nothing has asked to say one here yet.
            71 => {
                let op = ref_of(self.mark(c[0]));
                self.at(ASTNodeKind::RefType { op, life: None, inner: c[1] }, c[0])
            }
            // <cast_type> -> ptr <cast_type>
            72 => self.at(ASTNodeKind::PtrType(c[1]), c[0]),
            // <cast_type> -> <cast_base> <array_suffix_list>
            73 => self.fold_suffixes(c[0], c[1]),

            // ---- Unary ---------------------------------------------------
            // <unary> -> <unary_op> <unary>
            384 => {
                let op = unary_of(self.mark(c[0]));
                self.at(ASTNodeKind::Unary { op, operand: c[1] }, c[0])
            }
            // <unary> -> <postfix>
            385 => self.pass(c[0]),
            // <unary_op> -> !
            386 => self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Not)), c[0]),
            // <unary_op> -> -
            387 => self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Neg)), c[0]),
            // <unary_op> -> <ref_op>
            // `&x` and `*x` take a reference; neither dereferences, so the
            // same two spellings mean here what they mean in a type.
            388 => {
                let op = ref_of(self.mark(c[0]));
                self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Ref(op))), c[0])
            }
            // <unary_op> -> addr
            389 => self.at(ASTNodeKind::Mark(ASTMark::Unary(ASTUnaryOp::Addr)), c[0]),

            // ---- Postfix -------------------------------------------------
            // Each suffix was built around a HOLE; this is where it is given
            // the expression it was written after.
            // <postfix> -> <primary>
            283 => self.pass(c[0]),
            // <postfix> -> <postfix> <postfix_op>
            284 => self.with_base(c[1], c[0]),
            // <postfix_op> -> . IDENTIFIER
            285 => {
                let name = self.text(c[1]);
                self.at(ASTNodeKind::Field { base: HOLE, name }, c[0])
            }
            // <postfix_op> -> . INT_LITERAL
            // The same `.`, reaching into a tuple: a member there is counted
            // and not named, so what follows the dot is the number.
            286 => self.at(
                ASTNodeKind::TupleIndex { base: HOLE, index: self.index(c[1]) },
                c[0],
            ),
            // <postfix_op> -> :: <path_seg>
            287 => {
                let name = self.text(c[1]);
                self.at(ASTNodeKind::Path { base: HOLE, name }, c[0])
            }
            // <postfix_op> -> ( <arg_list_opt> )
            288 => self.at(
                ASTNodeKind::Call { callee: HOLE, args: self.list(c[1]) },
                c[0],
            ),
            // <postfix_op> -> [ <index> ]
            289 => self.at(ASTNodeKind::Index { base: HOLE, index: c[1] }, c[0]),
            // <postfix_op> -> <struct_literal_tail>
            291 => self.pass(c[0]),

            // ---- Primaries -----------------------------------------------
            // <primary> -> <literal> | self | IDENTIFIER | <array_literal>
            //           |  <map_literal> | <set_literal> | <grouping>
            //           |  <tuple_expr>
            292 | 293 | 296 | 299 | 300 | 301 | 302 | 303 => self.pass(c[0]),
            // A root is the base of the `::` chain that follows it, and a base
            // is a name: what tells this one from a name someone wrote is that
            // no one can write it. Which module it stands for is the resolver's.
            // <primary> -> super
            294 => self.at(ASTNodeKind::Ident("super".to_string()), c[0]),
            // <primary> -> suite
            295 => self.at(ASTNodeKind::Ident("suite".to_string()), c[0]),

            // ---- Grouping ------------------------------------------------
            // Parentheses are gone from the tree: what they said about
            // precedence the shape now says.
            // <grouped_type> -> ( <type> )
            171 => self.pass(c[1]),
            // <grouping> -> ( <expression> )
            172 => self.pass(c[1]),

            // ---- Call arguments ------------------------------------------
            // <arg_list> -> <expression_seq>
            6 => self.pass(c[0]),
            // <arg_list> -> <expression_seq> ,
            7 => self.pass(c[0]),
            // <arg_list_opt> -> ε
            8 => self.here(ASTNodeKind::List(Vec::new())),
            // <arg_list_opt> -> <arg_list>
            9 => self.pass(c[0]),

            // ---- Indexing and initializers -------------------------------
            // <index> -> <expression>
            195 => self.pass(c[0]),
            // <initializer_opt> -> ε
            196 => self.here(ASTNodeKind::Empty),
            // <initializer_opt> -> = <expression>
            197 => self.pass(c[1]),

            // ---- Closures ------------------------------------------------
            // <closure_expr> -> <move_opt> | <closure_param_list_opt> | <value_expr>
            74 => {
                let is_move = matches!(self.kind(c[0]), ASTNodeKind::Mark(ASTMark::Move));
                // Where `move` was not written the closure begins at its first
                // `|`, the ε node having nowhere of its own to stand.
                let anchor = if is_move { c[0] } else { c[1] };
                self.at(
                    ASTNodeKind::Closure { is_move, params: self.list(c[2]), body: c[4] },
                    anchor,
                )
            }
            // <closure_param> -> <binding_name> <type_annotation_opt>
            75 => self.at(
                ASTNodeKind::Param { name: self.binding(c[0]), ty: self.opt(c[1]) },
                c[0],
            ),
            // <closure_param_list> -> <closure_param>
            76 => self.one(c[0]),
            // <closure_param_list> -> <closure_param_list> , <closure_param>
            77 => self.grew(c[0], c[2]),
            // <closure_param_list_opt> -> ε
            78 => self.here(ASTNodeKind::List(Vec::new())),
            // <closure_param_list_opt> -> <closure_param_list>
            79 => self.pass(c[0]),

            // ---- Closures, continued -------------------------------------
            // <move_opt> -> ε
            247 => self.here(ASTNodeKind::Empty),
            // <move_opt> -> move
            248 => self.at(ASTNodeKind::Mark(ASTMark::Move), c[0]),

            // ---- Jumps ---------------------------------------------------
            // <jump_expr> -> return <expression_opt>
            203 => self.at(ASTNodeKind::Return(self.opt(c[1])), c[0]),
            // <jump_expr> -> break <expression_opt>
            204 => self.at(ASTNodeKind::Break(self.opt(c[1])), c[0]),
            // <jump_expr> -> continue
            205 => self.at(ASTNodeKind::Continue, c[0]),

            // ---- Literals ------------------------------------------------
            // The leaf a shift built already holds the value: <literal> only
            // says that one may stand where an expression may.
            // <literal> -> INT_LITERAL | FLOAT_LITERAL | STRING_LITERAL
            //           |  CHAR_LITERAL | true | false | null
            209 | 210 | 211 | 212 | 213 | 214 | 215 => self.pass(c[0]),
            // <literal_pattern> -> <literal>
            216 => self.at(ASTNodeKind::LitPat { negated: false, value: self.lit(c[0]) }, c[0]),
            // <literal_pattern> -> - <literal>
            217 => self.at(ASTNodeKind::LitPat { negated: true, value: self.lit(c[1]) }, c[0]),

            // ---- Values --------------------------------------------------
            // <value_expr> -> <assignment> | <closure_expr> | <block_expr>
            402 | 403 | 404 => self.pass(c[0]),

            // ---- Names ---------------------------------------------------
            // A segment is a name whatever spelled it, so a path stays a list of
            // strings and a root is the string it was written with. No one can
            // write these three as a name, which is what keeps them apart from
            // one without a node to say so.
            // <path_seg> -> IDENTIFIER
            265 => self.pass(c[0]),
            // <path_seg> -> suite
            266 => self.at(ASTNodeKind::Ident("suite".to_string()), c[0]),
            // <path_seg> -> super
            267 => self.at(ASTNodeKind::Ident("super".to_string()), c[0]),
            // <path_seg> -> self
            268 => self.at(ASTNodeKind::Ident("self".to_string()), c[0]),

            // <qualified_name> -> <path_seg>
            322 => self.at(ASTNodeKind::Name(vec![self.text(c[0])]), c[0]),
            // <qualified_name> -> <qualified_name> :: <path_seg>
            323 => {
                let mut segments = self.path(c[0]);
                segments.push(self.text(c[2]));
                self.at(ASTNodeKind::Name(segments), c[0])
            }

            // ---- Expressions and statements ------------------------------
            // <expr_stmt> -> <expression> ;
            117 => self.at(ASTNodeKind::ExprStmt(c[0]), c[0]),
            // <expression> -> <value_expr> | <jump_expr>
            118 | 119 => self.pass(c[0]),
            // <expression_opt> -> ε
            120 => self.here(ASTNodeKind::Empty),
            // <expression_opt> -> <expression>
            121 => self.pass(c[0]),
            // <expression_seq> -> <expression>
            122 => self.one(c[0]),
            // <expression_seq> -> <expression_seq> , <expression>
            123 => self.grew(c[0], c[2]),

            _ => return None,
        })
    }
}
