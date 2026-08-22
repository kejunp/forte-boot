// What the arms build, checked against the trees they are meant to make.

use super::*;

// Parses `source` and gives back the parser -- which is the arena -- and the
// root. A node names its children by handle, so neither half says much alone.
fn tree(source: &str) -> (Parser, ASTNode) {
    let mut p = Parser::new(lexer::Lexer::new(source));
    let root = p.parse();
    assert!(p.errors().is_empty(), "{}\n{:#?}", source, p.errors());
    (p, root)
}

// The one item of a file that has one.
fn only_item(source: &str) -> (Parser, ASTNode) {
    let (p, root) = tree(source);
    let items = match &root.kind {
        ASTNodeKind::Program(items) => items.clone(),
        other => panic!("a file built {:?}", other),
    };
    assert_eq!(items.len(), 1, "{}", source);
    let item = p.get_node(items[0]).clone();
    (p, item)
}

// The statements of `fn main`'s body, for a test about statements rather than
// about what has to be written around them.
fn statements(body: &str) -> (Parser, Vec<ASTNodeId>) {
    let source = format!("fn main() {{\n{}\n}}\n", body);
    let (p, item) = only_item(&source);
    let block = match &item.kind {
        ASTNodeKind::Fn { body: Some(id), .. } => *id,
        other => panic!("a function built {:?}", other),
    };
    let stmts = match &p.get_node(block).kind {
        ASTNodeKind::Block { stmts, .. } => stmts.clone(),
        other => panic!("a body built {:?}", other),
    };
    (p, stmts)
}

#[test]
fn a_file_is_its_items_in_order() {
    let (p, root) = tree("import a::b;\nstruct P {\n    x: i32,\n}\nfn f() {}\n");
    let items = match &root.kind {
        ASTNodeKind::Program(items) => items.clone(),
        other => panic!("a file built {:?}", other),
    };
    assert_eq!(items.len(), 3);
    assert!(matches!(p.get_node(items[0]).kind, ASTNodeKind::Import { .. }));
    assert!(matches!(p.get_node(items[1]).kind, ASTNodeKind::Struct { .. }));
    assert!(matches!(p.get_node(items[2]).kind, ASTNodeKind::Fn { .. }));
}

// The leaves an import reached, as `(path, alias, glob)` triples.
#[cfg(test)]
fn leaves_of(item: &ASTNode) -> Vec<(Vec<String>, Option<String>, bool)> {
    match &item.kind {
        ASTNodeKind::Import { leaves, .. } => leaves
            .iter()
            .map(|l| (l.path.clone(), l.alias.clone(), l.glob))
            .collect(),
        other => panic!("{:?}", other),
    }
}

#[cfg(test)]
fn path_of(segments: &[&str]) -> Vec<String> {
    segments.iter().map(|s| s.to_string()).collect()
}

#[test]
fn an_import_keeps_its_path_and_its_alias() {
    let (_, item) = only_item("import shapes::circle as c;\n");
    assert_eq!(
        leaves_of(&item),
        vec![(path_of(&["shapes", "circle"]), Some("c".to_string()), false)]
    );

    let (_, bare) = only_item("import shapes;\n");
    assert_eq!(leaves_of(&bare), vec![(path_of(&["shapes"]), None, false)]);
}

// A group is spelling and nothing more: what reaches the tree is the names it
// reached, each with the path in front of it already written on.
#[test]
fn a_group_flattens_into_one_leaf_for_each_name() {
    let (_, item) = only_item("import a::{b, c::{d, e}};\n");
    assert_eq!(
        leaves_of(&item),
        vec![
            (path_of(&["a", "b"]), None, false),
            (path_of(&["a", "c", "d"]), None, false),
            (path_of(&["a", "c", "e"]), None, false),
        ]
    );

    // An alias belongs to the leaf it renames, so one group holds both.
    let (_, aliased) = only_item("import a::{b as x, c};\n");
    assert_eq!(
        leaves_of(&aliased),
        vec![
            (path_of(&["a", "b"]), Some("x".to_string()), false),
            (path_of(&["a", "c"]), None, false),
        ]
    );
}

#[test]
fn a_glob_is_a_leaf_that_names_nothing() {
    let (_, item) = only_item("import super::super::circle::*;\n");
    assert_eq!(
        leaves_of(&item),
        vec![(path_of(&["super", "super", "circle"]), None, true)]
    );

    // A glob inside a group is a glob of the path the group stands under.
    let (_, nested) = only_item("import suite::shapes::{circle, square::*};\n");
    assert_eq!(
        leaves_of(&nested),
        vec![
            (path_of(&["suite", "shapes", "circle"]), None, false),
            (path_of(&["suite", "shapes", "square"]), None, true),
        ]
    );
}

// An import is a declaration now, so it carries what one carries.
#[test]
fn an_import_takes_a_visibility() {
    let (_, item) = only_item("pub import shapes::circle;\n");
    match &item.kind {
        ASTNodeKind::Import { vis, .. } => assert_eq!(*vis, ASTVisibility::Pub),
        other => panic!("{:?}", other),
    }

    let (_, plain) = only_item("import shapes::circle;\n");
    match &plain.kind {
        ASTNodeKind::Import { vis, .. } => assert_eq!(*vis, ASTVisibility::Unwritten),
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_receiver_says_how_it_was_taken() {
    for (source, held, life) in [
        ("impl P {\n    fn f(self);\n}\n", ASTSelf::Value, None),
        ("impl P {\n    fn f(&self);\n}\n", ASTSelf::Ref, None),
        ("impl P {\n    fn f(*self);\n}\n", ASTSelf::Mut, None),
        // And with a region named, which is a <ref_op> and a <lifetime_opt> in
        // front of the word exactly as they stand in front of a type.
        ("impl P {\n    fn f<'a>(&'a self);\n}\n", ASTSelf::Ref, Some("a")),
        ("impl P {\n    fn f<'a>(*'a self);\n}\n", ASTSelf::Mut, Some("a")),
    ] {
        let (p, item) = only_item(source);
        let ASTNodeKind::Impl { members, .. } = &item.kind else { panic!("{:?}", item.kind) };
        let ASTNodeKind::Fn { params, .. } = &p.get_node(members[0]).kind else {
            panic!("not a fn")
        };
        match &p.get_node(params[0]).kind {
            ASTNodeKind::Param { name, ty } => {
                assert_eq!(
                    *name,
                    ASTBinding::SelfRecv(held, life.map(|l: &str| l.to_string())),
                );
                // A receiver is written and not annotated.
                assert!(ty.is_none());
            }
            other => panic!("{:?}", other),
        }
    }
}

#[test]
fn pub_suite_is_its_own_visibility() {
    let (_, item) = only_item("pub(suite) fn helper();\n");
    match &item.kind {
        ASTNodeKind::Fn { vis, .. } => assert_eq!(*vis, ASTVisibility::Suite),
        other => panic!("{:?}", other),
    }
}

#[test]
fn precedence_is_spent_on_the_shape() {
    // `1 + 2 * 3` is an add whose right side is the multiply.
    let (p, stmts) = statements("    1 + 2 * 3;");
    let expr = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };
    match &p.get_node(expr).kind {
        ASTNodeKind::Binary { op, lhs, rhs } => {
            assert_eq!(*op, ASTBinOp::Add);
            assert_eq!(p.get_node(*lhs).kind, ASTNodeKind::Literal(ASTLit::Int(1, None)));
            match &p.get_node(*rhs).kind {
                ASTNodeKind::Binary { op, .. } => assert_eq!(*op, ASTBinOp::Mul),
                other => panic!("{:?}", other),
            }
        }
        other => panic!("{:?}", other),
    }
}

// The bitwise pair, and where they sit: tighter than a comparison and looser
// than a shift.
#[test]
fn the_bitwise_operators_bind_between_a_shift_and_a_comparison() {
    let binary = |p: &Parser, id: ASTNodeId| match &p.get_node(id).kind {
        ASTNodeKind::Binary { op, lhs, rhs } => (*op, *lhs, *rhs),
        other => panic!("{:?}", other),
    };
    let expr = |p: &Parser, stmts: &[ASTNodeId]| match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };

    // `a & b` is one operator and not two references, and `a | b` is
    // neither a closure nor a pattern's alternatives.
    let (p, stmts) = statements("    a & b;");
    let (op, lhs, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::BitAnd);
    assert_eq!(p.get_node(lhs).kind, ASTNodeKind::Ident("a".to_string()));
    assert_eq!(p.get_node(rhs).kind, ASTNodeKind::Ident("b".to_string()));

    let (p, stmts) = statements("    a | b;");
    assert_eq!(binary(&p, expr(&p, &stmts)).0, ASTBinOp::BitOr);

    let (p, stmts) = statements("    a ^ b;");
    assert_eq!(binary(&p, expr(&p, &stmts)).0, ASTBinOp::BitXor);

    // `&` binds tighter than `^`, and `^` tighter than `|`, so
    // `a | b ^ c & d` nests the whole ladder to the right.
    let (p, stmts) = statements("    a | b ^ c & d;");
    let (op, _, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::BitOr);
    let (op, _, rhs) = binary(&p, rhs);
    assert_eq!(op, ASTBinOp::BitXor);
    assert_eq!(binary(&p, rhs).0, ASTBinOp::BitAnd);

    // Tighter than a comparison, which is the whole point of putting them
    // here: `a & mask == 0` is `(a & mask) == 0`, not C's reading.
    let (p, stmts) = statements("    a & mask == 0;");
    let (op, lhs, _) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::Eq);
    assert_eq!(binary(&p, lhs).0, ASTBinOp::BitAnd);

    // Looser than a shift: `a | b << c` is `a | (b << c)`.
    let (p, stmts) = statements("    a | b << c;");
    let (op, _, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::BitOr);
    assert_eq!(binary(&p, rhs).0, ASTBinOp::Shl);

    // Looser than the logical pair is `&&`'s side of it: `a && b | c` is
    // `a && (b | c)`.
    let (p, stmts) = statements("    a && b | c;");
    let (op, _, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::And);
    assert_eq!(binary(&p, rhs).0, ASTBinOp::BitOr);

    // The logical three are the same ladder over booleans: `&&` tightest,
    // then `^^`, then `||`. `a || b ^^ c && d` nests the same way.
    let (p, stmts) = statements("    a || b ^^ c && d;");
    let (op, _, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::Or);
    let (op, _, rhs) = binary(&p, rhs);
    assert_eq!(op, ASTBinOp::Xor);
    assert_eq!(binary(&p, rhs).0, ASTBinOp::And);

    // `^^` is looser than every bitwise one, `^` included: the bits are
    // worked out before the booleans are.
    let (p, stmts) = statements("    a ^^ b ^ c;");
    let (op, _, rhs) = binary(&p, expr(&p, &stmts));
    assert_eq!(op, ASTBinOp::Xor);
    assert_eq!(binary(&p, rhs).0, ASTBinOp::BitXor);

    // Left-associative, as every other binary here is.
    for (source, op) in [
        ("    a & b & c;", ASTBinOp::BitAnd),
        ("    a | b | c;", ASTBinOp::BitOr),
        ("    a ^ b ^ c;", ASTBinOp::BitXor),
        ("    a ^^ b ^^ c;", ASTBinOp::Xor),
    ] {
        let (p, stmts) = statements(source);
        let (found, lhs, _) = binary(&p, expr(&p, &stmts));
        assert_eq!(found, op, "{}", source);
        assert_eq!(binary(&p, lhs).0, op, "{}", source);
    }
}

// Every compound assignment reaches the tree as the operator it names. `^=` is
// the newest, and the one the grammar was missing.
#[test]
fn a_compound_assignment_carries_its_operator() {
    for (source, op) in [
        ("    a = b;", ASTAssignOp::Set),
        ("    a += b;", ASTAssignOp::Add),
        ("    a &= b;", ASTAssignOp::And),
        ("    a |= b;", ASTAssignOp::Or),
        ("    a ^= b;", ASTAssignOp::Xor),
        ("    a <<= b;", ASTAssignOp::Shl),
        ("    a >>= b;", ASTAssignOp::Shr),
    ] {
        let (p, stmts) = statements(source);
        let expr = match &p.get_node(stmts[0]).kind {
            ASTNodeKind::ExprStmt(id) => *id,
            other => panic!("{}: {:?}", source, other),
        };
        match &p.get_node(expr).kind {
            ASTNodeKind::Assign { op: found, .. } => assert_eq!(*found, op, "{}", source),
            other => panic!("{}: {:?}", source, other),
        }
    }
}

#[test]
fn a_postfix_takes_everything_to_its_left() {
    // `a.b(c)` is a call of a field, not a field of a call.
    let (p, stmts) = statements("    a.b(c);");
    let expr = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };
    let callee = match &p.get_node(expr).kind {
        ASTNodeKind::Call { callee, args } => {
            assert_eq!(args.len(), 1);
            *callee
        }
        other => panic!("{:?}", other),
    };
    match &p.get_node(callee).kind {
        ASTNodeKind::Field { base, name } => {
            assert_eq!(name, "b");
            assert_eq!(p.get_node(*base).kind, ASTNodeKind::Ident("a".to_string()));
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_declaration_carries_what_was_written_in_front_of_it() {
    let (p, item) = only_item("%repr(C)\npub const unsafe fn f(x: i32): i32 {\n    x\n}\n");
    match &item.kind {
        ASTNodeKind::Fn { attrs, vis, is_const, is_unsafe, name, params, ret, .. } => {
            assert_eq!(attrs.len(), 1);
            assert_eq!(*vis, ASTVisibility::Pub);
            assert!(*is_const && *is_unsafe);
            assert_eq!(name, "f");
            assert_eq!(params.len(), 1);
            assert!(ret.is_some());
            match &p.get_node(attrs[0]).kind {
                ASTNodeKind::Attr { name, args } => {
                    assert_eq!(name, "repr");
                    assert_eq!(args.len(), 1);
                }
                other => panic!("{:?}", other),
            }
        }
        other => panic!("{:?}", other),
    }
    // The declaration begins at its first attribute, not at `public`.
    assert_eq!((item.line, item.col), (1, 1));
}

#[test]
fn a_signature_without_a_body_has_none() {
    let (p, item) = only_item("trait Show {\n    fn show(&self): str;\n}\n");
    let members = match &item.kind {
        ASTNodeKind::Trait { members, .. } => members.clone(),
        other => panic!("{:?}", other),
    };
    assert_eq!(members.len(), 1);
    match &p.get_node(members[0]).kind {
        ASTNodeKind::Fn { body, params, .. } => {
            assert!(body.is_none());
            assert_eq!(params.len(), 1);
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_type_is_read_from_the_inside_out() {
    // `x: i32[8][]` is a run of arrays of 8.
    let (p, stmts) = statements("    let x: i32[8][] = y;");
    let ty = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::Variable { ty: Some(id), intro, .. } => {
            assert_eq!(*intro, ASTVariableIntro::Let);
            *id
        }
        other => panic!("{:?}", other),
    };
    let elem = match &p.get_node(ty).kind {
        ASTNodeKind::Run(elem) => *elem,
        other => panic!("{:?}", other),
    };
    match &p.get_node(elem).kind {
        ASTNodeKind::Array { elem, .. } => {
            assert_eq!(p.get_node(*elem).kind, ASTNodeKind::Prim(ASTPrimType::I32));
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_tuple_keeps_its_members_in_order() {
    // The type, the literal and the `.0` that reaches into one. Each holds
    // the members the comma separated, and the first of them is no
    // different from the rest for having stood in front of it.
    let (p, item) = only_item("fn pair(): (i32, str) {\n    (1, \"a\").0\n}\n");
    let (ret, body) = match &item.kind {
        ASTNodeKind::Fn { ret: Some(ret), body: Some(body), .. } => (*ret, *body),
        other => panic!("{:?}", other),
    };
    match &p.get_node(ret).kind {
        ASTNodeKind::TupleType(members) => {
            assert_eq!(members.len(), 2);
            assert_eq!(p.get_node(members[0]).kind, ASTNodeKind::Prim(ASTPrimType::I32));
            assert_eq!(p.get_node(members[1]).kind, ASTNodeKind::Prim(ASTPrimType::Str));
        }
        other => panic!("{:?}", other),
    }
    let tail = match &p.get_node(body).kind {
        ASTNodeKind::Block { tail: Some(id), .. } => *id,
        other => panic!("{:?}", other),
    };
    let base = match &p.get_node(tail).kind {
        ASTNodeKind::TupleIndex { base, index } => {
            assert_eq!(*index, 0);
            *base
        }
        other => panic!("{:?}", other),
    };
    match &p.get_node(base).kind {
        ASTNodeKind::TupleLit(members) => {
            assert_eq!(members.len(), 2);
            assert_eq!(p.get_node(members[0]).kind, ASTNodeKind::Literal(ASTLit::Int(1, None)));
        }
        other => panic!("{:?}", other),
    }
    // A group of one is still a group: the parentheses leave no node.
    let (p, stmts) = statements("    let x = (1);");
    match &p.get_node(stmts[0]).kind {
        ASTNodeKind::Variable { init: Some(id), .. } => {
            assert_eq!(p.get_node(*id).kind, ASTNodeKind::Literal(ASTLit::Int(1, None)));
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_tuple_pattern_is_a_variant_pattern_with_no_name() {
    let (p, stmts) = statements("    match p {\n        (0, y) => y,\n        _ => 0,\n    };");
    let expr = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };
    let arms = match &p.get_node(expr).kind {
        ASTNodeKind::Match { arms, .. } => arms.clone(),
        other => panic!("{:?}", other),
    };
    let pats = match &p.get_node(arms[0]).kind {
        ASTNodeKind::MatchArm { pats, .. } => pats.clone(),
        other => panic!("{:?}", other),
    };
    match &p.get_node(pats[0]).kind {
        ASTNodeKind::TuplePat(elems) => {
            assert_eq!(elems.len(), 2);
            match &p.get_node(elems[0]).kind {
                ASTNodeKind::LitPat { negated, value } => {
                    assert!(!negated);
                    assert_eq!(*value, ASTLit::Int(0, None));
                }
                other => panic!("{:?}", other),
            }
            // A bare name is a `Name`: whether it binds is not the
            // parser's to say.
            assert_eq!(p.get_node(elems[1]).kind, ASTNodeKind::Name(vec!["y".to_string()]));
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_block_tells_its_tail_from_its_statements() {
    let (p, item) = only_item("fn f(): i32 {\n    g();\n    1\n}\n");
    let block = match &item.kind {
        ASTNodeKind::Fn { body: Some(id), .. } => *id,
        other => panic!("{:?}", other),
    };
    match &p.get_node(block).kind {
        ASTNodeKind::Block { stmts, tail } => {
            assert_eq!(stmts.len(), 1);
            let tail = tail.expect("the last expression is the block's value");
            assert_eq!(p.get_node(tail).kind, ASTNodeKind::Literal(ASTLit::Int(1, None)));
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_match_keeps_its_arms_and_their_alternatives() {
    let (p, stmts) = statements("    match x {\n        1 | 2 => a,\n        _ => b,\n    };");
    let expr = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::ExprStmt(id) => *id,
        other => panic!("{:?}", other),
    };
    let arms = match &p.get_node(expr).kind {
        ASTNodeKind::Match { arms, .. } => arms.clone(),
        other => panic!("{:?}", other),
    };
    assert_eq!(arms.len(), 2);
    match &p.get_node(arms[0]).kind {
        ASTNodeKind::MatchArm { pats, .. } => assert_eq!(pats.len(), 2),
        other => panic!("{:?}", other),
    }
    match &p.get_node(arms[1]).kind {
        ASTNodeKind::MatchArm { pats, .. } => {
            assert_eq!(p.get_node(pats[0]).kind, ASTNodeKind::Wildcard);
        }
        other => panic!("{:?}", other),
    }
}

#[test]
fn a_node_stands_where_it_was_written() {
    let (p, stmts) = statements("    let x = 1;\n    y = 2;");
    // Line 1 is the `fn`, so the statements are on 2 and 3.
    assert_eq!(p.get_node(stmts[0]).line, 2);
    assert_eq!(p.get_node(stmts[0]).col, 5);
    assert_eq!(p.get_node(stmts[1]).line, 3);
}

#[test]
fn check_tree() {
    // Every node the root can reach is a node of the language: no `ASTMark`
    // survived the rule that took its word, and no hole was left unfilled.
    let source = "import a::b as c;\n\
                  pub import a::{b, c::*, d::{e, f as g}};\n\
                  pub(suite) import super::super::h::*;\n\
                  import suite::i::j;\n\
                  %attr(1)\n\
                  pub fn f<T: Ord>(&self, x: *i32[2]): (bool, i32) {\n\
                      let y = -x.a as i64 .. 3;\n\
                      let t: (i32, str) = (1, \"a\");\n\
                      let u = t.1;\n\
                      let v = suite::limits::MAX + super::k::n;\n\
                      let w: super::Node = self;\n\
                      import self::inner::q;\n\
                      unsafe let p: ptr u8 = addr x.a;\n\
                      let gc r = #{1: 2};\n\
                      unsafe var gc s = addr x.a;\n\
                      if y { g(#{1: 2}, {,}, [1]) } else { move |z| z + 1 };\n\
                      while y { continue }\n\
                      for i in 0..=9 { break }\n\
                      match x {\n\
                          1..=2 => a,\n\
                          -3 => b,\n\
                          P::Q(m) => m,\n\
                          (m, _) => m,\n\
                          P { n: o } => o,\n\
                          suite::P::Q => a,\n\
                          _ => return,\n\
                      }\n\
                  }\n\
                  namespace n {\n\
                      const K: i32 = 1;\n\
                      pub let gc t: ptr u8 = z();\n\
                      enum E { A, B(i32), C { x: i32 }, D = 4 }\n\
                      struct S<T> { priv v: T[] }\n\
                      trait W { fn w<T>(&self, t: T): str where T: Ord; }\n\
                      impl W for S<i32> { priv fn w(&self): str { P { r: 1 } } }\n\
                      impl S<i32> { fn take(self); fn put(*self); }\n\
                      struct H<'a, 'b: 'a, T: Ord + 'a> { v: &'a T[], w: *'b T, p: ptr T }\n\
                      fn h<'a, T>(x: &'a T, y: &Map<'a, T>): &'a T where T: 'a, 'a: 'b;\n\
                  }\n";
    let (p, root) = tree(source);
    let mut seen = vec![false; p.nodes.len()];
    let mut stack = vec![0usize];
    // The root itself is not in the arena under a handle of its own --
    // `parse` gives back a copy -- so it is walked from here.
    let mut walk = vec![root.kind.clone()];
    while let Some(kind) = walk.pop() {
        assert!(
            !matches!(kind, ASTNodeKind::Mark(_)),
            "a mark reached the tree: {:?}",
            kind
        );
        for child in children_of(&kind) {
            assert_ne!(child, HOLE, "a hole was left unfilled in {:?}", kind);
            if !seen[child] {
                seen[child] = true;
                stack.push(child);
                walk.push(p.get_node(child).kind.clone());
            }
        }
    }
    assert!(stack.len() > 1, "the walk found nothing");
}

#[test]
fn a_recovered_parse_still_builds_a_tree() {
    // Recovery cuts the stack back to a state that can go on, and every
    // entry left is still the state a symbol was reached by and the node
    // that symbol built -- so the reductions after one take the children
    // their rules call for, and `build` never sees a stack it cannot read.
    for source in [
        "fn a() { let x = ; }\nfn b() { g(] }\nfn c() {}\n",
        "fn f(x: ) {}\nstruct S { y: i32, }\n",
        "fn main() {\n    f(1, 2\n}\n",
        "fn main() {\n    match x {\n        1 => ,\n    }\n}\n",
    ] {
        let mut p = Parser::new(lexer::Lexer::new(source));
        let root = p.parse();
        assert!(!p.errors().is_empty(), "{}", source);
        // Whatever it built, it is a file or the `Empty` a parse that could
        // not recover gives back -- never a half-built rule.
        assert!(
            matches!(root.kind, ASTNodeKind::Program(_) | ASTNodeKind::Empty),
            "{} built {:?}",
            source,
            root.kind
        );
    }
}

// Every handle a node names. One arm per kind that holds any, so a kind added
// to the tree is not walked past in silence.
fn children_of(kind: &ASTNodeKind) -> Vec<ASTNodeId> {
    let mut out = Vec::new();
    match kind {
        ASTNodeKind::Program(ids)
        | ASTNodeKind::List(ids)
        | ASTNodeKind::ArrayLit(ids)
        | ASTNodeKind::TupleLit(ids)
        | ASTNodeKind::TupleType(ids)
        | ASTNodeKind::TuplePat(ids)
        | ASTNodeKind::TuplePayload(ids)
        | ASTNodeKind::NamedPayload(ids) => out.extend_from_slice(ids),
        ASTNodeKind::Fn { attrs, generics, params, ret, wheres, body, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.extend_from_slice(params);
            out.extend_from_slice(wheres);
            out.extend(ret.iter().chain(body.iter()));
        }
        ASTNodeKind::Struct { attrs, generics, fields, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.extend_from_slice(fields);
        }
        ASTNodeKind::Enum { attrs, generics, variants, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.extend_from_slice(variants);
        }
        ASTNodeKind::Trait { attrs, generics, members, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.extend_from_slice(members);
        }
        ASTNodeKind::Impl { attrs, generics, ty, for_ty, wheres, members, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.extend_from_slice(wheres);
            out.extend_from_slice(members);
            out.push(*ty);
            out.extend(for_ty.iter());
        }
        ASTNodeKind::Namespace { attrs, items, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(items);
        }
        ASTNodeKind::Variable { attrs, ty, init, .. } => {
            out.extend_from_slice(attrs);
            out.extend(ty.iter().chain(init.iter()));
        }
        ASTNodeKind::Const { attrs, ty, value, .. } => {
            out.extend_from_slice(attrs);
            out.push(*ty);
            out.push(*value);
        }
        ASTNodeKind::TypeAlias { attrs, generics, ty, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(generics);
            out.push(*ty);
        }
        ASTNodeKind::Attr { args, .. } => out.extend_from_slice(args),
        ASTNodeKind::Param { ty, .. } => out.extend(ty.iter()),
        ASTNodeKind::FieldDecl { attrs, ty, .. } => {
            out.extend_from_slice(attrs);
            out.push(*ty);
        }
        ASTNodeKind::EnumVariant { attrs, body, .. } => {
            out.extend_from_slice(attrs);
            out.extend(body.iter());
        }
        ASTNodeKind::Discriminant(id)
        | ASTNodeKind::Run(id)
        | ASTNodeKind::PtrType(id)
        | ASTNodeKind::ExprStmt(id)
        | ASTNodeKind::Unsafe(id) => out.push(*id),
        ASTNodeKind::MacroDecl { attrs, params, body, .. } => {
            out.extend_from_slice(attrs);
            out.extend_from_slice(params);
            out.push(*body);
        }
        ASTNodeKind::MacroCall { args, .. } => out.extend_from_slice(args),
        ASTNodeKind::GenericParam { bounds, .. }
        | ASTNodeKind::LifetimeParam { bounds, .. } => out.extend_from_slice(bounds),
        ASTNodeKind::WherePred { ty, bounds } => {
            out.push(*ty);
            out.extend_from_slice(bounds);
        }
        ASTNodeKind::RefType { life, inner, .. } => {
            out.extend(life.iter().copied());
            out.push(*inner);
        }
        ASTNodeKind::Array { elem, len } => {
            out.push(*elem);
            out.push(*len);
        }
        ASTNodeKind::Named { args, .. } => out.extend_from_slice(args),
        ASTNodeKind::Map { entries, .. } => out.extend_from_slice(entries),
        ASTNodeKind::Set { elems, .. } => out.extend_from_slice(elems),
        ASTNodeKind::MapEntry { key, value } => {
            out.push(*key);
            out.push(*value);
        }
        ASTNodeKind::Field { base, .. }
        | ASTNodeKind::TupleIndex { base, .. }
        | ASTNodeKind::Path { base, .. } => out.push(*base),
        ASTNodeKind::TypeArgs { base, args } => {
            out.push(*base);
            out.extend_from_slice(args);
        }
        ASTNodeKind::Call { callee, args } => {
            out.push(*callee);
            out.extend_from_slice(args);
        }
        ASTNodeKind::Index { base, index } => {
            out.push(*base);
            out.push(*index);
        }
        ASTNodeKind::StructLit { base, fields } => {
            out.push(*base);
            out.extend_from_slice(fields);
        }
        ASTNodeKind::FieldInit { value, .. } => out.push(*value),
        ASTNodeKind::Unary { operand, .. } => out.push(*operand),
        ASTNodeKind::Binary { lhs, rhs, .. } => {
            out.push(*lhs);
            out.push(*rhs);
        }
        ASTNodeKind::Assign { target, value, .. } => {
            out.push(*target);
            out.push(*value);
        }
        ASTNodeKind::Range { start, end, .. } => out.extend(start.iter().chain(end.iter())),
        ASTNodeKind::Cast { value, ty } => {
            out.push(*value);
            out.push(*ty);
        }
        ASTNodeKind::Closure { params, body, .. } => {
            out.extend_from_slice(params);
            out.push(*body);
        }
        ASTNodeKind::Block { stmts, tail } => {
            out.extend_from_slice(stmts);
            out.extend(tail.iter());
        }
        ASTNodeKind::If { cond, then, elifs, else_block } => {
            out.push(*cond);
            out.push(*then);
            out.extend_from_slice(elifs);
            out.extend(else_block.iter());
        }
        ASTNodeKind::Elif { cond, block } => {
            out.push(*cond);
            out.push(*block);
        }
        ASTNodeKind::While { cond, body } => {
            out.push(*cond);
            out.push(*body);
        }
        ASTNodeKind::For { iter, body, .. } => {
            out.push(*iter);
            out.push(*body);
        }
        ASTNodeKind::Match { scrutinee, arms } => {
            out.push(*scrutinee);
            out.extend_from_slice(arms);
        }
        ASTNodeKind::MatchArm { pats, body } => {
            out.extend_from_slice(pats);
            out.push(*body);
        }
        ASTNodeKind::Return(id) | ASTNodeKind::Break(id) => out.extend(id.iter()),
        ASTNodeKind::RangePat { lo, hi, .. } => {
            out.push(*lo);
            out.push(*hi);
        }
        ASTNodeKind::VariantPat { elems, .. } => out.extend_from_slice(elems),
        ASTNodeKind::StructPat { fields, .. } => out.extend_from_slice(fields),
        ASTNodeKind::FieldPat { pat, .. } => out.extend(pat.iter()),
        // An import holds only the attributes written in front of it: the tree
        // it reached is spelling, and stands in the node itself.
        ASTNodeKind::Import { attrs, .. } => out.extend_from_slice(attrs),
        // The leaves, and the scaffolding that names nothing.
        ASTNodeKind::Empty
        | ASTNodeKind::Mark(_)
        | ASTNodeKind::ImportTree(_)
        | ASTNodeKind::Prim(_)
        | ASTNodeKind::Infer
        | ASTNodeKind::Literal(_)
        | ASTNodeKind::Ident(_)
        | ASTNodeKind::Lifetime(_)
        | ASTNodeKind::MacroVar(_)
        | ASTNodeKind::MacroParam { .. }
        | ASTNodeKind::SelfExpr
        | ASTNodeKind::SelfRecv(..)
        | ASTNodeKind::Name(_)
        | ASTNodeKind::Continue
        | ASTNodeKind::Wildcard
        | ASTNodeKind::LitPat { .. } => {}
    }
    out
}

// A lifetime reaches the tree in the four places it is written: a parameter of
// the declaration, an argument of a type, in front of a referent, and as a
// bound. The `~` is the lexer's, so what the tree holds is the name alone.
#[test]
fn a_lifetime_reaches_the_tree_where_it_was_written() {
    let (p, item) = only_item("fn longest<'a, T: 'a>(x: &'a str): &'a T;\n");
    let (generics, params, ret) = match &item.kind {
        ASTNodeKind::Fn { generics, params, ret, .. } => {
            (generics.clone(), params.clone(), ret.expect("a return type"))
        }
        other => panic!("built {:?}", other),
    };

    // `<'a, T: 'a>`: a lifetime parameter, then a type parameter bounded by it.
    assert_eq!(generics.len(), 2);
    match &p.get_node(generics[0]).kind {
        ASTNodeKind::LifetimeParam { name, bounds } => {
            assert_eq!(name, "a");
            assert!(bounds.is_empty());
        }
        other => panic!("the first parameter built {:?}", other),
    }
    match &p.get_node(generics[1]).kind {
        ASTNodeKind::GenericParam { name, bounds } => {
            assert_eq!(name, "T");
            assert_eq!(bounds.len(), 1);
            // A bound is a type or a lifetime, and this one is the lifetime.
            assert_eq!(p.get_node(bounds[0]).kind, ASTNodeKind::Lifetime("a".to_string()));
        }
        other => panic!("the second parameter built {:?}", other),
    }

    // `x: &'a str`: the lifetime hangs off the reference, not off the referent.
    let ty = match &p.get_node(params[0]).kind {
        ASTNodeKind::Param { ty: Some(id), .. } => *id,
        other => panic!("a parameter built {:?}", other),
    };
    match &p.get_node(ty).kind {
        ASTNodeKind::RefType { op, life, inner } => {
            assert_eq!(*op, ASTRefOp::Imm);
            let life = life.expect("a written lifetime");
            assert_eq!(p.get_node(life).kind, ASTNodeKind::Lifetime("a".to_string()));
            assert_eq!(p.get_node(*inner).kind, ASTNodeKind::Prim(ASTPrimType::Str));
        }
        other => panic!("a reference type built {:?}", other),
    }
    assert!(matches!(p.get_node(ret).kind, ASTNodeKind::RefType { life: Some(_), .. }));
}

// A reference with no lifetime written is the usual one, and says so with a
// `None` rather than with a name the parse invented.
#[test]
fn a_reference_with_no_lifetime_written_holds_none() {
    let (p, item) = only_item("fn f(x: &str);\n");
    let params = match &item.kind {
        ASTNodeKind::Fn { params, .. } => params.clone(),
        other => panic!("built {:?}", other),
    };
    let ty = match &p.get_node(params[0]).kind {
        ASTNodeKind::Param { ty: Some(id), .. } => *id,
        other => panic!("a parameter built {:?}", other),
    };
    assert!(matches!(p.get_node(ty).kind, ASTNodeKind::RefType { life: None, .. }));
}

// `ptr T` is a type of its own and not a third <ref_op>: it takes no lifetime,
// and what it holds is whatever a type holds -- a run included, since a pointer
// binds looser than an array suffix exactly as a reference does.
#[test]
fn a_pointer_type_holds_a_type_and_no_lifetime() {
    let (p, item) = only_item("fn f(dst: ptr u8[], src: ptr ptr Node);\n");
    let params = match &item.kind {
        ASTNodeKind::Fn { params, .. } => params.clone(),
        other => panic!("built {:?}", other),
    };
    let ty_of = |p: &Parser, id| match &p.get_node(id).kind {
        ASTNodeKind::Param { ty: Some(id), .. } => *id,
        other => panic!("a parameter built {:?}", other),
    };

    // `ptr u8[]`: the suffix went on the `u8`, so this points at a run.
    let inner = match p.get_node(ty_of(&p, params[0])).kind {
        ASTNodeKind::PtrType(inner) => inner,
        ref other => panic!("a pointer type built {:?}", other),
    };
    match p.get_node(inner).kind {
        ASTNodeKind::Run(elem) => {
            assert_eq!(p.get_node(elem).kind, ASTNodeKind::Prim(ASTPrimType::U8));
        }
        ref other => panic!("the referent built {:?}", other),
    }

    // `ptr ptr Node`: one nests in the other, no rule of its own needed.
    let inner = match p.get_node(ty_of(&p, params[1])).kind {
        ASTNodeKind::PtrType(inner) => inner,
        ref other => panic!("a pointer type built {:?}", other),
    };
    assert!(matches!(p.get_node(inner).kind, ASTNodeKind::PtrType(_)));
}

// A pointer stands wherever a type stands: in a struct field, in a type
// argument, in a return type, and after the `as` of a cast.
#[test]
fn a_pointer_stands_where_a_type_stands() {
    let (p, item) = only_item("struct Buf {\n    p: ptr u8,\n    all: Vec<Vec<ptr u8>>,\n}\n");
    let fields = match &item.kind {
        ASTNodeKind::Struct { fields, .. } => fields.clone(),
        other => panic!("built {:?}", other),
    };
    let ty_of = |p: &Parser, id| match &p.get_node(id).kind {
        ASTNodeKind::FieldDecl { ty, .. } => *ty,
        other => panic!("a field built {:?}", other),
    };
    assert!(matches!(p.get_node(ty_of(&p, fields[0])).kind, ASTNodeKind::PtrType(_)));
    // Nested, so the `>>` that closes both is split as it is anywhere else --
    // the pointer inside did not cost the lexer the context it needs to.
    let inner = match &p.get_node(ty_of(&p, fields[1])).kind {
        ASTNodeKind::Named { args, .. } => args[0],
        other => panic!("the second field built {:?}", other),
    };
    match &p.get_node(inner).kind {
        ASTNodeKind::Named { args, .. } => {
            assert!(matches!(p.get_node(args[0]).kind, ASTNodeKind::PtrType(_)));
        }
        other => panic!("the nested argument built {:?}", other),
    }

    let (p, stmts) = statements("unsafe let q = p as ptr u64;");
    let cast = match &p.get_node(stmts[0]).kind {
        ASTNodeKind::Unsafe(inner) => match &p.get_node(*inner).kind {
            ASTNodeKind::Variable { init: Some(id), .. } => *id,
            other => panic!("the guarded statement built {:?}", other),
        },
        other => panic!("built {:?}", other),
    };
    match &p.get_node(cast).kind {
        ASTNodeKind::Cast { ty, .. } => {
            assert!(matches!(p.get_node(*ty).kind, ASTNodeKind::PtrType(_)));
        }
        other => panic!("a cast built {:?}", other),
    }
}

// `addr` is a <unary_op>, so it binds as the other three do: looser than a
// postfix and tighter than anything infix. `addr p.x` is the address of the
// field and `addr a + b` adds to the address of `a`.
#[test]
fn addr_binds_as_a_unary_operator() {
    let (p, stmts) = statements("unsafe let a = addr p.x;\n    unsafe let b = addr y + 1;");
    let init_of = |p: &Parser, id| match &p.get_node(id).kind {
        ASTNodeKind::Unsafe(inner) => match &p.get_node(*inner).kind {
            ASTNodeKind::Variable { init: Some(id), .. } => *id,
            other => panic!("the guarded statement built {:?}", other),
        },
        other => panic!("built {:?}", other),
    };
    match &p.get_node(init_of(&p, stmts[0])).kind {
        ASTNodeKind::Unary { op, operand } => {
            assert_eq!(*op, ASTUnaryOp::Addr);
            assert!(matches!(p.get_node(*operand).kind, ASTNodeKind::Field { .. }));
        }
        other => panic!("built {:?}", other),
    }
    match &p.get_node(init_of(&p, stmts[1])).kind {
        ASTNodeKind::Binary { op: ASTBinOp::Add, lhs, .. } => {
            assert!(matches!(
                p.get_node(*lhs).kind,
                ASTNodeKind::Unary { op: ASTUnaryOp::Addr, .. }
            ));
        }
        other => panic!("built {:?}", other),
    }
}

// A lifetime is a type argument like any other, and a `where` predicate takes
// one on either side of its colon.
#[test]
fn a_lifetime_is_an_argument_and_a_predicate() {
    let (p, item) = only_item("struct Parser<'a> {\n    text: &'a str,\n}\n");
    match &item.kind {
        ASTNodeKind::Struct { generics, fields, .. } => {
            assert_eq!(generics.len(), 1);
            assert_eq!(fields.len(), 1);
            assert!(matches!(
                p.get_node(generics[0]).kind,
                ASTNodeKind::LifetimeParam { .. }
            ));
        }
        other => panic!("built {:?}", other),
    }

    let (p, item) = only_item("fn f<'a, 'b>(x: &'a i32) where 'a: 'b;\n");
    let wheres = match &item.kind {
        ASTNodeKind::Fn { wheres, .. } => wheres.clone(),
        other => panic!("built {:?}", other),
    };
    assert_eq!(wheres.len(), 1);
    match &p.get_node(wheres[0]).kind {
        ASTNodeKind::WherePred { ty, bounds } => {
            assert_eq!(p.get_node(*ty).kind, ASTNodeKind::Lifetime("a".to_string()));
            assert_eq!(bounds.len(), 1);
            assert_eq!(p.get_node(bounds[0]).kind, ASTNodeKind::Lifetime("b".to_string()));
        }
        other => panic!("a where predicate built {:?}", other),
    }
}

// The tables and these arms are written against the same grammar, and nothing
// but this says so. A rule id is the generator's: adding a rule to
// docs/grammar.bnf shifts every id after it, and an arm left behind points at
// whatever production took its number -- silently, since a wrong arm of the
// same arity builds a wrong node rather than panicking.
//
// `build` does complain about a rule with no arm at all, but only once some
// source reaches that rule, and `parse.rs` runs the tables without building a
// tree at all. This asks for every rule at once, which is the only moment the
// answer is cheap.
#[test]
fn every_rule_has_exactly_one_arm() {
    // The pattern of an arm: the ids at the head of a line, up to the `=>`.
    // Anchored so that nothing inside a body -- `c[0]`, `1u64` -- can match.
    fn ids_of(pattern: &str) -> Vec<usize> {
        let mut out = Vec::new();
        for part in pattern.split('|') {
            let part = part.trim();
            match part.split_once("..=") {
                Some((lo, hi)) => {
                    let (lo, hi): (usize, usize) =
                        (lo.trim().parse().unwrap(), hi.trim().parse().unwrap());
                    out.extend(lo..=hi);
                }
                None => out.push(part.parse().unwrap()),
            }
        }
        out
    }

    // The head of a line, if it is one an arm could begin with.
    fn arm_of(line: &str) -> Option<&str> {
        let (head, _) = line.split_once("=>")?;
        let head = head.trim();
        let ok = |c: char| c.is_ascii_digit() || c == '|' || c == '.' || c == '=' || c == ' ';
        if head.is_empty() || !head.chars().all(ok) || !head.starts_with(|c: char| c.is_ascii_digit())
        {
            return None;
        }
        Some(head)
    }

    // What each rule of the tables was generated from, by the comment the
    // generator wrote beside it.
    let tables = include_str!("../../tables.rs");
    let rules: Vec<&str> = tables
        .split_once("pub const RULES: &[Rule] = &[")
        .expect("the tables hold a rule table")
        .1
        .split_once("\n];")
        .unwrap()
        .0
        .lines()
        .filter(|l| l.trim_start().starts_with("Rule {"))
        .map(|l| l.split_once("// ").expect("a rule names its production").1.trim())
        .collect();

    let files: [(&str, &str); 6] = [
        ("items.rs", include_str!("items.rs")),
        ("exprs.rs", include_str!("exprs.rs")),
        ("types.rs", include_str!("types.rs")),
        ("patterns.rs", include_str!("patterns.rs")),
        ("stmts.rs", include_str!("stmts.rs")),
        ("literals.rs", include_str!("literals.rs")),
    ];

    let mut owner: Vec<Option<String>> = vec![None; rules.len()];
    for (name, source) in files {
        let lines: Vec<&str> = source.lines().collect();
        for (n, line) in lines.iter().enumerate() {
            let Some(head) = arm_of(line) else { continue };
            for id in ids_of(head) {
                let at = format!("{}:{}", name, n + 1);
                assert!(id < rules.len(), "{} points at rule {}, past the table", at, id);
                assert!(
                    owner[id].is_none(),
                    "rule {} has two arms: {} and {}",
                    id,
                    owner[id].as_ref().unwrap(),
                    at
                );
                owner[id] = Some(at);
            }

            // What the arm says it builds has to be what it was given. Only
            // where one comment names one rule: the rest summarise.
            let ids = ids_of(head);
            if ids.len() != 1 {
                continue;
            }
            let mut k = n;
            while k > 0 && lines[k - 1].trim_start().starts_with("//") {
                let comment = lines[k - 1].trim_start().trim_start_matches("//").trim();
                if comment.starts_with('<') && comment.contains(" -> ") {
                    assert_eq!(
                        comment,
                        rules[ids[0]],
                        "{}:{} builds rule {}, which is a different production",
                        name,
                        n + 1,
                        ids[0]
                    );
                    break;
                }
                k -= 1;
            }
        }
    }

    let orphans: Vec<String> = owner
        .iter()
        .enumerate()
        .filter(|(_, o)| o.is_none())
        .map(|(i, _)| format!("{} {}", i, rules[i]))
        .collect();
    assert!(orphans.is_empty(), "rules with no arm:\n  {}", orphans.join("\n  "));
}


// `gc` stands between the intro and the name, so it annotates the binding
// rather than the value: `let gc x` and `var gc x` are both said, and the word
// is spent by the time the tree is built.
#[test]
fn gc_is_a_flag_on_the_binding() {
    let (p, stmts) = statements("    let gc m = {1: 2};\n    var gc s = {1};\n    let n = 1;");
    let flags: Vec<(bool, ASTVariableIntro)> = stmts
        .iter()
        .map(|&s| match p.get_node(s).kind.clone() {
            ASTNodeKind::Variable { gc, intro, .. } => (gc, intro),
            other => panic!("{:?}", other),
        })
        .collect();
    assert_eq!(
        flags,
        vec![
            (true, ASTVariableIntro::Let),
            (true, ASTVariableIntro::Var),
            (false, ASTVariableIntro::Let),
        ]
    );
}

// It is a whole word, as every keyword is: `gcx` and `gc_root` are names.
#[test]
fn gc_is_reserved_as_a_whole_word_only() {
    let (p, stmts) = statements("    let gcx = 1;\n    let gc_root = 2;");
    let names: Vec<ASTBinding> = stmts
        .iter()
        .map(|&s| match p.get_node(s).kind.clone() {
            ASTNodeKind::Variable { gc: false, name, .. } => name,
            other => panic!("{:?}", other),
        })
        .collect();
    assert_eq!(
        names,
        vec![ASTBinding::Name("gcx".to_string()), ASTBinding::Name("gc_root".to_string())]
    );
}
