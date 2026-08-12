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

#[test]
fn an_import_keeps_its_path_and_its_alias() {
    let (_, item) = only_item("import shapes::circle as c;\n");
    match &item.kind {
        ASTNodeKind::Import { path, alias } => {
            assert_eq!(path, &["shapes", "circle"]);
            assert_eq!(alias.as_deref(), Some("c"));
        }
        other => panic!("{:?}", other),
    }
    let (_, bare) = only_item("import shapes;\n");
    match &bare.kind {
        ASTNodeKind::Import { path, alias } => {
            assert_eq!(path, &["shapes"]);
            assert_eq!(alias, &None);
        }
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
            assert_eq!(p.get_node(*lhs).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
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
    let (p, item) = only_item("%repr(C)\npublic const unsafe fn f(x: i32): i32 {\n    x\n}\n");
    match &item.kind {
        ASTNodeKind::Fn { attrs, vis, is_const, is_unsafe, name, params, ret, .. } => {
            assert_eq!(attrs.len(), 1);
            assert_eq!(*vis, ASTVisibility::Public);
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
    let (p, item) = only_item("trait Show {\n    fn show(this): str;\n}\n");
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
            assert_eq!(p.get_node(members[0]).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
        }
        other => panic!("{:?}", other),
    }
    // A group of one is still a group: the parentheses leave no node.
    let (p, stmts) = statements("    let x = (1);");
    match &p.get_node(stmts[0]).kind {
        ASTNodeKind::Variable { init: Some(id), .. } => {
            assert_eq!(p.get_node(*id).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
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
                    assert_eq!(*value, ASTLit::Int(0));
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
            assert_eq!(p.get_node(tail).kind, ASTNodeKind::Literal(ASTLit::Int(1)));
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
                  %attr(1)\n\
                  public fn f<T: Ord>(this, x: *i32[2]): (bool, i32) {\n\
                      let y = -x.a as i64 .. 3;\n\
                      let t: (i32, str) = (1, \"a\");\n\
                      let u = t.1;\n\
                      if y { g(#{1: 2}, {,}, [1]) } else { move |z| z + 1 };\n\
                      while y { continue }\n\
                      for i in 0..=9 { break }\n\
                      match x {\n\
                          1..=2 => a,\n\
                          -3 => b,\n\
                          P::Q(m) => m,\n\
                          (m, _) => m,\n\
                          P { n: o } => o,\n\
                          _ => return,\n\
                      }\n\
                  }\n\
                  namespace n {\n\
                      const K: i32 = 1;\n\
                      enum E { A, B(i32), C { x: i32 }, D = 4 }\n\
                      struct S<T> { private v: T[] }\n\
                      trait W { fn w<T>(this, t: T): str where T: Ord; }\n\
                      impl W for S<i32> { private fn w(this): str { P { r: 1 } } }\n\
                      struct H<~a, ~b: ~a, T: Ord + ~a> { v: &~a T[], w: *~b T }\n\
                      fn h<~a, T>(x: &~a T, y: &Map<~a, T>): &~a T where T: ~a, ~a: ~b;\n\
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
        // The leaves, and the scaffolding that names nothing.
        ASTNodeKind::Empty
        | ASTNodeKind::Mark(_)
        | ASTNodeKind::Import { .. }
        | ASTNodeKind::Prim(_)
        | ASTNodeKind::Infer
        | ASTNodeKind::Literal(_)
        | ASTNodeKind::Ident(_)
        | ASTNodeKind::Lifetime(_)
        | ASTNodeKind::MacroVar(_)
        | ASTNodeKind::MacroParam { .. }
        | ASTNodeKind::This
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
    let (p, item) = only_item("fn longest<~a, T: ~a>(x: &~a str): &~a T;\n");
    let (generics, params, ret) = match &item.kind {
        ASTNodeKind::Fn { generics, params, ret, .. } => {
            (generics.clone(), params.clone(), ret.expect("a return type"))
        }
        other => panic!("built {:?}", other),
    };

    // `<~a, T: ~a>`: a lifetime parameter, then a type parameter bounded by it.
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

    // `x: &~a str`: the lifetime hangs off the reference, not off the referent.
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

// A lifetime is a type argument like any other, and a `where` predicate takes
// one on either side of its colon.
#[test]
fn a_lifetime_is_an_argument_and_a_predicate() {
    let (p, item) = only_item("struct Parser<~a> {\n    text: &~a str,\n}\n");
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

    let (p, item) = only_item("fn f<~a, ~b>(x: &~a i32) where ~a: ~b;\n");
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
