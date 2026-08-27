// Closures: what they capture, how they took it, and what that lets the body
// and the caller do with it afterwards.

use super::*;

// ---- Closures -------------------------------------------------------------

// "A name the body uses but did not declare is captured, and how is worked out
// per name, each taking the least the body asks of it. Reading one takes a `&`
// of it and assigning to one takes a `*`" (section 5). The prose's own example.
#[test]
fn a_capture_takes_the_least_the_body_asks() {
    let ttir = clean(
        // One block, and the three stand together: a capture is a borrow that
        // lasts until nothing reads the closure again, and nothing reads any
        // of these -- so no two of them are in hand at once.
        "fn f() {\n\
         \x20   var n = 0\n\
         \x20   let show = || n\n\
         \x20   let bump = || n = n + 1\n\
         \x20   let own = move || n\n\
         }\n",
    );
    let modes: Vec<TTIRCaptureMode> = ttir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Closure { captures, .. } => captures.first().map(|c| c.mode),
            _ => None,
        })
        .collect();
    assert_eq!(
        modes,
        vec![
            // `|| n` reads it.
            TTIRCaptureMode::Ref(TIRRefOp::Imm),
            // `|| n = n + 1` assigns to it.
            TTIRCaptureMode::Ref(TIRRefOp::Mut),
            // "a `move` closure captures every name by value instead".
            TTIRCaptureMode::Value,
        ]
    );
}

// A closure's parameters are slots of its own body, and a name it did not
// declare is a slot of its own too -- standing for the one outside it.
#[test]
fn a_closure_is_a_body_of_its_own() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = |x: i32| x + n\n}\n");
    let (captures, body) = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Closure { captures, body } => Some((captures.clone(), *body)),
        _ => None,
    }).expect("a closure");
    assert_eq!(captures.len(), 1);
    // The slot inside stands for the slot outside, and the two are not the same
    // number: `outer` is the frame's and `slot` is the closure's.
    let inner = &ttir.bodies[body];
    assert_eq!(inner.locals.len(), 2, "the parameter and what it caught");
    assert_eq!(captures[0].slot, 1);
    assert_eq!(captures[0].outer, 0);
}

// A name used twice is caught once.
#[test]
fn a_name_is_caught_once_however_often_it_is_used() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = || n + n + n\n}\n");
    let captures = ttir.exprs.iter().find_map(|e| match &e.kind {
        TTIRExprKind::Closure { captures, .. } => Some(captures.clone()),
        _ => None,
    }).expect("a closure");
    assert_eq!(captures.len(), 1);
}

// A closure inside a closure takes what it needs from the one that took it.
#[test]
fn a_closure_inside_a_closure_catches_through_it() {
    let ttir = clean("fn f() {\n    let n = 1\n    let g = || || n\n}\n");
    let held: Vec<usize> = ttir
        .exprs
        .iter()
        .filter_map(|e| match &e.kind {
            TTIRExprKind::Closure { captures, .. } => Some(captures.len()),
            _ => None,
        })
        .collect();
    // Both of them caught it: the inner one from the outer, and the outer one
    // from the fn.
    assert_eq!(held, vec![1, 1]);
}

// ---- Closure captures ------------------------------------------------------

// "a closure that captures by reference cannot outlive what it captured, and
// `move` is the only thing that lets one be returned" (§8). A closure is the
// one value here whose type says nothing about what is inside it, so what it
// points into is read off its captures and not off `fn(): i32`.
#[test]
fn a_closure_that_captured_by_reference_may_not_outlive_what_it_captured() {
    let out = refused(
        "fn f() {\n    var c = || 1;\n    {\n        let n = 2;\n\
         \x20       c = || n;\n    }\n}\n",
    );
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(out.contains("5 |         c = || n;"), "{}", out);
}

// And `move` is what lets it out: by value the slot is not pointed at, so there
// is nothing left in the block for the closure to outlive.
#[test]
fn a_move_closure_is_what_lets_one_out() {
    clean(
        "fn f() {\n    var c = || 1;\n    {\n        let n = 2;\n\
         \x20       c = move || n;\n    }\n}\n",
    );
}

// A closure is a value like any other, so a block does not let one out by being
// the value of a `let` either.
#[test]
fn a_closure_does_not_leave_a_block_by_being_its_value() {
    let out = refused("fn f() {\n    let c = {\n        let n = 2;\n        || n\n    };\n}\n");
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(out.contains("4 |         || n"), "{}", out);
}

// What was taken by value is followed only as far as that value went: a `move`
// closure holding a reference points where the reference pointed, and not at
// the slot the reference sat in.
#[test]
fn a_captured_value_is_followed_as_far_as_it_points() {
    let out = refused(
        "fn f(p: &i32) {\n    var c = move || p;\n    {\n        let n = 2;\n\
         \x20       let r = &n;\n        c = move || r;\n    }\n}\n",
    );
    // `n`, which `r` points at -- and not `r`, which was copied into the closure.
    assert!(out.contains("`n` does not live long enough"), "{}", out);
    assert!(!out.contains("`r` does not live long enough"), "{}", out);
}

// And what was taken by reference is followed one step further: the closure
// holds a reference to the slot, so the slot has to last, and so does whatever
// reading through it reaches.
#[test]
fn a_captured_reference_holds_the_slot_as_well_as_what_it_points_at() {
    let out = refused(
        "fn f(p: &i32) {\n    var c = move || p;\n    {\n        let n = 2;\n\
         \x20       let r = &n;\n        c = || r;\n    }\n}\n",
    );
    assert!(out.contains("`r` does not live long enough"), "{}", out);
    assert!(out.contains("`n` does not live long enough"), "{}", out);
}

// A closure that captured nothing points at nothing, whatever it is put in.
#[test]
fn a_closure_that_captured_nothing_may_go_anywhere() {
    clean("fn f() {\n    var c = || 1;\n    {\n        c = || 2;\n    }\n}\n");
}

// ---- What a closure's body may do with what it captured ---------------------

// A name captured by reference is the enclosing frame's, and handing it away
// from inside the closure would hand away what somebody else still owns. §5
// works the mode out from what the body asks -- reading takes a `&` and
// assigning takes a `*` -- and taking the value is more than either.
#[test]
fn a_name_captured_by_reference_may_not_be_handed_away() {
    let with = "struct Buf {\n    pub n: i32,\n}\nfn eat(b: Buf): i32 {\n    1\n}\n";
    let out = refused(&format!(
        "{}fn f(): i32 {{\n    let b = Buf {{ n: 1 }};\n    let c = || eat(b);\n    1\n}}\n",
        with
    ));
    assert!(out.contains("`b` cannot be moved out of a closure"), "{}", out);
    assert!(out.contains("captured it by `&`"), "{}", out);
    // "a `move` closure takes what it captures, and may give it away".
    clean(&format!(
        "{}fn f(): i32 {{\n    let b = Buf {{ n: 1 }};\n    let c = move || eat(b);\n    1\n}}\n",
        with
    ));
}

// What a closure gives back may point at what it captured -- which outlives the
// closure -- but not at anything its body declared, which does not.
#[test]
fn a_closure_may_not_give_back_a_reference_to_its_own_body() {
    let out = refused(
        "fn f(): fn(): &i32 {\n    move || {\n        let m = 1;\n        &m\n    }\n}\n",
    );
    assert!(out.contains("`m` does not live long enough"), "{}", out);
    assert!(out.contains("4 |         &m"), "{}", out);
    // A capture is the other way: it came from outside and goes on living
    // there, so giving it back is what a closure is for.
    clean("fn f(p: &i32): fn(): &i32 {\n    move || p\n}\n");
}

// ---- What calling a closure does to what it captured ------------------------

// The three fn types, worked out from what each capture asks. "worked out per
// name, each taking the least the body asks of it" (§5), and the closure is the
// most of those.
#[test]
fn a_closure_is_whichever_of_the_three_its_captures_make_it() {
    let with = "struct Buf {\n    pub n: i32,\n}\nfn eat(b: Buf): i32 {\n    1\n}\n";
    // Reads: nothing captured, or captured and only read.
    clean(&format!("{}fn f(): fn(): i32 {{\n    || 1\n}}\n", with));
    clean(&format!(
        "{}fn f(): fn(): i32 {{\n    let b = Buf {{ n: 1 }};\n    move || b.n\n}}\n",
        with
    ));
    // Writes: a capture the body assigns to. `move`, because a closure that
    // captured by reference cannot outlive what it captured (§8) and this one
    // is being handed back out of the block that declared `n`.
    clean(&format!(
        "{}fn f(): var fn(): null {{\n    var n = 1;\n    move || n = n + 1\n}}\n",
        with
    ));
    // Takes: a capture the body hands away.
    clean(&format!(
        "{}fn f(): once fn(): i32 {{\n    let b = Buf {{ n: 1 }};\n    move || eat(b)\n}}\n",
        with
    ));
}

// "a closure stands where a weaker one is wanted, and not the other way."
#[test]
fn a_closure_stands_where_a_weaker_one_is_wanted() {
    let with = "struct Buf {\n    pub n: i32,\n}\nfn eat(b: Buf): i32 {\n    1\n}\n";
    // Reading is less than taking, so a plain closure fits a `once fn`.
    clean(&format!("{}fn f(): once fn(): i32 {{\n    || 1\n}}\n", with));
    // And not the other way.
    let out = refused(&format!(
        "{}fn f(): fn(): i32 {{\n    let b = Buf {{ n: 1 }};\n    move || eat(b)\n}}\n",
        with
    ));
    assert!(out.contains("this is `once fn(): i32` and what wants it says `fn(): i32`"), "{}", out);
    assert!(out.contains("it may be called fewer times than that"), "{}", out);
    // Writing is less than taking and more than reading.
    let out = refused(&format!(
        "{}fn f(): fn(): null {{\n    var n = 1;\n    move || n = n + 1\n}}\n",
        with
    ));
    assert!(out.contains("`var fn(): null`"), "{}", out);
}

// "one call and no more": calling a `once fn` hands away what it captured, so
// the call takes the closure and a second one is a use of something that went.
#[test]
fn a_once_closure_may_be_called_once() {
    let with = "struct Buf {\n    pub n: i32,\n}\nfn eat(b: Buf): i32 {\n    1\n}\n";
    clean(&format!(
        "{}fn f(): i32 {{\n    let b = Buf {{ n: 1 }};\n    let c = move || eat(b);\n    c()\n}}\n",
        with
    ));
    let out = refused(&format!(
        "{}fn f(): i32 {{\n    let b = Buf {{ n: 1 }};\n    let c = move || eat(b);\n\
         \x20   let one = c();\n    let two = c();\n    one + two\n}}\n",
        with
    ));
    assert!(out.contains("`c` has been moved"), "{}", out);
    // And one that only reads may be called as often as anybody likes.
    clean("fn f(): i32 {\n    let n = 1;\n    let c = || n;\n    c() + c() + c()\n}\n");
}

// A fn declared with a name captures nothing, so calling it does nothing to
// what it captured however many times.
#[test]
fn a_declared_fn_reads_what_it_captured_because_it_captured_nothing() {
    let ttir = clean("fn g(): i32 {\n    1\n}\nfn f(): fn(): i32 {\n    g\n}\n");
    let f = ttir.items.iter().find_map(|i| match &i.kind {
        TTIRItemKind::Fn(f) if f.name == "g" => Some(f),
        _ => None,
    }).expect("g");
    assert!(matches!(
        &ttir.types[f.ty],
        Ty::Fn { uses: crate::tir::tir_nodes::TIRFnUses::Reads, .. }
    ));
}
