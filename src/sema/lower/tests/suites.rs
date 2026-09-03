// More than one file, lowered into one tree.
//
// A file used to be a program: `sema::lower` was handed one, and everything
// after it ran on what that one file came to. So an `import` resolved to a
// file, that file was compiled, and the name still did not cross -- the
// resolver had done its work and there was nobody to hand it to.
//
// What makes one tree necessary rather than merely tidy is generics. A `fn
// empty<K, V>()` declared in one file and used in another becomes a body only
// where somebody says what `K` and `V` are, and two separate programs have
// nothing to monomorphise against. So the suite is the unit, and the tests
// below are about the two things that then have to be true: a name crosses
// exactly where an import carried it, and no further.

use super::*;

// ---- A name crosses where an import carried it ------------------------------

#[test]
fn a_name_an_import_bound_is_found_in_the_file_that_bound_it() {
    let (_, said) = suite(
        &[
            ("lib", "pub fn one(): i64 {\n    1\n}\n"),
            ("user", "fn go(): i64 {\n    one()\n}\n"),
        ],
        &[Vec::new(), vec![bound("one", 0, &["one"])]],
    );
    assert!(said.is_empty(), "{:#?}", said);
}

#[test]
fn a_name_nothing_imported_is_not_found() {
    let (_, said) = suite(
        &[
            ("lib", "pub fn one(): i64 {\n    1\n}\n"),
            ("user", "fn go(): i64 {\n    one()\n}\n"),
        ],
        &[Vec::new(), Vec::new()],
    );
    assert!(
        said.iter().any(|s| s.contains("nothing is called `one`")),
        "a name crossed that nothing carried: {:#?}",
        said
    );
}

// The alias is what the importing file calls it, which is the whole of what
// `import a as b` is for.
#[test]
fn an_import_may_rename_what_it_carries() {
    let (_, said) = suite(
        &[
            ("lib", "pub fn one(): i64 {\n    1\n}\n"),
            ("user", "fn go(): i64 {\n    uno()\n}\n"),
        ],
        &[Vec::new(), vec![bound("uno", 0, &["one"])]],
    );
    assert!(said.is_empty(), "{:#?}", said);
}

// A type, not only a fn -- and a generic one, since that is the case a
// per-file program could not have done at all.
#[test]
fn a_generic_declared_in_one_file_is_used_in_another() {
    let (ttir, said) = suite(
        &[
            (
                "lib",
                "pub struct Box<T> {\n    pub held: T,\n}\n\
                 pub fn made<T>(x: T): Box<T> {\n    Box { held: x }\n}\n\
                 pub fn opened<T>(b: Box<T>): T {\n    b.held\n}\n",
            ),
            (
                "user",
                "fn go(): i64 {\n    let b = made(7)\n    opened(b)\n}\n",
            ),
        ],
        &[
            Vec::new(),
            vec![bound("Box", 0, &["Box"]), bound("made", 0, &["made"]),
                 bound("opened", 0, &["opened"])],
        ],
    );
    assert!(said.is_empty(), "{:#?}", said);
    // One tree: both files' declarations are in it, which is what leaves
    // anything for `mir::mono` to work against.
    assert_eq!(ttir.modules.len(), 2);
    assert!(ttir.modules[0].roots.len() >= 3, "{:#?}", ttir.modules);
}

// ---- And no further ---------------------------------------------------------

// Two files may both declare a name. Neither is the other's, and a bare name
// in one finds its own -- which is what makes a private helper private rather
// than a hazard.
#[test]
fn two_files_may_declare_the_same_name() {
    let (_, said) = suite(
        &[
            ("a", "fn width(): i64 {\n    4\n}\npub fn get(): i64 {\n    width()\n}\n"),
            ("b", "fn width(): i64 {\n    8\n}\npub fn get(): i64 {\n    width()\n}\n"),
        ],
        &[Vec::new(), Vec::new()],
    );
    assert!(said.is_empty(), "{:#?}", said);
}

// A full path reaches what is `pub` and nothing else. Without this an importer
// held to the visibility rule could write the path out instead and go round it.
#[test]
fn a_written_path_reaches_a_public_name() {
    let (_, said) = suite(
        &[
            ("lib", "pub fn one(): i64 {\n    1\n}\n"),
            ("user", "fn go(): i64 {\n    lib::one()\n}\n"),
        ],
        &[Vec::new(), Vec::new()],
    );
    assert!(said.is_empty(), "{:#?}", said);
}

#[test]
fn a_written_path_does_not_reach_a_private_one() {
    let (_, said) = suite(
        &[
            ("lib", "fn hidden(): i64 {\n    1\n}\npub fn one(): i64 {\n    hidden()\n}\n"),
            ("user", "fn go(): i64 {\n    lib::hidden()\n}\n"),
        ],
        &[Vec::new(), Vec::new()],
    );
    assert!(
        said.iter().any(|s| s.contains("nothing is called `lib::hidden`")),
        "a private name was reached by writing its path: {:#?}",
        said
    );
}

// ---- What each report is quoted against -------------------------------------

// A `Span` is a line and a column and says nothing about where. One report
// over several files has to know, or a caret lands under whatever happened to
// be on that line of the wrong file.
#[test]
fn a_report_is_quoted_against_the_file_it_is_about() {
    let (_, said) = suite(
        &[
            ("lib", "pub fn one(): i64 {\n    nope()\n}\n"),
            ("user", "fn go(): i64 {\n    nah()\n}\n"),
        ],
        &[Vec::new(), Vec::new()],
    );
    let about_lib = said.iter().find(|s| s.contains("nope")).expect("lib's");
    let about_user = said.iter().find(|s| s.contains("nah")).expect("user's");
    assert!(about_lib.contains("lib.ft"), "{}", about_lib);
    assert!(about_user.contains("user.ft"), "{}", about_user);
}
