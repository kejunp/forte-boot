// What the resolver makes of a tree of files. Each test writes a suite into a
// directory of its own, resolves it, and reads back either what was bound or
// what was said about it.

use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

// A directory nothing else is using. The counter is what keeps two tests in one
// run apart, and the process id what keeps two runs apart.
fn suite(files: &[(&str, &str)]) -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("fortec-imports-{}-{}", std::process::id(), n));
    let _ = fs::remove_dir_all(&dir);
    for (name, text) in files {
        let path = dir.join(name);
        fs::create_dir_all(path.parent().expect("a parent")).expect("a directory");
        fs::write(&path, text).expect("a file");
    }
    dir
}

// Resolves the suite rooted at `main.ft` and hands back the resolver. The
// directory goes as soon as `resolve` returns: every file it read is held in
// the resolver by then -- the text among it, since a report quotes it -- and
// nothing below touches the disk again.
fn resolved(files: &[(&str, &str)]) -> (ImportResolver, PathBuf) {
    let dir = suite(files);
    let root = dir.join("main.ft");
    let mut r = ImportResolver::new(Vec::new());
    r.resolve(&root).expect("the root file");
    fs::remove_dir_all(&dir).expect("the directory to go");
    (r, root)
}

// The names the root file's imports bound, in the order they were bound.
fn bound(files: &[(&str, &str)]) -> Vec<String> {
    let (r, root) = resolved(files);
    assert_eq!(r.render(), "", "the suite was meant to be clean");
    let mut names: Vec<String> =
        r.suite(&root).expect("the root").bindings.iter().map(|b| b.name.clone()).collect();
    names.sort();
    names
}

// Everything the resolver said, rendered against the file each was written in.
fn errors(files: &[(&str, &str)]) -> String {
    let (r, _) = resolved(files);
    r.render()
}

// A path names a module and the module is a file. The longest prefix that
// names one is the module, so a nested file and a name inside a flat one are
// both reached by the path they read as.
#[test]
fn a_path_names_a_file_then_what_is_in_it() {
    assert_eq!(
        bound(&[
            ("main.ft", "import shapes::circle;\n"),
            ("shapes.ft", "pub fn circle(): i32 { 1 }\n"),
        ]),
        vec!["circle"]
    );
    // The same import, where the deeper file exists instead.
    assert_eq!(
        bound(&[
            ("main.ft", "import shapes::circle;\n"),
            ("shapes/circle.ft", "pub fn area(): i32 { 1 }\n"),
        ]),
        vec!["circle"]
    );
}

// A namespace nests a module inside the one it is written in, so it is reached
// by the same path a nested file is.
#[test]
fn a_namespace_is_reached_like_a_file() {
    assert_eq!(
        bound(&[
            ("main.ft", "import suite::limits::MAX;\n"),
            ("limits.ft", "pub const MAX: i32 = 255;\n"),
        ]),
        vec!["MAX"]
    );
    assert_eq!(
        bound(&[
            ("main.ft", "import helpers::limits::MAX;\n"),
            ("helpers.ft", "pub namespace limits {\n    pub const MAX: i32 = 255;\n}\n"),
        ]),
        vec!["MAX"]
    );
}

// The alias belongs to the leaf it renames, and a group is spelling: what the
// resolver is handed is one leaf for each name.
#[test]
fn a_group_is_spelling_and_an_alias_is_the_leaf_s() {
    assert_eq!(
        bound(&[
            ("main.ft", "import shapes::{circle, square as sq, poly::tri};\n"),
            ("shapes.ft", "pub fn circle(): i32 { 1 }\npub fn square(): i32 { 2 }\npub namespace poly {\n    pub fn tri(): i32 { 3 }\n}\n"),
        ]),
        vec!["circle", "sq", "tri"]
    );
}

// A glob takes whatever the path holds, and holds only what was exported.
#[test]
fn a_glob_takes_what_is_exported_and_no_more() {
    assert_eq!(
        bound(&[
            ("main.ft", "import shapes::*;\n"),
            ("shapes.ft", "pub fn circle(): i32 { 1 }\nfn helper(): i32 { 2 }\npub(suite) fn square(): i32 { 3 }\n"),
        ]),
        vec!["circle", "square"]
    );
}

// `super` climbs, and repeats to climb twice.
#[test]
fn super_climbs_once_per_word() {
    assert_eq!(
        bound(&[
            ("main.ft", "import a::b::deep;\n"),
            ("a/b/deep.ft", "import super::super::helpers::trim as t;\npub fn go(): i32 { 1 }\n"),
            ("helpers.ft", "pub fn trim(): i32 { 1 }\n"),
        ]),
        vec!["deep"]
    );
}

// A file reached two ways is read once, and reading it twice is not a cycle.
#[test]
fn a_file_reached_twice_is_read_once() {
    let (r, _) = resolved(&[
        ("main.ft", "import a::f;\nimport b::g;\n"),
        ("a.ft", "import shared::k;\npub fn f(): i32 { 1 }\n"),
        ("b.ft", "import shared::k;\npub fn g(): i32 { 1 }\n"),
        ("shared.ft", "pub fn k(): i32 { 1 }\n"),
    ]);
    assert_eq!(r.render(), "");
    assert_eq!(r.suites().count(), 4);
}

// ---- What it turns down ---------------------------------------------------

#[test]
fn a_module_that_is_not_there_says_what_was_looked_for() {
    let out = errors(&[("main.ft", "import shapes::circle;\n")]);
    assert!(out.starts_with("error: no module answers to `shapes::circle`"), "{}", out);
    assert!(out.contains("shapes/circle.ft"), "{}", out);
    assert!(out.contains("shapes.ft"), "{}", out);
}

#[test]
fn a_name_the_module_does_not_have_says_what_was_probably_meant() {
    let out = errors(&[
        ("main.ft", "import shapes::circel;\n"),
        ("shapes.ft", "pub fn circle(): i32 { 1 }\n"),
    ]);
    assert!(out.contains("error: `circel` is not in `shapes.ft`"), "{}", out);
    assert!(out.contains("did you mean `circle`?"), "{}", out);
}

// Nothing near enough to name gets the list instead, the module's exports
// being a closed set the way the attributes are.
#[test]
fn a_name_with_no_near_miss_gets_the_list() {
    let out = errors(&[
        ("main.ft", "import shapes::wobble;\n"),
        ("shapes.ft", "pub fn circle(): i32 { 1 }\npub fn square(): i32 { 2 }\n"),
    ]);
    assert!(out.contains("it exports `circle`, `square`"), "{}", out);
}

// "priv" is the default written down, so a name with nothing on it is private
// too -- and the declaration gets a snippet of its own.
#[test]
fn a_private_name_is_refused_and_the_declaration_is_shown() {
    let out = errors(&[
        ("main.ft", "import shapes::helper;\n"),
        ("shapes.ft", "fn helper(): i32 { 1 }\n"),
    ]);
    assert!(out.contains("error: `helper` is private to `shapes.ft`"), "{}", out);
    // In words and not quoted: the declaration is in another file, and one
    // `Diagnostic` renders against one `Source`.
    assert!(out.contains("= note: it is declared at shapes.ft:1:1"), "{}", out);
    assert!(out.contains("write `pub` on it"), "{}", out);
}

#[test]
fn a_circle_is_reported_where_it_closes() {
    let out = errors(&[
        ("main.ft", "import a::f;\n"),
        ("a.ft", "import b::g;\npub fn f(): i32 { 1 }\n"),
        ("b.ft", "import a::f;\npub fn g(): i32 { 1 }\n"),
    ]);
    assert!(out.contains("is imported in a circle"), "{}", out);
    assert!(out.contains("a.ft"), "{}", out);
    assert!(out.contains("b.ft"), "{}", out);
}

// A root is a segment like any other to the parser, which is what lets `super`
// repeat; the cost is that `a::super::b` parses, and turning it down is this
// pass's (section 8).
#[test]
fn a_root_in_the_middle_of_a_path_is_refused() {
    let out = errors(&[
        ("main.ft", "import a::super::b;\n"),
        ("a.ft", "pub fn f(): i32 { 1 }\n"),
    ]);
    assert!(out.contains("error: `super` is not the start of this path"), "{}", out);
}

// Nothing above the suite is nameable, there being nothing above it to name.
#[test]
fn super_may_not_climb_out_of_the_suite() {
    let out = errors(&[("main.ft", "import super::escape;\n")]);
    assert!(out.contains("error: `super` climbs out of the suite"), "{}", out);
}

// Two names written by hand, and no way to tell which was meant.
#[test]
fn one_name_imported_twice_is_refused() {
    let out = errors(&[
        ("main.ft", "import a::f;\nimport b::f;\n"),
        ("a.ft", "pub fn f(): i32 { 1 }\n"),
        ("b.ft", "pub fn f(): i32 { 2 }\n"),
    ]);
    assert!(out.contains("error: `f` is imported twice"), "{}", out);
    assert!(out.contains("write `as` on one of them"), "{}", out);
}

// A name written by hand wins over one a glob brought in, whichever order the
// two were written in: the reader can see the first rule and act on it.
#[test]
fn a_name_written_by_hand_beats_a_glob() {
    for main in ["import a::*;\nimport b::f;\n", "import b::f;\nimport a::*;\n"] {
        let (r, root) = resolved(&[
            ("main.ft", main),
            ("a.ft", "pub fn f(): i32 { 1 }\n"),
            ("b.ft", "pub fn f(): i32 { 2 }\n"),
        ]);
        assert_eq!(r.render(), "", "{}", main);
        let bindings = &r.suite(&root).expect("the root").bindings;
        let f = bindings.iter().find(|b| b.name == "f").expect("f");
        assert!(!f.glob, "the glob won in {:?}", main);
        assert!(f.home.ends_with("b.ft"), "{:?}", f.home);
    }
}

// Two globs offering one name is the case no rule can quietly settle.
#[test]
fn two_globs_offering_one_name_is_refused() {
    let out = errors(&[
        ("main.ft", "import a::*;\nimport b::*;\n"),
        ("a.ft", "pub fn f(): i32 { 1 }\n"),
        ("b.ft", "pub fn f(): i32 { 2 }\n"),
    ]);
    assert!(out.contains("error: two globs both offer `f`"), "{}", out);
}

// ---- Reports belong to the file they are about ----------------------------

// Every file is quoted against its own text: a diagnostic about the imported
// file renders there, and one about the import renders in the importer.
#[test]
fn a_report_is_quoted_against_the_file_it_is_about() {
    let (r, _) = resolved(&[
        ("main.ft", "import shapes::circle;\n"),
        ("shapes.ft", "%inlien\npub fn circle(): i32 { 1 }\n"),
    ]);
    let out = r.render();
    assert!(out.contains("error: unknown attribute `%inlien`"), "{}", out);
    assert!(out.contains("shapes.ft:1:1"), "{}", out);
    // The line quoted is the one in that file, not the importer's.
    assert!(out.contains("1 | %inlien"), "{}", out);
}

// A file that would not parse exports nothing, and holding the importer to
// that would turn one mistake into a page of them.
#[test]
fn a_module_that_would_not_parse_costs_the_importer_nothing() {
    let (r, _) = resolved(&[
        ("main.ft", "import shapes::circle;\n"),
        ("shapes.ft", "pub fn circle(: i32 { 1 }\n"),
    ]);
    let out = r.render();
    assert!(r.has_errors());
    // The parse error is reported where it was written...
    assert!(out.contains("shapes.ft:1"), "{}", out);
    // ...and nothing is said about the import that reached it.
    assert!(!out.contains("is not in"), "{}", out);
}

// A `pub import` is a re-export: the names it brought in leave again.
#[test]
fn a_pub_import_re_exports() {
    assert_eq!(
        bound(&[
            ("main.ft", "import middle::deep;\n"),
            ("middle.ft", "pub import inner::deep;\n"),
            ("inner.ft", "pub fn deep(): i32 { 1 }\n"),
        ]),
        vec!["deep"]
    );
    // Written without the "pub" it stays where it was, and reaching for it
    // through the middle module is refused.
    let out = errors(&[
        ("main.ft", "import middle::deep;\n"),
        ("middle.ft", "import inner::deep;\n"),
        ("inner.ft", "pub fn deep(): i32 { 1 }\n"),
    ]);
    assert!(out.contains("`deep` is not in `middle.ft`"), "{}", out);
}


// A group holds several leaves and each is reported where it was written, so
// the caret lands on the name that was wrong and not on the `import`.
#[test]
fn each_leaf_of_a_group_is_reported_where_it_stands() {
    let out = errors(&[
        ("main.ft", "import shapes::{circle, wobble, square};\n"),
        ("shapes.ft", "pub fn circle(): i32 { 1 }\npub fn square(): i32 { 2 }\n"),
    ]);
    // `wobble` begins at column 25 of the line the group is written on.
    assert!(out.contains("main.ft:1:25"), "{}", out);
    assert!(out.contains("^ no such name there"), "{}", out);
    // Only the one leaf is turned down; the two beside it are fine.
    assert_eq!(out.matches("error:").count(), 1, "{}", out);
}


// The module path a file is reached by, which is what stands in front of
// everything it declares -- in a path a reader writes and in a symbol both.
#[test]
fn a_file_knows_the_module_it_is() {
    let (r, root) = resolved(&[
        ("main.ft", "import a::b::deep;\n"),
        ("a/b/deep.ft", "pub fn go(): i32 { 1 }\n"),
    ]);
    assert_eq!(r.render(), "");
    let dir = root.parent().expect("a parent");
    assert_eq!(r.module_of(&root), vec!["main"]);
    assert_eq!(r.module_of(&dir.join("a/b/deep.ft")), vec!["a", "b", "deep"]);
}


// ---- The prelude ------------------------------------------------------------

// A literal is syntax for a type a library declares, so the syntax is the
// language's and the type is not -- and until the prelude, that meant the type
// had to be imported before the syntax worked. `for i in 0..10` did not compile
// in a file that had imported nothing, which is the most ordinary loop there is
// turned down for a reason about libraries.
//
// What is bound is exactly what the language's own literals name, and each
// comes from the module named after it, lowercased.

#[test]
fn a_range_literal_binds_the_range_type_without_an_import() {
    let held = bound(&[
        ("main.ft", "fn main() {\n    for i in 0..10 { f(i) }\n}\n"),
        ("range.ft", "pub struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n"),
    ]);
    assert_eq!(held, vec!["Range".to_string()], "{:?}", held);
}

// The hashed kinds and the ordered ones are told apart by the `#`, which is the
// same reading `sema::lower::containers` makes when it looks the type up.
#[test]
fn the_hash_decides_which_container_type_is_wanted() {
    let held = bound(&[
        ("main.ft", "fn main() {\n    let gc m = #{1: 2}\n}\n"),
        ("hashmap.ft", "pub struct HashMap<K, V> {\n    pub len: i64,\n}\n"),
        ("map.ft", "pub struct Map<K, V> {\n    pub len: i64,\n}\n"),
    ]);
    assert_eq!(held, vec!["HashMap".to_string()], "{:?}", held);
}

// **Only what is written.** A module read because it might have been wanted is
// a module compiled into the program -- its fns are ordinary fns -- so a file
// that writes no literal is handed nothing and pays nothing.
#[test]
fn a_file_that_writes_no_literal_is_handed_nothing() {
    let held = bound(&[
        ("main.ft", "fn main(): i64 {\n    1 + 2\n}\n"),
        ("range.ft", "pub struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n"),
        ("hashmap.ft", "pub struct HashMap<K, V> {\n    pub len: i64,\n}\n"),
    ]);
    assert!(held.is_empty(), "{:?}", held);
}

// And a suite with no library at all is left as it was: the prelude adds no
// requirement, it only spares an import where the type is there to be found.
#[test]
fn a_suite_with_no_library_is_left_alone() {
    let held = bound(&[("main.ft", "fn main() {\n    for i in 0..10 { f(i) }\n}\n")]);
    assert!(held.is_empty(), "{:?}", held);
}

// A name written by hand wins, which is the way round a glob already loses
// (section 1): what is written beats what merely arrived.
#[test]
fn a_declaration_of_its_own_wins_over_the_prelude() {
    let (r, root) = resolved(&[
        (
            "main.ft",
            "struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n\
             fn main() {\n    for i in 0..10 { f(i) }\n}\n",
        ),
        ("range.ft", "pub struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n"),
    ]);
    assert_eq!(r.render(), "", "the suite was meant to be clean");
    // The binding is still made -- the resolver does not know what the file
    // declared -- and it is marked as the thing that loses.
    let held = r.suite(&root).expect("the root");
    let one = held.bindings.iter().find(|b| b.name == "Range").expect("a binding");
    assert!(one.implicit, "a prelude binding must lose to what is written");
}

// The module is the one named after the type, so a suite that writes that
// module gets the literal working with no change to the compiler.
#[test]
fn the_module_is_the_one_named_after_the_type() {
    let said = errors(&[
        ("main.ft", "fn main() {\n    for i in 0..10 { f(i) }\n}\n"),
        // Named something else, so nothing is found and nothing is said: a
        // prelude name that finds no module is passed over in silence.
        ("ranges.ft", "pub struct Range<T> {\n    pub start: T,\n    pub end: T,\n}\n"),
    ]);
    assert_eq!(said, "");
}
