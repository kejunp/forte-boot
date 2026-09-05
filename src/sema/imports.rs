// Imports: which file a path names, and what that file lets in.
//
//     prep -> lex -> parse -> expand -> lower -> TIR -> sema
//                                                       ^^^^
//
// The first pass that reads more than one file. Everything before it works on
// the text it was handed; this one follows an `import` to the module it names,
// reads that the same way, and goes on until nothing is left to read. What it
// produces is a `ParsedSuite` for each file -- the TIR of it, what it exports,
// and what its imports bound -- and a report for each file besides, since a
// diagnostic quotes the source it was written against and every file has one
// of its own.
//
// It reads the TIR and not the AST. `lower` has already flattened an import's
// tree into one leaf per name and put the path in front of each (section 1), so
// what a group was written as is spent before this pass sees it; and every item
// arrives with its visibility already read, which is the other half of what an
// export table is made of.
//
// Three things `docs/prose.txt` section 8 leaves open are settled here, there
// being nowhere else they could be settled:
//
//   - Where a path is looked up. A module is a file: `shapes::circle` is
//     `shapes/circle.ft`, or where that is not a file, `circle` inside
//     `shapes.ft`. The longest prefix that names a file is the module and the
//     rest is what to find in it, which is what lets a namespace be reached by
//     the same path -- `suite::limits::MAX` is `MAX` in the namespace `limits`,
//     wherever `limits` happens to be written.
//   - Where `super` may climb to. The suite root is the directory the root file
//     was read from, and nothing above the suite is nameable (section 1), so a
//     `super` that would leave it is turned down where it is written.
//   - What a glob does to a name already in scope. A name written by hand wins
//     over one a glob brought in, and two globs offering one name is an error
//     at the second. A reader can see the first rule and write around it; no
//     reader can be asked to choose between two globs.

// What reads it is `sema::lower`, which takes the whole suite and lowers it
// into one tree: the `bindings` below become the names each file can see that
// it did not declare. `main::compile` is what puts the two together.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::error::{Diagnostic, Diagnostics, Source, Span};
use crate::expand::Expander;
use crate::lex::lexer::Lexer;
use crate::parse::parser::Parser;
use crate::prep::preprocess;
use crate::tir::lower::Lowerer;
use crate::tir::tir_nodes::{
    TIRBinding, TIRExprKind, TIRImportLeaf, TIRItemId, TIRItemKind, TIRProgram, TIRVis,
};

// What a module is written in. A path names a module and not a file, and this
// is the whole of the difference between the two.
const EXT: &str = "ft";

// The names the language's own syntax builds, which are brought in without
// being asked for.
//
// A literal is syntax for a type a library declares: `0..10` builds a `Range`,
// `{1: 2}` a `Map` and `{1, 2}` a `Set`, with `#` making either of the last two
// the hashed kind. The syntax is the language's and the type is not, so a file
// that wrote a range had to import the type behind it before it could -- which
// meant `for i in 0..10` did not compile in a file that had imported nothing,
// the most ordinary loop there is turned down for a reason about libraries.
//
// So these five are looked for and bound without an `import`, and nothing else
// is: the prelude is exactly what the language's own literals name, which is a
// rule rather than a list somebody keeps adding to. Each lives in the module
// named after it, lowercased -- `Range` in `range`, `HashMap` in `hashmap` --
// so a suite that writes one of these modules gets the literal working with no
// change here.
//
// A name nothing declares is passed over in silence. A suite with no library
// at all is a suite where `{1: 2}` still has nothing to build, and that is the
// error it already got; the prelude adds no requirement, it only spares an
// import where the type is there to be found.
pub const PRELUDE: &[&str] = &["Range", "Map", "HashMap", "Set", "HashSet"];

// The three words that say where a path starts (section 1). They are segments
// like any other to the parser, which is what lets `super` repeat; making them
// mean something is this pass's.
const SELF: &str = "self";
const SUPER: &str = "super";
const SUITE: &str = "suite";

// ---- What a module has to offer -------------------------------------------

// One name a module declares, and where it was written. Every one of them is
// here and not only the exported ones: a name reached from outside has to be
// found before it can be turned down for being private, and a table holding
// only what leaves could not tell "there is no such name" from "that name is
// not yours". Whether it leaves is `exported(vis)`.
//
// What kind of thing it is, this pass says; what its type is, it does not --
// see the note over the type checker's vocabulary below.
#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub vis:  TIRVis,
    // The declaration itself, for whatever wants to read it: a handle into the
    // `items` arena of the `ParsedSuite` this symbol came from.
    pub item: TIRItemId,
    pub line: usize,
    pub col:  usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SymbolKind {
    Function,
    Struct,
    Enum,
    Trait,
    Const,
    GlobalVariable,
    TypeAlias,
    // A namespace nests a module inside the one it is written in (section 1),
    // so what it holds is a table of the same shape as the one it is in.
    Namespace(Vec<Symbol>),
    // A `pub import`: the name is this module's and what it names is not.
    Reexport,
}

// One name an import bound in the module that wrote it.
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    // What the name is known by here, which is the alias where one was written.
    pub name:  String,
    // The file the name came from, and the path inside it -- empty where the
    // module itself is what was bound.
    pub home:  PathBuf,
    pub path:  Vec<String>,
    // Whether it arrived through a glob, which is what decides a clash.
    pub glob:  bool,
    // Whether nobody asked for it: a prelude name, which loses to everything.
    // A file's own declaration wins, and so does an import it wrote by hand --
    // the same way round a glob already loses (section 1), and for the same
    // reason: what is written beats what merely arrived.
    pub implicit: bool,
    // The `import` that bound it, so a `pub import` can find its own names
    // again when it comes to re-export them. A handle and not a position: a
    // leaf stands where it was written and the item stands at the `import`.
    pub via:   TIRItemId,
    pub line:  usize,
    pub col:   usize,
}

// Everything one file came to. `text` is kept because `Source` borrows rather
// than owns and every file is quoted against itself: a report about this file
// renders against this text and no other.
pub struct ParsedSuite {
    pub path:     PathBuf,
    pub text:     Vec<char>,
    pub tir:      TIRProgram,
    // Every name the file declares, private ones included -- see `Symbol`.
    pub symbols:  Vec<Symbol>,
    pub bindings: Vec<Binding>,
    pub errors:   Diagnostics,
    // Whether the file got far enough for its export table to mean anything. A
    // file that would not parse exports nothing, and holding an importer to
    // that would turn one mistake into a page of them -- so nothing is checked
    // against a module that is not sound.
    pub sound:    bool,
}

// ---- The resolver ---------------------------------------------------------

pub struct ImportResolver {
    parsed:       HashMap<PathBuf, ParsedSuite>,
    // The order they were read in, so a report reads the way the compiler ran.
    order:        Vec<PathBuf>,
    search_paths: Vec<PathBuf>,
    // The directory `suite` names, and the one nothing may climb above.
    root:         PathBuf,
    // The files being resolved, innermost last. One already in here is a cycle,
    // and what is in here is what the report shows.
    open:         Vec<PathBuf>,
}

// What came of asking for a file.
enum Load {
    Ready,
    // Already being resolved further up: the chain closed on itself.
    Cycle,
    // Nothing could be read, and what the system said about it.
    Unreadable(String),
}

impl ImportResolver {
    pub fn new(search_paths: Vec<PathBuf>) -> ImportResolver {
        ImportResolver {
            parsed: HashMap::new(),
            order: Vec::new(),
            search_paths,
            root: PathBuf::new(),
            open: Vec::new(),
        }
    }

    // Reads `file` and everything it reaches. The root file's own directory is
    // what `suite` names, there being no unit above the suite to take it from.
    // The handle it gives back is how to ask for any of it afterwards.
    //
    // The one failure that is not a `Diagnostic`: the root file is the one
    // nothing imported, so there is no `import` to point a caret at and no
    // source to quote it against. Everything else this pass turns down is in
    // the report of the file that wrote it -- see `render`.
    pub fn resolve(&mut self, file: &Path) -> Result<PathBuf, String> {
        let file = normalise(file);
        self.root = file.parent().unwrap_or(Path::new(".")).to_path_buf();
        match self.load(&file) {
            Load::Ready | Load::Cycle => {
                self.prelude();
                Ok(file)
            }
            Load::Unreadable(why) => {
                Err(format!("cannot read {}: {}", file.display(), why))
            }
        }
    }

    // The names `PRELUDE` says every file may use without asking.
    //
    // Run after the root and everything it reaches, so that a module the suite
    // already imports is found in `parsed` rather than read twice, and so that
    // a file's own imports are in place before these are put behind them.
    //
    // The bindings go on every file of the suite, the prelude modules included:
    // one of them declaring a name it would also be handed is no trouble, since
    // an implicit binding loses to a declaration.
    fn prelude(&mut self) {
        let mut bases = vec![self.root.clone()];
        bases.extend(self.search_paths.iter().cloned());

        // Only the ones the suite actually writes the syntax for. A module read
        // because it might have been wanted is a module compiled into the
        // program: these are ordinary files and their fns are ordinary fns, so
        // reading all five put six bodies nobody could call into a program that
        // was two, and made the assembly for `hello.ft` seven times longer.
        //
        // Whether a name is wanted is a question about what is written, so it
        // is asked of what is written. Round and round until nothing new is
        // read, because a prelude module may itself write a literal -- and
        // bounded by the list, since each module is read at most once.
        let mut found: Vec<(String, PathBuf)> = Vec::new();
        loop {
            let want = self.wanted();
            let mut read = false;
            for name in PRELUDE {
                if found.iter().any(|(held, _)| held == *name) || !want.contains(name) {
                    continue;
                }
                let module = name.to_lowercase();
                let Some((file, rest)) = find_module(&bases, &[module]) else { continue };
                if !rest.is_empty() {
                    continue;
                }
                // A module that will not read is not a reason to stop: the
                // suite asked for nothing here, so what it gets is what was
                // there.
                if !matches!(self.load(&file), Load::Ready | Load::Cycle) {
                    continue;
                }
                read = true;
            // Only where the module really declares it, and declares it for
            // others to see. Looking the name up now rather than leaving it to
            // `sema::lower` keeps a binding that names nothing from being made
            // at all.
                let Some(suite) = self.parsed.get(&file) else { continue };
                if !suite.symbols.iter().any(|s| s.name == **name && exported(s.vis)) {
                    continue;
                }
                found.push(((*name).to_string(), file));
            }
            if !read {
                break;
            }
        }

        for file in self.order.clone() {
            let Some(suite) = self.parsed.get_mut(&file) else { continue };
            for (name, home) in &found {
                suite.bindings.push(Binding {
                    name:     name.clone(),
                    home:     home.clone(),
                    path:     vec![name.clone()],
                    glob:     false,
                    implicit: true,
                    // Nobody wrote it, so there is no `import` it came from and
                    // nowhere to point a caret. A re-export walks `via` and
                    // finds no item here, which is right: a prelude name is not
                    // this file's to hand on.
                    via:      usize::MAX,
                    line:     0,
                    col:      0,
                });
            }
        }
    }

    // Which prelude names the suite as read so far writes the syntax for.
    //
    // One entry per literal form, and the `#` is what tells the hashed kind
    // from the ordered one -- the same reading `sema::lower::containers` makes
    // when it goes looking for the type.
    fn wanted(&self) -> Vec<&'static str> {
        let mut out: Vec<&'static str> = Vec::new();
        for suite in self.parsed.values() {
            for expr in &suite.tir.exprs {
                let held = match &expr.kind {
                    TIRExprKind::Range { .. } => "Range",
                    TIRExprKind::Map { hashed: true, .. } => "HashMap",
                    TIRExprKind::Map { hashed: false, .. } => "Map",
                    TIRExprKind::Set { hashed: true, .. } => "HashSet",
                    TIRExprKind::Set { hashed: false, .. } => "Set",
                    _ => continue,
                };
                if !out.contains(&held) {
                    out.push(held);
                }
            }
        }
        out
    }

    // The module path a file is reached by, from the suite root: `a/b/deep.ft`
    // is `a::b::deep`. A file is a module (section 1), so this is what stands
    // in front of everything the file declares -- in a path a reader writes,
    // and in the symbol a fn is compiled to (`sema::names::Mangler`).
    //
    // The stem and not the file name: `.ft` is how the file is stored and no
    // part of what the module is called, which is the same answer `find_module`
    // gives when it goes the other way.
    pub fn module_of(&self, file: &Path) -> Vec<String> {
        let file = normalise(file);
        let rest = file.strip_prefix(&self.root).unwrap_or(&file);
        let mut out: Vec<String> = rest
            .parent()
            .map(|dirs| {
                dirs.components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect()
            })
            .unwrap_or_default();
        out.push(stem(&file));
        out
    }

    // One file by the path it was read from. Only the tests below ask: a build
    // walks every file in the order they were read (`suites`) and never wants
    // one in particular, and a compiler that kept an accessor nothing calls
    // would be keeping it for the same reason nobody deleted it.
    #[cfg(test)]
    pub fn suite(&self, file: &Path) -> Option<&ParsedSuite> {
        self.parsed.get(&normalise(file))
    }

    pub fn suites(&self) -> impl Iterator<Item = &ParsedSuite> {
        self.order.iter().filter_map(|p| self.parsed.get(p))
    }

    // Whether anything anywhere stops the build. A warning does not, here as
    // everywhere else.
    pub fn has_errors(&self) -> bool {
        self.suites().any(|s| s.errors.has_errors())
    }

    // Every file's report, each quoted against its own text, in the order the
    // files were read. A file with nothing to say contributes nothing, so no
    // blank space stands where a quiet file was.
    pub fn render(&self) -> String {
        self.suites()
            .filter(|s| !s.errors.is_empty())
            .map(|s| {
                let name = s.path.display().to_string();
                s.errors.render(&Source::new(&name, &s.text))
            })
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    // ---- Reading a file --------------------------------------------------

    // Reads, parses and lowers `file`, then follows what it imports. A file
    // reached twice is read once: the second time finds it in `parsed` and
    // says so, which is also what stops a cycle from running forever.
    fn load(&mut self, file: &Path) -> Load {
        if self.open.iter().any(|p| p == file) {
            return Load::Cycle;
        }
        if self.parsed.contains_key(file) {
            return Load::Ready;
        }

        let text = match fs::read_to_string(file) {
            Ok(text) => text,
            Err(e) => return Load::Unreadable(e.to_string()),
        };
        let suite = parse_one(file.to_path_buf(), &text);
        self.order.push(file.to_path_buf());
        self.parsed.insert(file.to_path_buf(), suite);

        // The leaves are taken out before the recursion so that nothing is
        // borrowed out of `parsed` while another file is being put into it.
        // Each is a handful of strings, and there is one per name imported.
        let imports = self.imports_of(file);

        self.open.push(file.to_path_buf());
        let mut found = Diagnostics::new();
        let mut bound: Vec<Binding> = Vec::new();
        for (via, at, leaf) in imports {
            self.leaf(file, via, at, &leaf, &mut found, &mut bound);
        }
        self.open.pop();

        let suite = self.parsed.get_mut(file).expect("just inserted");
        suite.errors.absorb(&mut found);
        suite.bindings = bound;
        // A `pub import` is a re-export (section 1): the names it brought in
        // leave again under the visibility written on the import.
        let reexports = reexports_of(&suite.tir, &suite.bindings);
        suite.symbols.extend(reexports);
        Load::Ready
    }

    // Every leaf of every import in `file`, with the visibility of the import
    // it came from and the place to point a caret at.
    fn imports_of(&self, file: &Path) -> Vec<(TIRItemId, Span, TIRImportLeaf)> {
        let Some(suite) = self.parsed.get(file) else { return Vec::new() };
        let mut out = Vec::new();
        for &id in &suite.tir.roots {
            let item = &suite.tir.items[id];
            if let TIRItemKind::Import { leaves, .. } = &item.kind {
                for leaf in leaves {
                    // The leaf's own place and not the item's: a group holds
                    // several, and each is reported where it was written.
                    out.push((id, Span::at(leaf.line, leaf.col), leaf.clone()));
                }
            }
        }
        out
    }

    // ---- One leaf --------------------------------------------------------

    // What one imported name comes to: the file it is in, whether that file
    // has it, and what it is called here. Everything this turns down is
    // reported into `out`, which is the importing file's own report.
    fn leaf(
        &mut self,
        from: &Path,
        via: TIRItemId,
        at: Span,
        leaf: &TIRImportLeaf,
        out: &mut Diagnostics,
        bound: &mut Vec<Binding>,
    ) {
        let Some((bases, taken)) = self.bases(from, leaf, at, out) else { return };
        let rest = &leaf.path[taken..];
        if rest.is_empty() {
            out.push(
                Diagnostic::error(
                    format!("`{}` names no module", leaf.path.join("::")),
                    at,
                )
                .with_label("this reaches a place and stops there")
                .with_help("write what to take from it after the `::`"),
            );
            return;
        }

        let Some((file, inner)) = find_module(&bases, rest) else {
            out.push(
                Diagnostic::error(
                    format!("no module answers to `{}`", leaf.path.join("::")),
                    at,
                )
                .with_label("nothing here is a file")
                .with_help(format!("tried {}", tried(&bases, rest))),
            );
            return;
        };

        match self.load(&file) {
            Load::Ready => {}
            Load::Cycle => {
                let chain = self
                    .open
                    .iter()
                    .map(|p| short(p, &self.root))
                    .collect::<Vec<_>>()
                    .join(" -> ");
                out.push(
                    Diagnostic::error(
                        format!("`{}` is imported in a circle", leaf.path.join("::")),
                        at,
                    )
                    .with_label("this closes it")
                    .with_note(format!("{} -> {}", chain, short(&file, &self.root))),
                );
                return;
            }
            Load::Unreadable(why) => {
                out.push(
                    Diagnostic::error(
                        format!("cannot read `{}`", short(&file, &self.root)),
                        at,
                    )
                    .with_label("this names it")
                    .with_note(why),
                );
                return;
            }
        }

        // A module that would not parse exports nothing, and holding this
        // import to that would report a mistake that is somewhere else.
        let Some(target) = self.parsed.get(&file) else { return };
        if !target.sound {
            return;
        }

        if leaf.glob {
            self.glob(&file, &inner, via, at, out, bound);
        } else {
            self.named(&file, &inner, leaf, via, at, out, bound);
        }
    }

    // `import a::b::*`: every name the module or the namespace exports, each
    // bound here under the name it has there.
    fn glob(
        &self,
        file: &Path,
        inner: &[String],
        via: TIRItemId,
        at: Span,
        out: &mut Diagnostics,
        bound: &mut Vec<Binding>,
    ) {
        let suite = self.parsed.get(file).expect("loaded");
        let Some(table) = walk(&suite.symbols, inner) else {
            self.no_such(suite, inner, at, out);
            return;
        };
        for symbol in table.iter().filter(|s| exported(s.vis)) {
            let mut path = inner.to_vec();
            path.push(symbol.name.clone());
            add(
                bound,
                Binding {
                    implicit: false,
                    name: symbol.name.clone(),
                    home: file.to_path_buf(),
                    path,
                    glob: true,
                    via,
                    line: at.line,
                    col: at.col,
                },
                at,
                out,
            );
        }
    }

    // `import a::b` and `import a::b as c`: one name, which the module has to
    // have and to have exported.
    fn named(
        &self,
        file: &Path,
        inner: &[String],
        leaf: &TIRImportLeaf,
        via: TIRItemId,
        at: Span,
        out: &mut Diagnostics,
        bound: &mut Vec<Binding>,
    ) {
        let suite = self.parsed.get(file).expect("loaded");

        // Nothing after the module's own name: the module itself is what was
        // imported, and it is reached like the namespace it is (section 1).
        let name = match inner.last() {
            None => leaf
                .alias
                .clone()
                .unwrap_or_else(|| stem(file)),
            Some(last) => leaf.alias.clone().unwrap_or_else(|| last.clone()),
        };
        if !inner.is_empty() {
            let (up_to, last) = inner.split_at(inner.len() - 1);
            let Some(table) = walk(&suite.symbols, up_to) else {
                self.no_such(suite, up_to, at, out);
                return;
            };
            let Some(symbol) = table.iter().find(|s| s.name == last[0]) else {
                let known: Vec<&str> = table
                    .iter()
                    .filter(|s| exported(s.vis))
                    .map(|s| s.name.as_str())
                    .collect();
                let mut d = Diagnostic::error(
                    format!("`{}` is not in `{}`", last[0], short(file, &self.root)),
                    at,
                )
                .with_label("no such name there");
                if let Some(near) = nearest(&last[0], &known) {
                    d = d.with_help(format!("did you mean `{}`?", near));
                } else if !known.is_empty() {
                    d = d.with_help(format!("it exports {}", quoted(&known)));
                }
                out.push(d);
                return;
            };
            // It is there and it is not ours to have: `priv` is the default
            // written down, so an item with nothing on it is private too.
            if !exported(symbol.vis) {
                out.push(
                    Diagnostic::error(
                        format!("`{}` is private to `{}`", last[0], short(file, &self.root)),
                        at,
                    )
                    .with_label("this name is not exported")
                    // Where it *is* declared goes in words. A `with_secondary`
                    // would quote it, and a `Diagnostic` renders against one
                    // `Source`: the snippet would come out of this file at the
                    // other file's line, which is worse than not showing it.
                    // See the note at the foot of this module.
                    .with_note(format!(
                        "it is declared at {}:{}:{}",
                        short(file, &self.root),
                        symbol.line,
                        symbol.col
                    ))
                    .with_help("write `pub` on it, or `pub(suite)` to go no further"),
                );
                return;
            }
        }

        add(
            bound,
            Binding {
                implicit: false,
                name,
                home: file.to_path_buf(),
                path: inner.to_vec(),
                glob: false,
                via,
                line: at.line,
                col: at.col,
            },
            at,
            out,
        );
    }

    // A namespace on the way in that the module does not have.
    fn no_such(&self, suite: &ParsedSuite, inner: &[String], at: Span, out: &mut Diagnostics) {
        out.push(
            Diagnostic::error(
                format!(
                    "`{}` is not in `{}`",
                    inner.join("::"),
                    short(&suite.path, &self.root)
                ),
                at,
            )
            .with_label("no such namespace there"),
        );
    }

    // ---- Where a path starts ---------------------------------------------

    // The directories `rest` is looked up in, and how many segments the roots
    // took. A rooted path has exactly one place to look; a bare one is looked
    // up beside the file that wrote it and then along the search paths.
    fn bases(
        &self,
        from: &Path,
        leaf: &TIRImportLeaf,
        at: Span,
        out: &mut Diagnostics,
    ) -> Option<(Vec<PathBuf>, usize)> {
        let here = from.parent().unwrap_or(Path::new(".")).to_path_buf();
        let path = &leaf.path;

        let (base, taken) = match path.first().map(String::as_str) {
            Some(SUITE) => (self.root.clone(), 1),
            Some(SELF) => (here, 1),
            Some(SUPER) => {
                let mut base = here;
                let mut taken = 0;
                while path.get(taken).map(String::as_str) == Some(SUPER) {
                    // Nothing above the suite is nameable, there being nothing
                    // above it to name (section 1).
                    if normalise(&base) == self.root {
                        out.push(
                            Diagnostic::error(
                                "`super` climbs out of the suite".to_string(),
                                at,
                            )
                            .with_label("there is nothing above the suite")
                            .with_note(format!(
                                "the suite is rooted at `{}`",
                                self.root.display()
                            )),
                        );
                        return None;
                    }
                    base = match base.parent() {
                        Some(up) => up.to_path_buf(),
                        None => return None,
                    };
                    taken += 1;
                }
                (base, taken)
            }
            _ => {
                let mut bases = vec![here];
                bases.extend(self.search_paths.iter().cloned());
                return self.no_root_within(path, 0, at, out).then_some((bases, 0));
            }
        };

        self.no_root_within(path, taken, at, out)
            .then_some((vec![base], taken))
    }

    // A root is a segment like any other to the parser, which is what lets
    // `super` repeat -- and the cost is that `a::super::b` parses, a root in
    // the middle where it names nothing (section 8). Turning it down is this
    // pass's, and this is where.
    fn no_root_within(
        &self,
        path: &[String],
        from: usize,
        at: Span,
        out: &mut Diagnostics,
    ) -> bool {
        for seg in &path[from..] {
            if seg == SELF || seg == SUPER || seg == SUITE {
                out.push(
                    Diagnostic::error(
                        format!("`{}` is not the start of this path", seg),
                        at,
                    )
                    .with_label("a root stands in the middle here")
                    .with_help("`self`, `super` and `suite` say where a path starts, so one of them only begins one"),
                );
                return false;
            }
        }
        true
    }
}

// ---- Reading one file -----------------------------------------------------

// The whole of the pipeline above this pass, run over one file. Each phase is
// let go of before the next runs, in the order `main` runs them: what expansion
// makes of a tree the parser recovered through says more about the recovery
// than the source, and the same is true of what lowering makes of it.
fn parse_one(path: PathBuf, source: &str) -> ParsedSuite {
    let text: Vec<char> = source.chars().collect();
    let prepped = preprocess(source);
    debug_assert_eq!(
        source.chars().count(),
        prepped.chars().count(),
        "preprocessing must not move anything"
    );

    let mut errors = Diagnostics::new();
    let mut parser = Parser::new(Lexer::new(&prepped));
    let root = parser.parse();
    if !parser.errors().is_empty() {
        errors.absorb(&mut parser.errors().clone());
        return ParsedSuite {
            path,
            text,
            tir: TIRProgram::default(),
            symbols: Vec::new(),
            bindings: Vec::new(),
            errors,
            sound: false,
        };
    }

    let root = {
        let mut expander = Expander::new(&mut parser);
        let out = expander.expand(&root);
        if !expander.errors().is_empty() {
            errors.absorb(&mut expander.errors().clone());
            return ParsedSuite {
                path,
                text,
                tir: TIRProgram::default(),
                symbols: Vec::new(),
                bindings: Vec::new(),
                errors,
                sound: false,
            };
        }
        out
    };

    let mut lowerer = Lowerer::new(&parser);
    lowerer.lower(&root);
    let sound = lowerer.errors().is_empty();
    errors.absorb(&mut lowerer.errors().clone());
    let tir = lowerer.finish();
    let symbols = symbols_of(&tir, &tir.roots);
    ParsedSuite { path, text, tir, symbols, bindings: Vec::new(), errors, sound }
}

// ---- What a file exports --------------------------------------------------

// The items a file or a namespace declares, in the order they were written,
// whatever their visibility -- see `Symbol` for why the private ones are kept.
// An `impl` is not among them: it has no name of its own, being attached to the
// type it is written for, and is reached through that type rather than
// imported. An `import` is not either -- what a `pub import` re-exports is
// added once its own leaves have been resolved.
fn symbols_of(tir: &TIRProgram, roots: &[TIRItemId]) -> Vec<Symbol> {
    let mut out = Vec::new();
    for &id in roots {
        let item = &tir.items[id];
        let (name, kind, vis) = match &item.kind {
            TIRItemKind::Fn(f) => (f.name.clone(), SymbolKind::Function, f.vis),
            TIRItemKind::Struct { vis, name, .. } => {
                (name.clone(), SymbolKind::Struct, *vis)
            }
            TIRItemKind::Enum { vis, name, .. } => (name.clone(), SymbolKind::Enum, *vis),
            TIRItemKind::Trait { vis, name, .. } => (name.clone(), SymbolKind::Trait, *vis),
            TIRItemKind::Const { vis, name, .. } => (name.clone(), SymbolKind::Const, *vis),
            TIRItemKind::TypeAlias { vis, name, .. } => {
                (name.clone(), SymbolKind::TypeAlias, *vis)
            }
            TIRItemKind::Global { vis, name, .. } => {
                let TIRBinding::Name(name) = name else { continue };
                (name.clone(), SymbolKind::GlobalVariable, *vis)
            }
            TIRItemKind::Namespace { vis, name, items, .. } => (
                name.clone(),
                SymbolKind::Namespace(symbols_of(tir, items)),
                *vis,
            ),
            TIRItemKind::Impl { .. } | TIRItemKind::Import { .. } => continue,
        };
        out.push(Symbol { name, kind, vis, item: id, line: item.line, col: item.col });
    }
    out
}

// The names a `pub import` sends out again. The visibility is the import's own
// and not the declaration's: what a re-export of a `pub(suite)` name comes to
// is not said (section 8), so what is written here is what is written down.
fn reexports_of(tir: &TIRProgram, bindings: &[Binding]) -> Vec<Symbol> {
    let mut out = Vec::new();
    for &id in &tir.roots {
        let item = &tir.items[id];
        let TIRItemKind::Import { vis, .. } = &item.kind else { continue };
        if !exported(*vis) {
            continue;
        }
        for b in bindings.iter().filter(|b| b.via == id) {
            out.push(Symbol {
                name: b.name.clone(),
                kind: SymbolKind::Reexport,
                vis:  *vis,
                item: id,
                line: item.line,
                col:  item.col,
            });
        }
    }
    out
}

// Whether a visibility lets a name out of the module it was written in. Both
// answers that do are one answer here: everything compiled together is one
// suite, so `pub(suite)` reaches every file this pass will read, and the day
// there is a second suite is the day the two come apart.
fn exported(vis: TIRVis) -> bool {
    matches!(vis, TIRVis::Pub | TIRVis::Suite)
}

// ---- Finding the file -----------------------------------------------------

// The longest prefix of `rest` that names a file, and what is left over to
// find inside it. `a::b::c` is `a/b/c.ft` where there is one, then `c` inside
// `a/b.ft`, then `b::c` inside `a.ft` -- so a namespace is reached by the same
// path a nested file is, which is what section 1 means by a namespace nesting
// a module inside the one it is written in.
fn find_module(bases: &[PathBuf], rest: &[String]) -> Option<(PathBuf, Vec<String>)> {
    for base in bases {
        for take in (1..=rest.len()).rev() {
            let candidate = file_for(base, &rest[..take]);
            if candidate.is_file() {
                return Some((normalise(&candidate), rest[take..].to_vec()));
            }
        }
    }
    None
}

fn file_for(base: &Path, segments: &[String]) -> PathBuf {
    let mut out = base.to_path_buf();
    for seg in &segments[..segments.len() - 1] {
        out.push(seg);
    }
    out.push(format!("{}.{}", segments[segments.len() - 1], EXT));
    out
}

// What was looked for, for the reader of a report that found none of it.
fn tried(bases: &[PathBuf], rest: &[String]) -> String {
    let mut out = Vec::new();
    for base in bases {
        for take in (1..=rest.len()).rev() {
            out.push(format!("`{}`", file_for(base, &rest[..take]).display()));
        }
    }
    out.join(", ")
}

// Enough of a path to name a file in a message. Under the suite root it is
// written from there, since that is where the reader is standing.
fn short(file: &Path, root: &Path) -> String {
    file.strip_prefix(root).unwrap_or(file).display().to_string()
}

fn stem(file: &Path) -> String {
    file.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
}

// `.` and `..` spent, so that one file reached two ways is one key in the
// table. It does not touch the filesystem: a path that does not exist has to
// survive this to be named in the report that says it does not exist.
fn normalise(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for part in path.components() {
        match part {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

// ---- Reaching into a module -----------------------------------------------

// The table `segments` names, walking into a namespace for each one.
fn walk<'a>(table: &'a [Symbol], segments: &[String]) -> Option<&'a [Symbol]> {
    let mut here = table;
    for seg in segments {
        let symbol = here.iter().find(|s| s.name == *seg)?;
        let SymbolKind::Namespace(inner) = &symbol.kind else { return None };
        if !exported(symbol.vis) {
            return None;
        }
        here = inner;
    }
    Some(here)
}

// Puts one name in the module's scope, or says why it cannot. A name written
// by hand wins over one a glob brought in -- so an explicit binding quietly
// replaces a glob's and a glob quietly loses to one -- and everything else
// that collides is reported where the second one is written.
fn add(bound: &mut Vec<Binding>, binding: Binding, at: Span, out: &mut Diagnostics) {
    let Some(i) = bound.iter().position(|b| b.name == binding.name) else {
        bound.push(binding);
        return;
    };
    let held = &bound[i];
    match (held.glob, binding.glob) {
        // The one already there was written by hand: a glob does not disturb it.
        (false, true) => {}
        // This one is: it takes the place of what the glob brought in.
        (true, false) => bound[i] = binding,
        (false, false) => out.push(
            Diagnostic::error(format!("`{}` is imported twice", binding.name), at)
                .with_label("this name is already in scope")
                .with_secondary(Span::at(held.line, held.col), "it was imported")
                .with_help("write `as` on one of them to tell the two apart"),
        ),
        (true, true) => out.push(
            Diagnostic::error(format!("two globs both offer `{}`", binding.name), at)
                .with_label("this brings in a name another glob brought in")
                .with_secondary(Span::at(held.line, held.col), "the other glob is")
                .with_help("import the one that was meant by name"),
        ),
    }
}

// ---- Saying what was probably meant ---------------------------------------

// The nearest name a module actually has, where one is near enough to be worth
// naming. The same two the attribute check uses -- see `tir::lower` -- since a
// misspelling is a misspelling wherever it is written.
fn nearest(name: &str, known: &[&str]) -> Option<String> {
    let mut best: Option<(usize, &str)> = None;
    for &candidate in known {
        let d = distance(name, candidate);
        if d <= 2 && best.map_or(true, |(b, _)| d < b) {
            best = Some((d, candidate));
        }
    }
    best.map(|(_, found)| found.to_string())
}

// Levenshtein, small and plain: the words are short and a module has few.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        cur[0] = i;
        for j in 1..=b.len() {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

fn quoted(names: &[&str]) -> String {
    names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", ")
}

// ---- One report per file, and what that costs -----------------------------
// A `Diagnostic` renders against one `Source` (see `error/render.rs`), which is
// the right shape for every pass below this one: each works on the file it was
// handed and has no second one to point at. This pass has. A name imported from
// somewhere else is refused *here* and declared *there*, and the two places are
// in different files.
//
// So a report belongs to the file it is written in, and a place in another file
// is put in words -- `it is declared at shapes.ft:1:1` -- rather than quoted.
// The alternative is a `Label` that carries its own `Source`, which would let
// `with_secondary` reach across a file and quote the declaration properly. That
// is a change to `error` and not to this pass, and it is worth making the first
// time a second pass wants it.

// The tables a type checker would have wanted here are in `sema::names`
// instead: an `Info::Function` is what a `FnSig` was, an `Info::Struct` what a
// `StructDef` was, and an `Info::Variable` what a `Variable` was -- each of
// them filled from the typed tree, where the types actually are. A `Symbol`
// here carries the handle to the declaration, which is how the two meet.

#[cfg(test)]
mod tests;
