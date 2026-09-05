mod gir;
mod mir;
mod sir;
mod error;
mod expand;
mod lex;
mod link;
mod parse;
mod prep;
mod tir;
mod sema;

use std::path::{Path, PathBuf};

use lex::lexer::Lexer;
use lex::tokens::TokType;
use error::Source;
use expand::Expander;
use tir::lower::Lowerer;
use parse::parser::Parser;
use prep::preprocess;
use sema::imports::{ImportResolver, ParsedSuite};
use sema::names;
use sema::scopes::Scopes;

fn dump(source: &str) {
    println!("source:\n{}\n", source);
    dump_tokens(source);
}

fn dump_tokens(source: &str) {
    let mut lexer = Lexer::new(source);
    loop {
        let tok = lexer.next_token();
        println!("{:>2}:{:<3} {:?}", tok.line, tok.col, tok.toktype);
        if tok.toktype == TokType::EOF {
            break;
        }
    }
    println!();
}

fn dump_prep(source: &str) {
    let prepped = preprocess(source);
    println!("source:\n{}\n", source);
    println!("preprocessed:\n{}\n", prepped);

    // The pass rewrites in place -- a comment is blanked rather than deleted --
    // so every character keeps its line and column.
    dump_tokens(&prepped);
    println!();
}

// Parses `source` and shows what it had to say about it. A source is held and
// quoted in the same place on purpose: every phase reports a `Span` and none of
// them knows what the text is or what it is called.
//
// The preprocessor is what makes that split necessary. The lexer reads a copy
// with the comments blanked out, and a phase quoting the text it was handed
// would show a reader a line they did not write. Blanking keeps every character
// where it was, so a span from the stripped copy lands in the written one.
//
// A parse that recovers reports more than one thing, and all of them print.
fn dump_parse(path: &str, source: &str) {
    let prepped = preprocess(source);
    debug_assert_eq!(
        source.chars().count(),
        prepped.chars().count(),
        "preprocessing must not move anything"
    );

    let mut parser = Parser::new(Lexer::new(&prepped));
    let root = parser.parse();
    let written: Vec<char> = source.chars().collect();
    if !parser.errors().is_empty() {
        println!("{}\n", parser.errors().render(&Source::new(path, &written)));
        return;
    }

    // Macros are spent before anything else looks at the tree. A parse that
    // failed does not reach here: what expansion would make of a tree the
    // parser recovered through says more about the recovery than the source.
    let mut expander = Expander::new(&mut parser);
    let root = expander.expand(&root);
    if !expander.errors().is_empty() {
        println!("{}\n", expander.errors().render(&Source::new(path, &written)));
        return;
    }

    // The tree the rest of the compiler would read. Lowering is the last pass
    // that cares how any of it was written.
    //
    // What comes next is `sema`, which turns this into the typed tree the GIR
    // is built from. `run` is the path that takes it there; this one is the
    // demo walk, which shows what one file lowers to and stops.
    let mut lowerer = Lowerer::new(&parser);
    lowerer.lower(&root);
    if !lowerer.errors().is_empty() {
        println!("{}\n", lowerer.errors().render(&Source::new(path, &written)));
        return;
    }
    let tir = lowerer.finish();
    println!(
        "{}: lowered -- {} items, {} expressions, {} types, {} patterns\n",
        path,
        tir.items.len(),
        tir.exprs.len(),
        tir.types.len(),
        tir.pats.len()
    );
}

// ---- The compiler ---------------------------------------------------------

// Compiles the suite rooted at `root`. The resolver reads that file and
// everything it reaches, so this is the first thing here that works on a suite
// rather than on a source: what a file's own passes had to say and what the
// resolver had to say about reaching it are one report per file, and they all
// come out together.
//
// `false` where the build stopped. A warning is not that, so a report that is
// not empty is not the same as a compilation that failed.
fn compile(
    root: &Path,
    search_paths: Vec<PathBuf>,
    level: sir::opt::Level,
    target: sir::target::Target,
    emit: Option<What>,
    out: Option<PathBuf>,
    runtime: Option<PathBuf>,
) -> bool {
    let mut resolver = ImportResolver::new(search_paths);
    // The one failure with no source to quote: nothing imported the root file,
    // so there is no `import` to point a caret at.
    let root = match resolver.resolve(root) {
        Ok(root) => root,
        Err(why) => {
            eprintln!("{}", why);
            return false;
        }
    };

    let said = resolver.render();
    if !said.is_empty() {
        eprintln!("{}\n", said);
    }
    if resolver.has_errors() {
        return false;
    }

    // Every file at once, turned into one typed tree. This is where the
    // compiler stops being about what was written and starts being about what
    // it means -- and where it stops being about a file.
    //
    // One tree and not one per file, which is what makes an import worth
    // writing. A generic declared in one file and used in another has to be
    // monomorphised against the use, and two separate programs have nothing to
    // monomorphise: `empty<K, V>()` in `hashmap.ft` becomes a body only where
    // somebody says what `K` and `V` are. So the suite is the unit from here
    // down, and every pass below runs once.
    let files: Vec<&ParsedSuite> = resolver.suites().collect();
    let tirs: Vec<&tir::tir_nodes::TIRProgram> = files.iter().map(|s| &s.tir).collect();
    let paths: Vec<Vec<String>> =
        files.iter().map(|s| resolver.module_of(&s.path)).collect();

    // What each file's imports bound, with the file said as a number: the
    // resolver holds a path on disk and `sema::lower` would rather not.
    let where_at = |held: &Path| files.iter().position(|s| s.path == held);
    let bound: Vec<Vec<sema::lower::Bound>> = files
        .iter()
        .map(|s| {
            s.bindings
                .iter()
                .filter_map(|b| {
                    Some(sema::lower::Bound {
                        name: b.name.clone(),
                        file: where_at(&b.home)?,
                        path: b.path.clone(),
                        implicit: b.implicit,
                    })
                })
                .collect()
        })
        .collect();

    // Every file's own name, for a report to be quoted against.
    let shown: Vec<String> = files
        .iter()
        .map(|s| {
            s.path
                .strip_prefix(root.parent().unwrap_or(Path::new(".")))
                .unwrap_or(&s.path)
                .display()
                .to_string()
        })
        .collect();
    let quoted: Vec<Source> = files
        .iter()
        .zip(shown.iter())
        .map(|(s, name)| Source::new(name, &s.text))
        .collect();
    let name = Path::new(shown.first().map(|s| s.as_str()).unwrap_or("suite"));

    {
        let (ttir, errors) =
            sema::lower::Lowerer::across(tirs, paths).lower_suite(&bound);
        if !errors.is_empty() {
            eprintln!("{}\n", errors.render_across(&quoted));
        }
        if errors.has_errors() {
            return false;
        }

        // What the checker made of it, and what every pass built on it can now
        // read: the symbols it compiles to, and the names it holds.
        let symbols = names::SymbolTable::of(&ttir);
        let scopes = Scopes::of(&ttir);

        // And the graph, which is what the tree was for: the control flow drawn
        // as edges, every release placed, and the blocks nothing reaches gone.
        let mut lowerer = gir::lower::Lowerer::new(&ttir);
        lowerer.lower();
        let mut graph = lowerer.finish();
        let copies = sema::borrows::Copies::of(&ttir);
        let generics: Vec<Vec<tir::ttir_nodes::TTIRGeneric>> = (0..graph.bodies.len())
            .map(|body| generics_of(&ttir, body))
            .collect();
        gir::drops::Drops::new(&ttir, &copies).place(&mut graph, &generics);
        let blocks: usize = graph.bodies.iter().map(|b| b.blocks.len()).sum();
        gir::opt::optimize(&mut graph);
        let left: usize = graph.bodies.iter().map(|b| b.blocks.len()).sum();

        // And the SSA, which is what the graph was for: the trees flattened,
        // the last two terminators written out as tests and a loop, and every
        // name whose address goes nowhere taken out of the frame and named
        // where it is made.
        let mut lowerer = sir::lower::Lowerer::new(&ttir, &graph);
        lowerer.lower();
        let mut ssa = lowerer.finish();
        let slots: usize = ssa.bodies.iter().map(|b| b.slots.len()).sum();
        let promoted = sir::promote::promote(&mut ssa);
        let values: usize = ssa.bodies.iter().map(|b| b.values.len()).sum();
        // And then what the program does not have to do, taken out of it. The
        // instruction count is what this moves, so it is counted either side
        // rather than at the end.
        let insts = instructions(&ssa);
        let worked = sir::opt::optimize(&mut ssa, &ttir, level, target);

        // And the machine's, which is what the SSA was for: every generic made
        // once per set of types it is used with, every type turned into a
        // number of bytes, and every register the body wanted met with the
        // ones a machine has.
        let made = mir::mono::monomorphise(&ttir, &ssa);
        for said in &made.refused {
            eprintln!("{}: {}", name.display(), said);
        }
        if !made.refused.is_empty() {
            return false;
        }
        let m = mir::machine::Machine::of(target);
        let mut lowerer = mir::lower::Lowerer::new(&made, m);
        lowerer.lower();
        // A release the lowering could not write. It does not stop the
        // compilation -- what is left is a program with one routine missing,
        // which is a link error and not a wrong answer -- but it is the
        // difference between a leak and a leak nobody mentioned.
        for said in std::mem::take(&mut lowerer.gaps) {
            eprintln!("{}: {}", name.display(), said);
        }
        let machine_ir = lowerer.finish();

        // How many of the bodies are a release rather than something somebody
        // wrote, which is what says how much of the output the compiler made
        // up out of the declarations.
        let releases =
            machine_ir.bodies.iter().filter(|body| body.symbol.starts_with("__D")).count();

        // How many types the runtime was told about. Every one of them is a
        // type the collector will read a map of rather than guess at, so the
        // number is what says how much of the heap is scanned precisely.
        let described =
            machine_ir.pool.iter().filter(|held| held.symbol.starts_with("__T")).count();

        // What the allocation came to, which is the one thing about a body that
        // is a fact about the machine rather than about the program.
        let (mut spills, mut frame, mut most) = (0usize, 0usize, 0usize);
        for body in &machine_ir.bodies {
            let mut held = mir::linear::linearise(body);
            let out = mir::regalloc::allocate(&mut held, m);
            spills += out.spills;
            most = most.max(out.most);
            frame += mir::text::frame(&held.frame, m).1;
        }

        // The stats and the names go to the error stream where something is
        // being emitted, so that what comes out of the compiler is the thing
        // and not the thing with a paragraph in front of it.
        let loose = emit.is_some() && out.is_none();
        let said = |line: String| match loose {
            true => eprintln!("{}", line),
            false => println!("{}", line),
        };
        said(format!(
            "{}: {} items, {} symbols, {} types, {} bodies, {} blocks ({} after opt), \
             {} values ({} of {} slots promoted), \
             {} instructions ({} after {:?} for {}: {} calls written out, {} loops unrolled, \
             {} lifted out of a loop, {} widened, {} folded, {} shared, {} forwarded, \
             {} dead), \
             then {} machine bodies ({} made from a generic, {} a release) on {}: \
             {} bytes of frame, {} spilled, {} registers wanted at once, \
             {} types described for the runtime",
            name.display(),
            ttir.items.len(),
            symbols.len(),
            ttir.types.len(),
            ttir.bodies.len(),
            blocks,
            left,
            values,
            promoted,
            slots,
            insts,
            instructions(&ssa),
            level,
            target.name,
            worked.inlined,
            worked.unrolled,
            worked.hoisted,
            worked.widened,
            worked.folded,
            worked.shared,
            worked.forwarded,
            worked.dead,
            machine_ir.bodies.len(),
            made.instances,
            releases,
            m.name,
            frame,
            spills,
            most,
            described
        ));
        // The assembly, and whatever the emitters would not write. Worked out
        // once: `--emit asm` writes it and a link step assembles it, and the
        // two must not be able to differ.
        let assembly = || {
            let (text, said) = mir::asm::render(&machine_ir, m);
            for one in said {
                eprintln!("{}: {}", name.display(), one);
            }
            text
        };
        // A page to read, a page to assemble, or a file to run. The last is
        // the only one that is not simply text, and it is the only one that
        // can fail here.
        match (emit, out.as_deref()) {
            (Some(what), where_to) => {
                let text = match what {
                    What::Mir => mir::text::render(&machine_ir, m),
                    What::Asm => assembly(),
                };
                match where_to {
                    Some(at) => {
                        if let Err(why) = std::fs::write(at, &text) {
                            eprintln!("could not write {}: {}", at.display(), why);
                            return false;
                        }
                    }
                    None => print!("{}", text),
                }
            }
            // Nothing named to emit and a file to make: the whole way down.
            (None, Some(at)) => {
                let Some(entry) = entry_of(&ttir) else {
                    eprintln!(
                        "{}: nothing to run -- there is no `main` taking no arguments \
                         at the top of this file, and a program needs one to start at",
                        name.display()
                    );
                    return false;
                };
                let text = assembly();
                if let Err(why) = link::link(&text, &entry, m, at, runtime.as_deref()) {
                    eprintln!("{}: {}", name.display(), why);
                    return false;
                }
            }
            (None, None) => {}
        }
        for (symbol, _) in symbols.sorted() {
            said(format!("    {}", symbol));
        }
        let _ = scopes;
    }
    true
}

// The program's own entry: `main` at the top of the root module, taking
// nothing.
//
// The root module and not any module, because a suite has one beginning and it
// is the file that was named -- a `main` in something imported is a fn called
// `main`, and two files each holding one is not two programs. And taking
// nothing, because a `main` with parameters is mangled with them and is not
// the one a process starts at; there is nowhere for an argument to come from.
//
// `answers` is whether what it hands back is a number, which is what may
// become an exit status. Everything else -- `null` above all, which is what a
// fn with no return type returns -- leaves the answer register holding
// whatever the body last put there, and that is not a status.
fn entry_of(ttir: &tir::ttir_nodes::TTIRProgram) -> Option<link::Entry> {
    use tir::tir_nodes::TIRPrim;
    use tir::ttir_nodes::{Ty, TTIRItemKind};

    // The mangler and not `TTIRFn::symbol`, which `sema::lower` leaves empty:
    // what a fn is called is worked out from where it was declared, and that
    // is a fact about the whole program rather than about the fn.
    let mangler = names::Mangler::new(ttir);
    let module = ttir.modules.first()?;
    for &item in &module.roots {
        let TTIRItemKind::Fn(f) = &ttir.items[item].kind else { continue };
        if f.name != "main" || !f.params.is_empty() {
            continue;
        }
        let answers = matches!(
            ttir.types.get(f.ret),
            Some(Ty::Prim(
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
            ))
        );
        return Some(link::Entry { symbol: mangler.symbol_of(item, ttir)?, answers });
    }
    None
}

// Every instruction the bodies can still reach, which is what `sir::opt`
// changes. The blocks it emptied are still in the arena -- nothing in this
// compiler shrinks one -- so the count is over what the entry reaches and not
// over what is there.
fn instructions(ssa: &sir::sir_nodes::SIRProgram) -> usize {
    ssa.bodies
        .iter()
        .map(|body| {
            let live = body.live();
            body.blocks
                .iter()
                .enumerate()
                .filter(|(at, _)| live[*at])
                .map(|(_, block)| block.insts.len() + block.phis.len())
                .sum::<usize>()
        })
        .sum()
}

// `fortec <root.ft> [-I <dir>]...`. A `-I` adds somewhere else to look for a
// module whose path starts at no root; the file's own directory is looked in
// first either way, and is what `suite` names.
// The declaration a body belongs to, for the parts of `gir` that answer a
// `Ty::Param` -- what a type parameter comes to is the declaration's and not
// the body's.
// What `--emit` may be asked for. Two things and they are two different
// readers: the listing is for a person and the assembly is for `as`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum What {
    Mir,
    Asm,
}

fn generics_of(p: &tir::ttir_nodes::TTIRProgram, body: usize) -> Vec<tir::ttir_nodes::TTIRGeneric> {
    for item in &p.items {
        if let tir::ttir_nodes::TTIRItemKind::Fn(f) = &item.kind {
            if f.body == Some(body) {
                return f.generics.clone();
            }
        }
    }
    Vec::new()
}

fn run(args: &[String]) -> bool {
    let mut root: Option<PathBuf> = None;
    let mut search_paths = Vec::new();
    // What is built when nothing says otherwise: everything that only removes,
    // and everything that moves code, but not the widening.
    let mut level = sir::opt::Level::default();
    // And what for: the machine this is running on, until something names
    // another. See `sir::target`, which is the only thing in this compiler
    // that has an opinion about where the program will end up.
    let mut target = sir::target::Target::default();
    // Whether to write the listing out. Off by default: what a build prints is
    // one line per file, and a back end's own page is something to be asked
    // for.
    let mut emit: Option<What> = None;
    // Where the output goes. Nothing by default, which is the shape this had
    // before there was anything to write: a build that names no file is a
    // build asking whether the program compiles.
    let mut out: Option<PathBuf> = None;
    // And what runtime to put beside it, for the one case where the archive is
    // not the one next to this compiler.
    let mut runtime: Option<PathBuf> = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "-I" => match rest.next() {
                Some(dir) => search_paths.push(PathBuf::from(dir)),
                None => {
                    eprintln!("-I wants a directory after it");
                    return false;
                }
            },
            // `-O`, `-O0` .. `-O3`. Bare `-O` is the most there is, which is
            // what it means everywhere else.
            other if other.starts_with("-O") => {
                let asked = &other[2..];
                level = match asked {
                    "" => sir::opt::Level::More,
                    _ => match asked.parse::<u8>() {
                        Ok(n) => sir::opt::Level::of(n),
                        Err(_) => {
                            eprintln!("-O wants a number after it, not `{}`", asked);
                            return false;
                        }
                    },
                };
            }
            // `--emit mir` writes the machine IR out as a listing and
            // `--emit asm` writes assembly for the target. The first is the
            // program in the order it would run, with the registers it would
            // use. There is one thing to emit, and it takes a name anyway so
            // that a second one does not need a second flag.
            "--emit" => match rest.next() {
                Some(what) if what == "mir" => emit = Some(What::Mir),
                Some(what) if what == "asm" => emit = Some(What::Asm),
                Some(what) => {
                    eprintln!("nothing to emit called `{}` (there is mir and asm)", what);
                    return false;
                }
                None => {
                    eprintln!("--emit wants a name after it");
                    return false;
                }
            },
            // `-o` is where the output goes, and what the output *is* depends
            // on whether anything was asked to be emitted: the listing or the
            // assembly where it was, and an executable where it was not.
            "-o" => match rest.next() {
                Some(at) => out = Some(PathBuf::from(at)),
                None => {
                    eprintln!("-o wants a file after it");
                    return false;
                }
            },
            "--runtime" => match rest.next() {
                Some(at) => runtime = Some(PathBuf::from(at)),
                None => {
                    eprintln!("--runtime wants an archive after it");
                    return false;
                }
            },
            "--target" => match rest.next() {
                Some(name) => match sir::target::of(name) {
                    Some(held) => target = held,
                    None => {
                        eprintln!(
                            "no such target: {} (there is {})",
                            name,
                            sir::target::NAMES.join(", ")
                        );
                        return false;
                    }
                },
                None => {
                    eprintln!("--target wants a name after it");
                    return false;
                }
            },
            other if other.starts_with('-') => {
                eprintln!("no such option: {}", other);
                return false;
            }
            other if root.is_none() => root = Some(PathBuf::from(other)),
            other => {
                eprintln!("only one root file: {} is a second", other);
                return false;
            }
        }
    }
    match root {
        Some(root) => compile(&root, search_paths, level, target, emit, out, runtime),
        None => {
            eprintln!(
                "usage: fortec <root.ft> [-o <file>] [-O<0-3>] [--target <name>] \
                 [--emit mir|asm] [--runtime <archive>] [-I <dir>]...\n\
                 \n\
                 \x20 -o with no --emit assembles and links an executable; with one \
                 it writes\n\
                 \x20 what was emitted to the file instead of the standard output."
            );
            false
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        // Nothing to compile: show what each pass makes of the language
        // instead, which is what this program was until there was a resolver
        // to hand it a file.
        demos();
        return;
    }
    if !run(&args) {
        std::process::exit(1);
    }
}

// ---- The demos ------------------------------------------------------------

// What the lexer, the parser and lowering make of a source, one piece of the
// language at a time. Run when nothing was named on the command line.
fn demos() {
    dump("let x = 25;");

    // Same program with no semicolons at all.
    dump("let x = 25\nlet y = x + 1\n");

    // Line comment: everything after // becomes spaces on the same line.
    dump_prep("let x = 25; // the answer\nlet y = x + 1\n");

    // Block comment: newlines inside it survive so later lines keep their numbers.
    dump_prep("let x = /* a\nmultiline\ncomment */ 25\n");

    // Unterminated block comment runs to end of input.
    dump_prep("let x = 1 /* never closed\n");

    // Generics: the `>>` closing a nested argument list is two tokens.
    dump("let m: Map<str, List<i32>> = empty()\n");

    // ...but a real shift still lexes as one.
    dump("let n = bits >> 2\n");

    dump("trait Show<T> {\n    fn show(&self): str\n}\n");

    dump("impl Show<i32> for Box {\n    fn show(&self): str { return \"box\" }\n}\n");

    dump("let n = c as i64 + 1;");

    dump("for i in 0..10 {}\nfor j in 0..=n {}\n");

    // A struct body holds entries, and their commas are the writer's: a newline
    // inside one inserts nothing at all.
    dump("struct P {\n    x: i32,\n    y: i32,\n}\n");

    // A struct literal is entries too, and its `}` closes a value, so the
    // `.norm()` below still continues the line.
    dump("let p = Point {\n    x: 1,\n    y: 2,\n}\n.norm()\n");

    // The two kinds of body nest: inside the arm's block a newline ends a
    // statement, while the comma ending the arm itself is written.
    dump("match x {\n    1 => {\n        f()\n        g()\n    },\n    2 => h()\n}\n");

    // `[]` is an array, `{}` with colons a map, `{}` without a set, and `#`
    // glued to either makes it hashed.
    dump("let a = [1, 2, 3]\nlet m = {1: 2, 3: 4}\nlet s = {1, 2, 3}\nlet h = #{1: 2}\n");

    // The empty map is `{}` and the empty set `{,}`; a one-element set needs no
    // trailing comma. All of them close a value, so the chain continues.
    dump("let m = {}\nlet s = {,}\nlet one = {x}\n.len()\n");

    // The same braces hold statements where a statement could stand, and the
    // separators come back with them.
    dump("let v = {\n    f()\n    g()\n}\n{\n    h()\n    k()\n}\n");

    // A call may name its type arguments, and no `::` is needed to say so: the
    // lexer looks ahead for the matching `>` and the `(` after it. The second
    // line is the comparison the first would be without that look.
    dump("let a = foo<MyType>(x)\nlet b = a < b && c > d\n");

    // `::` reaches a namespace, a module or a type; `.` reaches a value and
    // nothing else. All three meet in one name here.
    dump("let c = shapes::Color::Red.name\n");

    // A `}` ends the line it sits on, so the `-1` is a statement of its own —
    // and `->` is how to say it was not.
    dump("match x {\n    1 => a\n}\n-1\n");

    // A lone `_` is the wildcard: the match-all pattern, and the name of a
    // binding whose value is deliberately unused. `_foo` is still a name.
    dump("match x {\n    1 => a,\n    _ => b,\n}\nlet _ = f()\nfor _ in 0..3 {}\nlet _foo = 1\n");

    // A constant is worked out at compile time, so it needs both a type and a
    // value. Only a statement starts with `const`, so the brace below is a
    // block and not a map, whatever its `:` looks like.
    dump("pub const MAX: i32 = 1 << 20\nlet v = {\n    const N: i32 = 2\n    N\n}\n");

    // `&` is an immutable reference and `*` a mutable one — neither a pointer,
    // so nothing dereferences them and `a = b` writes through.
    dump("fn swap(a: *i32, b: *i32) {\n    let t = a\n    a = b\n    b = t\n}\n");

    // A reference is a type like any other, and the lexer keeps its generic
    // context open across one, so the `>>` below still splits.
    dump("let v: Vec<&str> = empty()\nlet m: Map<str, List<*Node>> = empty()\n");

    // `&&` is the logical operator where an operand ends in front of it and two
    // references where none does, so a reference to a reference is written as
    // one expects.
    dump("let rr: &&i32 = &&x\nlet ok = a && b\n");

    // `T[8]` is a raw fixed-size array — a value, copied whole — and `T[]` a
    // run of unknown length, which only a reference can hold: `&T[]` reads it
    // and `*T[]` writes to it. A slice is a run, so it is borrowed the same way.
    dump("let a: i32[8] = [1, 2, 3, 4, 5, 6, 7, 8]\nlet s: &i32[] = &a\nlet w: *i32[] = *a[1..3]\n");

    // A tuple is two or more types or values in parentheses: positional,
    // declared nowhere, and reached into by number. The comma is what makes
    // one — `(i32)` is an i32 — and a number after a `.` is an index and so a
    // whole one, which is what keeps `p.0.1` two of them rather than a float.
    dump("fn divmod(a: i32, b: i32): (i32, i32) {\n    (a / b, a % b)\n}\n");
    dump("let p: (i32, str) = (1, `one`)\nlet n = p.0\nlet d = q.0.1\n");

    // An attribute is `%name` with its arguments, and a prefix of what it
    // annotates — so no separator is inserted at the end of the list.
    dump("%inline\n%repr(C)\npub fn f();\n");

    // An impl makes methods for a struct; anything else that wants a name in
    // front of it goes in a namespace, reached with a `::` like a module.
    dump("namespace limits {\n    pub const MAX: i32 = 255\n}\nlet n = limits::MAX\n");

    // `null` is a type and its one value, so it is what a loop nobody broke
    // out of yields, and what a function with no return type returns.
    dump("let found = for x in xs {\n    if p(x) { break x }\n}\nfn log(m: str): null;\n");

    // `|` is a token of its own now: pattern alternation and a closure's
    // parameters. `||` splits into two of them where no operand precedes it.
    dump("let f = |x: i32| x * 2\nlet g = || 0\nlet ok = a || b\n");

    // A lifetime is `'a`, one token: `~` spells nothing else, so nothing has
    // to be told apart from the `'a'` of a character literal.
    dump("fn longest<'a>(x: &'a str, y: &'a str): &'a str;\nstruct Parser<'a> {\n    text: &'a str,\n}\n");

    // It stands where a type parameter stands, bounds included, and a `'_` is
    // the one with no name worth giving.
    dump("fn f<'a, 'b: 'a, T: Show + 'a>(x: &'a T) where T: 'a;\nlet p: &'_ i32 = &x\n");

    // A name for a type, generic parameters and all.
    dump("type Pair<T> = (T, T)\ntype Ref<'a> = &'a str\nlet p: Pair<i32> = (1, 2)\n");

    // A macro is declared with a word and invoked with a sigil. `$x` is one
    // token, as `%name` and `'a` are.
    dump("macro twice($x:expr) {\n    $x\n    $x\n}\nlet n = @twice(f())\n");

    // `%` is the remainder operator too, and where it stands tells them apart.
    dump("let r = a % b\n%inline\nfn f();\n");

    // A signature carries `const`, its own generic parameters and a `where`
    // clause, and bounds are joined with `+`.
    dump("const fn square(n: i32): i32 { n * n }\nimpl<T> Stack<T> where T: Ord + Show {\n    fn len(&self): i32;\n}\n");

    // A constant sizes an array, and `_` is both an inferred argument and a
    // digit separator.
    dump("const ROWS: i32 = 8\nlet grid: i32[ROWS][ROWS]\nlet v: Vec<_> = f()\nlet big = 2_147_483_647\n");

    // A number may name its own type, and the `_` in front of the suffix is
    // that same separator: `5u8` says the same thing. A float suffix on a whole
    // number makes a float of it.
    dump("let n = 5_u8\nlet r = 2.6_f32\nlet mask = 0xFF_u8\nlet w = 5_f32\n");

    // A closure captures by `&` where it reads and `*` where it writes; `move`
    // takes a copy instead. The `||` after `move` is still two `|`.
    dump("let show = || print(n)\nlet bump = || n = n + 1\nlet own = move || n + 1\n");

    // Parentheses group a type, so the other reading of a reference and a
    // suffix finally has a spelling.
    dump("let view: &i32[]\nlet refs: (&i32)[8]\n");

    // The five attributes. `%symbol` is the one the mangler makes necessary:
    // nothing outside the language can predict `3add3i323i32`.
    dump("%symbol(\"malloc\")\nfn malloc(n: u64): *u8;\n%must_use\n%noinline\nfn parse(s: str): i32;\n");

    // `never` is the empty type — no values, so an expression of it agrees
    // with anything beside it. `null` is its opposite: one value, no news.
    dump("fn panic(m: str): never;\nlet x = match c {\n    1 => 5,\n    _ => panic(\"no\"),\n}\n");

    // `unsafe` marks a fn whose caller has something to prove, and prefixes the
    // statement that answers for it — a block where there is more than one, and
    // the statement itself where there is not. Only a `{` glued to the word
    // opens a body, so the brace below is still the literal's.
    dump("pub unsafe fn write(dst: *u8[], n: u64);\nunsafe {\n    let buf = malloc(n)\n    fill(buf, n)\n}\nunsafe free(q)\nunsafe p = P { x: 1 }\n");

    // `ptr T` is a raw pointer and `addr x` makes one. Neither word ends an
    // operand, so no separator is inserted after either, and `ptr` binds
    // looser than an array suffix exactly as `&` does.
    dump("struct Buf {\n    p: ptr u8,\n}\nunsafe let q = addr b.p\nunsafe let r = q as ptr u64\n");

    // `gc` sits between the intro and the name, so it annotates the binding.
    // It ends nothing and heads no body: the braces below are still the value
    // braces a collection literal is written with.
    dump("let gc table = #{1: 2, 3: 4}\nvar gc seen = {1, 2}\nlet gc_root = 1\n");

    // What the parser makes of a source it can take, and of five it cannot.
    // Each mistake is shown against the line it was written on.
    dump_parse("ok.ft", "fn main() {\n    let x = 1  // fine\n    g(x)\n}\n");

    // A comment on the line a mistake is on. The parse never sees it -- it was
    // blanked out before the lexer ran -- and the quoted line has it back.
    dump_parse("note.ft", "fn main() {\n    let x = /* huh */ ;  // why\n}\n");

    // A type is wanted and an `=` is written: the caret sits on the token the
    // tables turned down, and the margin says what was being written.
    dump_parse("annot.ft", "fn main() {\n    let x: = 5\n}\n");

    // A near-miss the language has a rule about, rather than a slip: `;` where
    // the entries of a struct are separated by `,`.
    dump_parse("field.ft", "struct P {\n    x: i32,\n    y: i32;\n}\n");

    // The `}` that gave it away is two lines from the `(` that caused it, so
    // the opener gets a snippet of its own.
    dump_parse("args.ft", "fn main() {\n    f(1, 2\n}\n");

    // A token the lexer gave up inside of: the caret runs to the end of the
    // line, which is as far as the reader can see it.
    dump_parse("string.ft", "fn main() {\n    let s = \"unclosed\n}\n");

    // Another it gave up inside of: a word glued to a number that names no
    // type. The twelve that would have are spelled out, the set being closed.
    dump_parse("suffix.ft", "fn main() {\n    let n = 5_u9\n}\n");

    // One mistake does not hide the next: the parse recovers and goes on, and
    // both are reported against their own lines.
    dump_parse("two.ft", "fn a() { let x = ; }\nfn b() { let y = ; }\n");

    // A macro is spent before anything else sees the tree, and what it says
    // when it cannot be is a diagnostic like any other.
    dump_parse("macro.ft", "macro twice($x:expr) {\n    $x\n    $x\n}\nfn main() {\n    @twice(f());\n}\n");
    dump_parse("nomacro.ft", "fn main() {\n    @nope(1);\n}\n");
    dump_parse("arity.ft", "macro one($x:expr) {\n    $x\n}\nfn main() {\n    @one(1, 2);\n}\n");
    dump_parse("frag.ft", "macro n($x:ident) {\n    $x\n}\nfn main() {\n    @n(1 + 2);\n}\n");

    // An import is a tree of the names it reaches, and lowering flattens it: a
    // group is spelling, and what comes out is one leaf for each name.
    dump_parse(
        "import.ft",
        "pub import shapes::{circle, square::*, poly::{tri, quad}};\n\
         import super::super::helpers::trim as t;\n\
         import suite::limits::MAX;\n\
         pub(suite) fn area(): i32 { suite::limits::MAX }\n\
         impl Buf {\n\
             pub fn len(&self): i32;\n\
             pub fn clear(*self);\n\
             fn into_vec(self): Vec<u8>;\n\
         }\n\
         namespace n { type T = i32 }\n",
    );

    // The closed set of attributes is checked while the GIR is built: a name
    // the compiler does not know is an error naming what was probably meant.
    dump_parse("attr.ft", "%inlien\nfn f();\n");
    dump_parse("target.ft", "%symbol(\"s\")\nstruct P {\n    x: i32,\n}\n");

    // `gc` says the collector owns what the binding holds, so what stands under
    // one has to be something to collect: a map, a set, or a pointer to one.
    dump_parse("gc.ft", "let gc table = #{1: 2, 3: 4}\nfn main() {\n    let gc seen = {1, 2}\n}\n");

    // A number is not collected, and the caret sits on what was written where
    // the value should have been.
    dump_parse("gcnum.ft", "fn main() {\n    let gc n = 1\n}\n");
    dump_parse("gcref.ft", "fn main() {\n    let gc r: &i32 = f()\n}\n");

    // A pointer is the other thing it holds, and `addr` still answers to the
    // `unsafe` around it: the two words are about the same statement and say
    // different things.
    dump_parse("gcaddr.ft", "fn f(b: Buf) {\n    let gc p = addr b.p\n}\n");
    dump_parse("gcok.ft", "fn f(b: Buf) {\n    unsafe let gc p = addr b.p\n}\n");

    // Simplification: the arithmetic folds, the fold settles the branch, the
    // branch leaves one value, and the value lands where the name was.
    dump_parse("opt.ft", "fn main() {\n    let n = if 2 * 3 > 5 { 10 + 1 } else { 0 }\n    g(n);\n    return;\n    h();\n}\n");
}
