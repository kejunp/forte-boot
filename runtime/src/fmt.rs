// Printing, and the formatting behind it -- which is Rust's, not one invented
// here.
//
// `std/fmt.ft` is the Forte half and this is what it calls. The reason the
// work is on this side is the reason the containers are: the language cannot
// yet write it. `println!` is a macro that reads its format string while the
// program is being compiled, and a Forte macro takes a fixed list of
// `$name:fragment` and has no repetition (`src/expand.rs`), so there is no
// spelling of one that takes a format string and however many arguments follow
// it. So the format string is read while the program runs, here, by a parser
// that answers to the same grammar `format_args!` does.
//
// What is Rust's is not only the grammar. Every value is turned into text by
// the `Display`, `Debug`, `LowerHex`, `Binary`, `Octal` and `LowerExp` that
// Rust already has for the type it decodes to, through `format!` -- so
// `{:.3}` of a float rounds the way Rust rounds, `{:x}` of a negative integer
// is the two's complement Rust prints, and `{}` of `1.0` is `1` while `{:?}`
// of it is `1.0`, because those are the two impls and not a choice made here.
// Width, fill and alignment are applied afterwards, over what came back.
//
// **A format string is not checked until it runs.** `println!` cannot be given
// a bad one -- the macro would not compile -- and this can, there being no
// compiler pass that reads a Forte string literal. So a mistake in one is a
// thing that happens to a running program, and what happens is: the placeholder
// is written out as it was written, a line saying what was wrong goes to the
// standard error, and the program carries on. Nothing panics and nothing is
// silently dropped, because a print that took the program down would be worse
// than the mistake, and one that printed nothing would hide it.

use std::io::Write as _;

// ---- What crosses the boundary ---------------------------------------------

// A Forte `str`, which is a pointer and a length -- the same two words Rust's
// own `&str` is, in the same order (`mir::layout`, `fat`).
//
// It is read through a pointer and not taken by value: this compiler hands
// every aggregate over as the address of a copy it made, whatever the platform
// would do with the value itself, so a Rust signature that took one by value
// would be reading two registers the caller never filled.
#[repr(C)]
pub struct Str {
    pub(crate) at:  *const u8,
    pub(crate) len: i64,
}

// A `&dyn Show`: where the value is, and where the routines that answer for it
// are, in that order. That is `mir::layout`'s `fat` for a reference to a
// `Ty::Dyn`, and it is what `mir::lower` reads a call through one out of.
//
// It used to be an `Arg` here -- a struct with a tag saying which of four
// fields meant anything, which every caller built at the call by writing
// `int(x)` or `text(s)`. The tag was the dispatch, because there was no other
// kind: `std/fmt.ft` said so and said what it was waiting for, and what it was
// waiting for arrived. A value is now asked what it looks like, and this is
// what asking looks like from here.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Object {
    data:  *const u8,
    table: *const Shows,
}

// The one member `Show` declares, at place 0 of the table -- "a table is a run
// of addresses and nothing says which is which, so the two ends agree by
// counting" (`mir::lower`). The receiver goes in front of what the signature
// says, so this is `fn show(&self, into: &Sink)`.
type Shows = unsafe extern "C" fn(*const u8, *mut Sink);

// What `std/fmt.ft` hands over: a `&(&dyn Show)[]`, which is a view -- an
// address and a length -- and crosses as the address of those two words, this
// compiler handing every aggregate over as the address of a copy.
//
// A view and not a pointer and a count, which is what the `Arg` version took.
// The reason that one took two was that it had a `Vec` to read them off; there
// is no `Vec` any more, the arguments arriving as a view already.
#[repr(C)]
pub struct Objects {
    at:  *const Object,
    len: i64,
}

// Where a value writes itself.
//
// The runtime's, and opaque to the program: what crosses is the address of one
// and the five `__rt_show_*` below are the only things that may be handed it.
// So a value that has no idea how a float is spelled still writes one, and
// nothing in the language had to learn to render a number.
pub struct Sink {
    out:     String,
    // Taken by the first write and default for every one after it. A spec
    // belongs to a value written as one thing -- `{:x}` of a number says what
    // that number looks like -- and a value made of several parts has no one
    // number for it to be about. So the first part gets what was asked for,
    // the rest get what nobody asked about, and `one` says something where the
    // spec was particular and the value was not.
    spec:    Option<Spec>,
    // How many pieces were written, and whether the first was a number: `pad`
    // leans a number right and everything else left where nothing says.
    writes:  usize,
    numeric: bool,
    // What went wrong inside a write, there being no way to hand an error back
    // through a C call the program made.
    wrong:   Option<String>,
}

// What a value writes itself as, one piece at a time.
enum Value<'a> {
    Int(i64),
    Uint(u64),
    Real(f64),
    Truth(bool),
    Text(&'a str),
}

impl Sink {
    fn new(spec: Spec) -> Sink {
        Sink { out: String::new(), spec: Some(spec), writes: 0, numeric: false, wrong: None }
    }

    // One piece of a value. The first takes the spec and says whether the
    // whole is to be treated as a number.
    fn wrote(&mut self, v: Value<'_>) {
        let numeric = matches!(v, Value::Int(_) | Value::Uint(_) | Value::Real(_));
        if self.writes == 0 {
            self.numeric = numeric;
        }
        self.writes += 1;
        let spec = self.spec.take().unwrap_or_default();
        match body(&v, &spec) {
            Ok(text) => self.out.push_str(&text),
            // The first mistake and not the last: what a reader wants is the
            // thing that went wrong, and a second complaint about the same
            // value is the same complaint.
            Err(why) => {
                if self.wrong.is_none() {
                    self.wrong = Some(why);
                }
            }
        }
    }
}

// Whether a spec asked anything about the value itself, as against the room
// around it. Width, fill and alignment are the room and apply to whatever came
// out; the rest are about a number or a piece of text and mean nothing said of
// a value written in several parts.
fn particular(s: &Spec) -> bool {
    s.plus || s.alt || s.precision.is_some() || s.kind != Kind::Display
}

// One value, written out by whatever answers for it, with the spec applied.
//
// Every call here is a call into the program: the table is the one `mir::mono`
// built, the entry is a plain C function, and the receiver goes first. Nothing
// is done about a table that is not one -- a null is checked and anything else
// is the program having handed over something that is not a `&dyn Show`, which
// no check here could tell from one that is.
fn asked(obj: &Object, spec: Spec) -> Sink {
    let mut sink = Sink::new(spec);
    if obj.table.is_null() || obj.data.is_null() {
        sink.wrong = Some("this is not a value that can be written".to_string());
        return sink;
    }
    let show = unsafe { *obj.table };
    unsafe { show(obj.data, &mut sink) };
    sink
}

impl Str {
    // The bytes as a `&str`, or `None` where there are none to read or they are
    // not text. A null pointer is not a failure worth a message: it is what an
    // empty string may be, and an empty string reads as one.
    pub(crate) fn read(&self) -> Option<&str> {
        if self.len == 0 {
            return Some("");
        }
        if self.at.is_null() || self.len < 0 {
            return None;
        }
        // Safe as far as anything here can be: the caller wrote both halves out
        // of one `str` value, and the length is the one the compiler put beside
        // the pointer.
        let bytes = unsafe { std::slice::from_raw_parts(self.at, self.len as usize) };
        std::str::from_utf8(bytes).ok()
    }
}

// ---- The grammar -----------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Align {
    Left,
    Middle,
    Right,
}

// Which of Rust's traits the value is to be written with.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Display,
    Debug,
    LowerHex,
    UpperHex,
    Binary,
    Octal,
    LowerExp,
    UpperExp,
}

// Everything one `{...}` asked for, in the order `format_spec` writes it.
#[derive(Clone, Copy)]
struct Spec {
    fill:      char,
    align:     Option<Align>,
    plus:      bool,
    alt:       bool,
    zero:      bool,
    width:     Option<usize>,
    precision: Option<usize>,
    kind:      Kind,
}

impl Default for Spec {
    fn default() -> Spec {
        Spec {
            fill:      ' ',
            align:     None,
            plus:      false,
            alt:       false,
            zero:      false,
            width:     None,
            precision: None,
            kind:      Kind::Display,
        }
    }
}

// `[[fill]align][sign]['#']['0'][width]['.'precision][type]`, which is
// `std::fmt`'s own line for it.
//
// `args` is there for the `N$` counts, which name an argument rather than
// carrying a number: `{:1$}` is as wide as argument one says.
fn spec_of(text: &str, args: &[Object]) -> Result<Spec, String> {
    let mut out = Spec::default();
    let held: Vec<char> = text.chars().collect();
    let mut at = 0usize;

    // The fill is only a fill if something aligns after it, which is what lets
    // `{:<8}` and `{:*<8}` be told apart without looking ahead any further.
    let align_of = |c: char| match c {
        '<' => Some(Align::Left),
        '^' => Some(Align::Middle),
        '>' => Some(Align::Right),
        _ => None,
    };
    if held.len() >= 2 {
        if let Some(a) = align_of(held[1]) {
            out.fill = held[0];
            out.align = Some(a);
            at = 2;
        }
    }
    if out.align.is_none() {
        if let Some(&c) = held.first() {
            if let Some(a) = align_of(c) {
                out.align = Some(a);
                at = 1;
            }
        }
    }

    // `-` is accepted and means nothing, which is what `std::fmt` does with it.
    match held.get(at) {
        Some('+') => {
            out.plus = true;
            at += 1;
        }
        Some('-') => at += 1,
        _ => {}
    }
    if held.get(at) == Some(&'#') {
        out.alt = true;
        at += 1;
    }
    // The `0` before a width is the flag; a `0` that is the width itself has
    // nothing after it to be a flag for. `{:0}` is the flag and no width, as in
    // Rust.
    if held.get(at) == Some(&'0') {
        out.zero = true;
        at += 1;
    }

    out.width = count(&held, &mut at, args)?;
    if held.get(at) == Some(&'.') {
        at += 1;
        out.precision = match count(&held, &mut at, args)? {
            Some(n) => Some(n),
            // `{:.}` is a precision of nothing at all, which Rust reads as
            // zero.
            None => Some(0),
        };
    }

    let rest: String = held[at..].iter().collect();
    out.kind = match rest.as_str() {
        "" => Kind::Display,
        "?" => Kind::Debug,
        "x" => Kind::LowerHex,
        "X" => Kind::UpperHex,
        "b" => Kind::Binary,
        "o" => Kind::Octal,
        "e" => Kind::LowerExp,
        "E" => Kind::UpperExp,
        // `x?` and `X?` are Rust's hexadecimal debug, and what they do to
        // anything here is what `?` does -- nothing decoded here has a
        // derived `Debug` with integers inside it to be shown in hex.
        "x?" | "X?" => Kind::Debug,
        other => return Err(format!("`{}` is not a kind of formatting", other)),
    };
    Ok(out)
}

// A width or a precision: digits, or `N$` naming the argument that carries it.
fn count(held: &[char], at: &mut usize, args: &[Object]) -> Result<Option<usize>, String> {
    let from = *at;
    while held.get(*at).is_some_and(|c| c.is_ascii_digit()) {
        *at += 1;
    }
    if from == *at {
        return Ok(None);
    }
    let digits: String = held[from..*at].iter().collect();
    let n: usize = digits
        .parse()
        .map_err(|_| format!("`{}` is too large to be a width or a precision", digits))?;

    if held.get(*at) != Some(&'$') {
        return Ok(Some(n));
    }
    *at += 1;
    // `{:1$}` is as wide as argument one, which has to be there and has to be
    // a number that a width can be.
    //
    // Asked the way every other argument is asked -- written out and read back
    // -- because writing itself is the only thing a value here does. So what
    // counts as a whole number is what writes itself as the digits of one,
    // which is exactly the values a width was ever going to be taken from.
    let Some(arg) = args.get(n) else {
        return Err(format!("`{}$` names argument {}, and there is no such argument", n, n));
    };
    let held = asked(arg, Spec::default());
    match held.out.parse::<usize>() {
        Ok(v) => Ok(Some(v)),
        Err(_) => Err(format!("`{}$` names argument {}, which is not a whole number", n, n)),
    }
}

// ---- Writing one value out -------------------------------------------------

// The value itself, with everything the spec says about the value and nothing
// it says about the room around it. `format!` does the work, so what comes back
// is what Rust's own impl for the type would have written.
fn body(v: &Value, s: &Spec) -> Result<String, String> {
    let plus = |held: String, negative: bool| match s.plus && !negative {
        true => format!("+{}", held),
        false => held,
    };
    // Rust's `#` writes the prefix in lower case for both hexadecimals.
    let alt = |held: String, prefix: &str| match s.alt {
        true => format!("{}{}", prefix, held),
        false => held,
    };

    Ok(match (v, s.kind) {
        // A whole number, and the two's complement for anything but the two
        // that read it as a number -- `{:x}` of -1 is `ffffffffffffffff`, which
        // is Rust's answer and not a choice made here.
        (Value::Int(n), Kind::Display | Kind::Debug) => plus(n.to_string(), *n < 0),
        (Value::Int(n), Kind::LowerExp) => plus(format!("{:e}", n), *n < 0),
        (Value::Int(n), Kind::UpperExp) => plus(format!("{:E}", n), *n < 0),
        (Value::Int(n), k) => radix(*n as u64, k, &alt)?,

        (Value::Uint(n), Kind::Display | Kind::Debug) => plus(n.to_string(), false),
        (Value::Uint(n), Kind::LowerExp) => plus(format!("{:e}", n), false),
        (Value::Uint(n), Kind::UpperExp) => plus(format!("{:E}", n), false),
        (Value::Uint(n), k) => radix(*n, k, &alt)?,

        // A float has a precision and a whole number does not, and `{}` and
        // `{:?}` of one differ -- `1.0` prints as `1` and debugs as `1.0`.
        (Value::Real(x), Kind::Display) => plus(
            match s.precision {
                Some(p) => format!("{:.*}", p, x),
                None => format!("{}", x),
            },
            x.is_sign_negative(),
        ),
        (Value::Real(x), Kind::Debug) => plus(
            match s.precision {
                Some(p) => format!("{:.*?}", p, x),
                None => format!("{:?}", x),
            },
            x.is_sign_negative(),
        ),
        (Value::Real(x), Kind::LowerExp) => plus(
            match s.precision {
                Some(p) => format!("{:.*e}", p, x),
                None => format!("{:e}", x),
            },
            x.is_sign_negative(),
        ),
        (Value::Real(x), Kind::UpperExp) => plus(
            match s.precision {
                Some(p) => format!("{:.*E}", p, x),
                None => format!("{:E}", x),
            },
            x.is_sign_negative(),
        ),
        (Value::Real(_), _) => {
            return Err("a float cannot be written in hexadecimal, binary or octal".to_string());
        }

        (Value::Truth(b), Kind::Display | Kind::Debug) => b.to_string(),
        (Value::Truth(_), _) => {
            return Err("a bool can only be written with `{}` or `{:?}`".to_string());
        }

        // A precision truncates a string, counted in characters as Rust counts
        // it -- so it never cuts one in half.
        (Value::Text(t), Kind::Display) => match s.precision {
            Some(p) => t.chars().take(p).collect(),
            None => (*t).to_string(),
        },
        (Value::Text(t), Kind::Debug) => match s.precision {
            Some(p) => format!("{:?}", t.chars().take(p).collect::<String>()),
            None => format!("{:?}", t),
        },
        (Value::Text(_), _) => {
            return Err("a string can only be written with `{}` or `{:?}`".to_string());
        }
    })
}

fn radix(n: u64, k: Kind, alt: &dyn Fn(String, &str) -> String) -> Result<String, String> {
    Ok(match k {
        Kind::LowerHex => alt(format!("{:x}", n), "0x"),
        Kind::UpperHex => alt(format!("{:X}", n), "0x"),
        Kind::Binary => alt(format!("{:b}", n), "0b"),
        Kind::Octal => alt(format!("{:o}", n), "0o"),
        // The four above are every kind that reaches here.
        _ => unreachable!("a kind that is not a radix"),
    })
}

// The room around the value: the width, and what fills it.
//
// Two ways to fill, and they are not the same. `0` pads *inside* the sign and
// the `0x`, so `{:08}` of -42 is `-0000042` and not `000-0042`; everything else
// pads outside, on whichever side the alignment says.
//
// Where both are written the zero flag wins and the alignment is not consulted,
// which is Rust's rule and not the one it reads as: `{:<08}` of -42 is
// `-0000042` and not a number leaning against eight columns of space.
fn pad(held: String, s: &Spec, numeric: bool) -> String {
    let Some(width) = s.width else { return held };
    let wide = held.chars().count();
    if wide >= width {
        return held;
    }
    let room = width - wide;

    if s.zero {
        let prefix = prefix_of(&held);
        let (head, rest) = held.split_at(prefix);
        return format!("{}{}{}", head, "0".repeat(room), rest);
    }

    // A number stands to the right of its room and everything else to the left,
    // which is what `std::fmt` does when nothing says otherwise.
    let align = s.align.unwrap_or(match numeric {
        true => Align::Right,
        false => Align::Left,
    });
    let fill: String = std::iter::repeat_n(s.fill, room).collect();
    match align {
        Align::Left => format!("{}{}", held, fill),
        Align::Right => format!("{}{}", fill, held),
        Align::Middle => {
            let left: String = std::iter::repeat_n(s.fill, room / 2).collect();
            let right: String = std::iter::repeat_n(s.fill, room - room / 2).collect();
            format!("{}{}{}", left, held, right)
        }
    }
}

// How many bytes at the front of a rendered number the zero flag must not get
// in front of: the sign, and the `0x` or `0b` or `0o` an alternate wrote.
fn prefix_of(held: &str) -> usize {
    let mut at = 0;
    if held.starts_with('+') || held.starts_with('-') {
        at = 1;
    }
    let rest = &held[at..];
    if rest.len() >= 2 && rest.starts_with('0') {
        if let Some(c) = rest.as_bytes().get(1) {
            if matches!(c, b'x' | b'X' | b'b' | b'o') {
                at += 2;
            }
        }
    }
    at
}

// What `{}` of one argument comes to, for a caller outside this file.
//
// `test` reports the two sides of a failed assertion with it, so that a value
// reads there exactly the way it reads in the `println` beside it rather than
// in a second spelling written for assertions.
pub(crate) fn shown(obj: &Object) -> String {
    let held = asked(obj, Spec::default());
    match held.wrong {
        Some(why) => format!("<{}>", why),
        None => held.out,
    }
}

// Whether two arguments are the same value.
//
// What each of them looks like, compared -- and that is a change of meaning
// worth saying out loud. It used to compare the tag and the payload, so
// `int(1)` and `uint(1)` were two different things written by somebody who
// meant two different things. There is no tag now: what a value is, is what it
// answers with, so what an assertion compares is what it is about to print.
//
// Within one type -- and `assert_eq` takes a bound, so both sides are one type
// -- this is the same answer for every primitive the language has. Where it
// differs it differs the useful way: `0.1 + 0.2` and `0.3` are two lines of
// digits and not one, and a reader told they are equal has been told something
// untrue about the program.
pub(crate) fn same(a: &Object, b: &Object) -> bool {
    let (a, b) = (asked(a, Spec::default()), asked(b, Spec::default()));
    a.wrong.is_none() && b.wrong.is_none() && a.out == b.out
}

// ---- The format string -----------------------------------------------------

// What the whole of it comes to, and everything that was wrong with it.
//
// The two are answered together rather than one or the other, because a
// mistake in one placeholder says nothing about the rest of the line: a format
// string with a bad `{:q}` in the middle still has a beginning and an end that
// the reader wrote and wants to see.
fn render(fmt: &str, args: &[Object]) -> (String, Vec<String>) {
    let mut out = String::new();
    let mut wrong = Vec::new();
    // Which argument an empty `{}` takes, which is the next one nobody named.
    let mut next = 0usize;

    let held: Vec<char> = fmt.chars().collect();
    let mut at = 0usize;
    while at < held.len() {
        let c = held[at];
        // `{{` and `}}` are the two braces spelled twice, and are the only way
        // to write one.
        if c == '{' && held.get(at + 1) == Some(&'{') {
            out.push('{');
            at += 2;
            continue;
        }
        if c == '}' && held.get(at + 1) == Some(&'}') {
            out.push('}');
            at += 2;
            continue;
        }
        if c == '}' {
            wrong.push("a `}` closes nothing; a written one is spelled `}}`".to_string());
            out.push('}');
            at += 1;
            continue;
        }
        if c != '{' {
            out.push(c);
            at += 1;
            continue;
        }

        // A placeholder, which runs to the first `}` after it.
        let Some(end) = held[at..].iter().position(|&c| c == '}').map(|n| at + n) else {
            wrong.push("a `{` was never closed".to_string());
            out.extend(&held[at..]);
            break;
        };
        let inner: String = held[at + 1..end].iter().collect();
        let written: String = held[at..=end].iter().collect();
        at = end + 1;

        match one(&inner, args, &mut next) {
            Ok(text) => out.push_str(&text),
            Err(why) => {
                wrong.push(format!("{}: {}", written, why));
                // What the reader wrote, so the line still lines up with the
                // format string they are about to go and look at.
                out.push_str(&written);
            }
        }
    }
    (out, wrong)
}

// One placeholder: which argument, and what to do with it.
fn one(inner: &str, args: &[Object], next: &mut usize) -> Result<String, String> {
    let (which, rest) = match inner.split_once(':') {
        Some((which, rest)) => (which.trim_end(), Some(rest)),
        None => (inner.trim_end(), None),
    };

    // `{}` takes the next one nobody asked for by number, and `{2}` asks. A
    // name is not answerable: nothing here has one, there being no way to write
    // `println("{x}")` and say what `x` is.
    let at = match which {
        "" => {
            let at = *next;
            *next += 1;
            at
        }
        digits if digits.chars().all(|c| c.is_ascii_digit()) => digits
            .parse::<usize>()
            .map_err(|_| format!("`{}` is too large to be an argument", digits))?,
        name => {
            return Err(format!(
                "`{}` names an argument, and an argument here has a number and no name",
                name
            ));
        }
    };
    let Some(arg) = args.get(at) else {
        return Err(match args.len() {
            0 => format!("there is no argument {}, nothing having been handed over", at),
            1 => format!("there is no argument {}; there is one argument, numbered 0", at),
            n => format!("there is no argument {}; the arguments are 0 to {}", at, n - 1),
        });
    };

    let spec = spec_of(rest.unwrap_or(""), args)?;
    let held = asked(arg, spec);
    // A spec about the value, said of a value written in more than one piece.
    // Asked before what went wrong inside, because this is *why* it went
    // wrong: the first piece took the spec, and a `{:x}` that reached the
    // "Point { x: " of a struct is a complaint about text that would tell the
    // reader nothing about the mistake they made.
    if particular(&spec) && held.writes > 1 {
        return Err("this writes itself in several pieces, and the spec is about \
                    one thing"
            .to_string());
    }
    if let Some(why) = held.wrong {
        return Err(why);
    }
    Ok(pad(held.out, &spec, held.numeric))
}

// ---- What the program calls ------------------------------------------------

// What a call asked for, in one word: whether a newline goes on the end -- the
// difference between `print` and `println` -- and which of the two streams it
// goes to, the difference between `print` and `eprint`.
//
// One word and not two parameters, which is what this was and could not stay.
// A call here carries the word, the format string and up to four arguments, and
// this machine hands the first six over in registers and has nothing that puts
// a seventh anywhere: two flags made the four-argument rung a call of seven,
// and a call of seven is one `mir::asm` declines to write. It said so, and what
// it left behind was a `print4` that printed nothing.
const NEWLINE: i64 = 1;
const TO_ERROR: i64 = 2;

// Everything the five entry points do, once.
//
// The line goes out in one write. Two would let another thread's line land
// between the text and its newline, and the lock a single `print!` takes is not
// held across two of them.
fn emit(how: i64, fmt: *const Str, args: &[Object]) {
    let Some(fmt) = (unsafe { fmt.as_ref() }).and_then(Str::read) else {
        eprintln!("fortec: print: the format string is not text");
        return;
    };
    let (mut text, wrong) = render(fmt, args);
    let nl = how & NEWLINE != 0;
    if nl {
        text.push('\n');
    }

    if how & TO_ERROR != 0 {
        // The error stream is not buffered, here as in Rust, so half a line on
        // it is already where the reader can see it.
        let stderr = std::io::stderr();
        let mut held = stderr.lock();
        let _ = held.write_all(text.as_bytes());
    } else {
        let stdout = std::io::stdout();
        let mut held = stdout.lock();
        let _ = held.write_all(text.as_bytes());
        // Where a line has no newline on it the reader is being shown a prompt
        // or half a line, and either way they are meant to see it now.
        if !nl {
            let _ = held.flush();
        }
    }

    for why in wrong {
        eprintln!("fortec: print: {}", why);
    }
}

// One entry, and the arity is a length rather than a name.
//
// It used to be five, `__rt_print0` through `__rt_print4`, because a Forte
// macro cannot take "a format string and whatever follows it" and a fn has no
// variadic form -- so the number was in the symbol. It is in the view now:
// `std/fmt.ft` hands over the `&(&dyn Show)[]` it was given, and this asks
// each of them what it looks like.
///
/// # Safety
/// `fmt` is one `Str` and `args` one `Objects`, both the caller's, and the
/// objects it names live for the length of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_print(how: i64, fmt: *const Str, args: *const Objects) {
    let held: &[Object] = match unsafe { args.as_ref() } {
        // Nothing to say about the arguments is not nothing to print: a
        // format string with no `{}` in it is the commonest call there is.
        // And a negative length is a caller that has lost track of what it
        // holds, for which reading nothing is the only safe answer.
        None => &[],
        Some(held) if held.at.is_null() || held.len <= 0 => &[],
        Some(held) => unsafe { std::slice::from_raw_parts(held.at, held.len as usize) },
    };
    emit(how, fmt, held);
}

// ---- What a value writes itself with ---------------------------------------

// The five, and the whole of what a `Show` body may do to a sink.
//
// There is no `__rt_show_str` taking bytes and a length as two words: a `str`
// is one aggregate and crosses as the address of a copy, exactly as the format
// string does.
//
// Each of them takes the sink by address and writes one piece. What that piece
// looks like is the spec's business and the spec is the sink's, so a body in
// the language says *what* it is writing and never how.

/// # Safety
/// `into` is a sink this runtime made and handed to the caller, live for the
/// length of the call that handed it over.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_show_int(into: *mut Sink, n: i64) {
    if let Some(sink) = unsafe { into.as_mut() } {
        sink.wrote(Value::Int(n));
    }
}

/// # Safety
/// As `__rt_show_int`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_show_uint(into: *mut Sink, n: u64) {
    if let Some(sink) = unsafe { into.as_mut() } {
        sink.wrote(Value::Uint(n));
    }
}

/// # Safety
/// As `__rt_show_int`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_show_real(into: *mut Sink, x: f64) {
    if let Some(sink) = unsafe { into.as_mut() } {
        sink.wrote(Value::Real(x));
    }
}

/// # Safety
/// As `__rt_show_int`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_show_truth(into: *mut Sink, v: i64) {
    if let Some(sink) = unsafe { into.as_mut() } {
        sink.wrote(Value::Truth(v != 0));
    }
}

/// # Safety
/// As `__rt_show_int`, and `text` is one `Str` of the caller's.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt_show_text(into: *mut Sink, text: *const Str) {
    let Some(sink) = (unsafe { into.as_mut() }) else { return };
    match (unsafe { text.as_ref() }).and_then(Str::read) {
        Some(held) => sink.wrote(Value::Text(held)),
        None => {
            if sink.wrong.is_none() {
                sink.wrong = Some("this is not text".to_string());
            }
        }
    }
}

// ---- A `&dyn Show` made without a program to make one ----------------------

// The tests in this crate ask what the formatter does, and what it does now
// begins with a call into a compiled Forte body. There is none here, so this is
// one: a table of one entry, and a value behind the data pointer that the entry
// knows how to write.
//
// It is the shape and not a simulation of it -- the same two words in the same
// order, the same C signature, the same receiver-first call -- so a test that
// passes here is a test about the path a program takes.
#[cfg(test)]
pub(crate) mod fake {
    use super::{Object, Shows, Sink, Value};

    // What one of these stands for. `Pieces` is the shape a derived `Show` has
    // and a primitive does not: a value written in more than one go.
    pub(crate) enum Held {
        Int(i64),
        Uint(u64),
        Real(f64),
        Truth(bool),
        Text(String),
        Pieces(Vec<String>),
        // Bytes that are not text, handed over the way a Forte `str` is: the
        // language has no operation that would have looked at them before now,
        // so `__rt_show_text` is where it is found out.
        Raw(Vec<u8>),
    }

    unsafe extern "C" fn shows(data: *const u8, into: *mut Sink) {
        let held = unsafe { &*(data as *const Held) };
        let sink = unsafe { &mut *into };
        match held {
            Held::Int(n) => sink.wrote(Value::Int(*n)),
            Held::Uint(n) => sink.wrote(Value::Uint(*n)),
            Held::Real(x) => sink.wrote(Value::Real(*x)),
            Held::Truth(v) => sink.wrote(Value::Truth(*v)),
            Held::Text(s) => sink.wrote(Value::Text(s)),
            Held::Pieces(held) => {
                for piece in held {
                    sink.wrote(Value::Text(piece));
                }
            }
            // Through the entry itself and not through `wrote`, that being the
            // whole of what this case is about.
            Held::Raw(bytes) => {
                let held = super::Str { at: bytes.as_ptr(), len: bytes.len() as i64 };
                unsafe { super::__rt_show_text(into, &held) };
            }
        }
    }

    static TABLE: Shows = shows;

    // Leaked, so that an `Object` may be written inline in a list of them the
    // way an `Arg` used to be. A test process is the one place where never
    // giving a few words back is the right trade for a readable assertion.
    pub(crate) fn made(held: Held) -> Object {
        let held: &'static Held = Box::leak(Box::new(held));
        Object { data: (held as *const Held).cast(), table: &TABLE }
    }

    // Not one at all: what a caller compiled against a different version of
    // this file would hand over, and what the tag that was not one of five
    // used to be.
    pub(crate) fn nothing() -> Object {
        Object { data: std::ptr::null(), table: std::ptr::null() }
    }
}

#[cfg(test)]
mod tests;
