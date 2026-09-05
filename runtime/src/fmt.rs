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

// One thing to print, with a tag saying which of the fields means anything.
//
// Four fields and not a union: a union would be a byte or two smaller and
// would have to agree with the compiler about how it laid one out, and this is
// a value that lives for the length of one call.
#[repr(C)]
pub struct Arg {
    pub(crate) tag:  i64,
    pub(crate) word: i64,
    pub(crate) real: f64,
    pub(crate) held: Str,
}

// The tags, which `std/fmt.ft` writes and this reads. They are spelled out in
// both files and nowhere else.
const INT: i64 = 1;
const UINT: i64 = 2;
const REAL: i64 = 3;
const TRUTH: i64 = 4;
const TEXT: i64 = 5;

// What an `Arg` turned out to be.
enum Value<'a> {
    Int(i64),
    Uint(u64),
    Real(f64),
    Truth(bool),
    Text(&'a str),
}

impl Arg {
    // What it says it is. `None` where the tag is not one of the five, which is
    // a caller that was compiled against a different version of this file.
    //
    // The text is checked rather than assumed: a `str` in Forte is bytes with a
    // length and nothing has ever looked at them, so one that is not UTF-8
    // reaches here and must not become a `&str` by assertion.
    fn value(&self) -> Option<Value<'_>> {
        Some(match self.tag {
            INT => Value::Int(self.word),
            UINT => Value::Uint(self.word as u64),
            REAL => Value::Real(self.real),
            TRUTH => Value::Truth(self.word != 0),
            TEXT => Value::Text(self.held.read()?),
            _ => return None,
        })
    }
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
fn spec_of(text: &str, args: &[&Arg]) -> Result<Spec, String> {
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
fn count(held: &[char], at: &mut usize, args: &[&Arg]) -> Result<Option<usize>, String> {
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
    let Some(arg) = args.get(n) else {
        return Err(format!("`{}$` names argument {}, and there is no such argument", n, n));
    };
    match arg.value() {
        Some(Value::Int(v)) if v >= 0 => Ok(Some(v as usize)),
        Some(Value::Uint(v)) => Ok(Some(v as usize)),
        _ => Err(format!("`{}$` names argument {}, which is not a whole number", n, n)),
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
pub(crate) fn shown(arg: &Arg) -> String {
    match arg.value() {
        Some(v) => match body(&v, &Spec::default()) {
            Ok(text) => text,
            Err(why) => format!("<{}>", why),
        },
        None => "<not a kind of thing this can print>".to_string(),
    }
}

// Whether two arguments are the same value.
//
// Two of different kinds never are, `int(1)` and `uint(1)` having been written
// by somebody who meant two different things. Floats compare as floats, so two
// NaNs are not equal and an assertion that they are fails -- which is Rust's
// answer, and the one the reader gets everywhere else.
pub(crate) fn same(a: &Arg, b: &Arg) -> bool {
    match (a.value(), b.value()) {
        (Some(Value::Int(x)), Some(Value::Int(y))) => x == y,
        (Some(Value::Uint(x)), Some(Value::Uint(y))) => x == y,
        (Some(Value::Real(x)), Some(Value::Real(y))) => x == y,
        (Some(Value::Truth(x)), Some(Value::Truth(y))) => x == y,
        (Some(Value::Text(x)), Some(Value::Text(y))) => x == y,
        _ => false,
    }
}

// ---- The format string -----------------------------------------------------

// What the whole of it comes to, and everything that was wrong with it.
//
// The two are answered together rather than one or the other, because a
// mistake in one placeholder says nothing about the rest of the line: a format
// string with a bad `{:q}` in the middle still has a beginning and an end that
// the reader wrote and wants to see.
fn render(fmt: &str, args: &[&Arg]) -> (String, Vec<String>) {
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
fn one(inner: &str, args: &[&Arg], next: &mut usize) -> Result<String, String> {
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
    let Some(value) = arg.value() else {
        return Err(format!("argument {} is not a kind of thing this can print", at));
    };
    let numeric = matches!(value, Value::Int(_) | Value::Uint(_) | Value::Real(_));
    Ok(pad(body(&value, &spec)?, &spec, numeric))
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
fn emit(how: i64, fmt: *const Str, args: &[&Arg]) {
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

// The arguments arrive as pointers to copies the caller made, one per
// parameter, because that is how this compiler hands an aggregate over. A null
// among them is a caller that disagrees with this file about how many it has,
// and is dropped rather than followed.
fn gather<'a>(held: &[*const Arg]) -> Vec<&'a Arg> {
    held.iter().filter_map(|p| unsafe { p.as_ref() }).collect()
}

// Five arities, because there is no sixth thing to write. A Forte macro cannot
// take "a format string and whatever follows it" (see the head of this file),
// so the arity is in the name on the Forte side and in the symbol here.
#[unsafe(no_mangle)]
pub extern "C" fn __rt_print0(how: i64, fmt: *const Str) {
    emit(how, fmt, &[]);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_print1(how: i64, fmt: *const Str, a: *const Arg) {
    emit(how, fmt, &gather(&[a]));
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_print2(
    how: i64,
    fmt: *const Str,
    a: *const Arg,
    b: *const Arg,
) {
    emit(how, fmt, &gather(&[a, b]));
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_print3(
    how: i64,
    fmt: *const Str,
    a: *const Arg,
    b: *const Arg,
    c: *const Arg,
) {
    emit(how, fmt, &gather(&[a, b, c]));
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt_print4(
    how: i64,
    fmt: *const Str,
    a: *const Arg,
    b: *const Arg,
    c: *const Arg,
    d: *const Arg,
) {
    emit(how, fmt, &gather(&[a, b, c, d]));
}

#[cfg(test)]
mod tests;
