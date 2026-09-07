// That a format string means here what it means in `println!`.
//
// Most of these assert against a `format!` written out beside them rather than
// against a string literal. That is the point of the file: the claim this
// module makes is not "this is what `{:>8.2}` produces", it is "this is what
// Rust produces for `{:>8.2}`", and an assertion that spells the answer out by
// hand would go on passing after Rust changed its mind.

use super::*;

// A `&dyn Show` without a Forte program to make one -- see `fmt::fake`, which
// is the table and the body behind these.
use super::fake::{made, nothing, Held};

fn int(n: i64) -> Object {
    made(Held::Int(n))
}

fn uint(n: u64) -> Object {
    made(Held::Uint(n))
}

fn real(x: f64) -> Object {
    made(Held::Real(x))
}

fn truth(b: bool) -> Object {
    made(Held::Truth(b))
}

fn text(s: &str) -> Object {
    made(Held::Text(s.to_string()))
}

// A value written in more than one go, which is what a derived `Show` is and
// what no primitive is.
fn pieces(held: &[&str]) -> Object {
    made(Held::Pieces(held.iter().map(|s| s.to_string()).collect()))
}

// What `render` made of it, with nothing to say about it.
fn shown(fmt: &str, args: &[Object]) -> String {
    let (out, wrong) = render(fmt, args);
    assert!(wrong.is_empty(), "`{}` was meant to be sound: {:?}", fmt, wrong);
    out
}

// What it said about one it could not take.
fn refused(fmt: &str, args: &[Object]) -> String {
    let (_, wrong) = render(fmt, args);
    assert!(!wrong.is_empty(), "`{}` was meant to be turned down", fmt);
    wrong.join("; ")
}

// ---- The plain ones ---------------------------------------------------------

#[test]
fn text_with_no_placeholder_is_itself() {
    assert_eq!(shown("hello", &[]), "hello");
    assert_eq!(shown("", &[]), "");
}

#[test]
fn an_empty_placeholder_takes_the_next_argument_nobody_named() {
    let (a, b) = (int(1), int(2));
    assert_eq!(shown("{} {}", &[a, b]), format!("{} {}", 1, 2));
}

#[test]
fn a_numbered_placeholder_takes_the_one_it_names_and_does_not_move_on() {
    let (a, b) = (int(1), int(2));
    assert_eq!(shown("{1} {0} {1}", &[a, b]), format!("{1} {0} {1}", 1, 2));
}

// A brace is written by writing it twice, and there is no other way to write
// one -- so a doubled brace is not a placeholder and does not take an argument.
#[test]
fn a_brace_is_spelled_twice() {
    let a = int(7);
    assert_eq!(shown("{{}} {}", &[a]), format!("{{}} {}", 7));
    assert_eq!(shown("{{{}}}", &[a]), format!("{{{}}}", 7));
}

// ---- Every kind of value ----------------------------------------------------

#[test]
fn a_whole_number_reads_as_rust_reads_it() {
    let n = int(-42);
    assert_eq!(shown("{}", &[n]), format!("{}", -42));
    assert_eq!(shown("{:?}", &[n]), format!("{:?}", -42));
    // The two's complement, which is what `{:x}` of a negative i64 is.
    assert_eq!(shown("{:x}", &[n]), format!("{:x}", -42i64));
    assert_eq!(shown("{:b}", &[int(5)]), format!("{:b}", 5));
    assert_eq!(shown("{:o}", &[int(64)]), format!("{:o}", 64));
    assert_eq!(shown("{:e}", &[int(1500)]), format!("{:e}", 1500));
}

#[test]
fn a_float_keeps_the_two_answers_display_and_debug_give() {
    let one = real(1.0);
    // `1` and `1.0`: the difference is Rust's and is not smoothed over here.
    assert_eq!(shown("{}", &[one]), format!("{}", 1.0f64));
    assert_eq!(shown("{:?}", &[one]), format!("{:?}", 1.0f64));
    assert_ne!(shown("{}", &[one]), shown("{:?}", &[one]));

    let pi = real(std::f64::consts::PI);
    assert_eq!(shown("{:.3}", &[pi]), format!("{:.3}", std::f64::consts::PI));
    assert_eq!(shown("{:.0}", &[pi]), format!("{:.0}", std::f64::consts::PI));
    assert_eq!(shown("{:e}", &[real(1500.0)]), format!("{:e}", 1500.0f64));
}

#[test]
fn a_bool_and_a_string_read_as_themselves() {
    assert_eq!(shown("{}", &[truth(true)]), format!("{}", true));
    assert_eq!(shown("{}", &[truth(false)]), format!("{}", false));

    let s = text("hi");
    assert_eq!(shown("{}", &[s]), format!("{}", "hi"));
    // Debug quotes and escapes it, which is the whole of what `{:?}` is for.
    assert_eq!(shown("{:?}", &[s]), format!("{:?}", "hi"));
    assert_eq!(shown("{:?}", &[text("a\"b\n")]), format!("{:?}", "a\"b\n"));
}

#[test]
fn an_unsigned_number_is_not_read_as_a_signed_one() {
    // The bit pattern of -1, which is what `u64::MAX` is handed over as.
    let n = uint(u64::MAX);
    assert_eq!(shown("{}", &[n]), format!("{}", u64::MAX));
    assert_ne!(shown("{}", &[n]), format!("{}", -1i64));
}

// ---- The room around a value ------------------------------------------------

#[test]
fn a_width_pads_a_number_on_the_left_and_a_string_on_the_right() {
    assert_eq!(shown("{:5}", &[int(42)]), format!("{:5}", 42));
    assert_eq!(shown("{:5}", &[text("ab")]), format!("{:5}", "ab"));
    // Which is to say the two differ, the default alignment being the value's.
    assert_ne!(shown("{:5}", &[int(42)]), shown("{:5}", &[text("42")]));
}

#[test]
fn an_alignment_and_a_fill_are_written_the_way_rust_writes_them() {
    let s = text("ab");
    assert_eq!(shown("{:<6}", &[s]), format!("{:<6}", "ab"));
    assert_eq!(shown("{:>6}", &[s]), format!("{:>6}", "ab"));
    assert_eq!(shown("{:^6}", &[s]), format!("{:^6}", "ab"));
    assert_eq!(shown("{:*^6}", &[s]), format!("{:*^6}", "ab"));
    assert_eq!(shown("{:-<6}", &[s]), format!("{:-<6}", "ab"));
    // An odd number of spaces leans left, which is where Rust puts the extra.
    assert_eq!(shown("{:^7}", &[s]), format!("{:^7}", "ab"));
}

// The zero flag pads inside the sign and inside the `0x`, which is the one rule
// here that a fill cannot express.
#[test]
fn zero_padding_goes_after_the_sign_and_after_the_prefix() {
    assert_eq!(shown("{:08}", &[int(-42)]), format!("{:08}", -42));
    assert_eq!(shown("{:08}", &[int(42)]), format!("{:08}", 42));
    assert_eq!(shown("{:+08}", &[int(42)]), format!("{:+08}", 42));
    assert_eq!(shown("{:#010x}", &[int(255)]), format!("{:#010x}", 255));
    assert_eq!(shown("{:#010b}", &[int(5)]), format!("{:#010b}", 5));
    // And it wins over an alignment written beside it rather than losing to
    // one, which is the rule that reads backwards.
    assert_eq!(shown("{:<08}", &[int(-42)]), format!("{:<08}", -42));
}

#[test]
fn a_sign_is_written_only_where_it_was_asked_for() {
    assert_eq!(shown("{:+}", &[int(42)]), format!("{:+}", 42));
    assert_eq!(shown("{:+}", &[int(-42)]), format!("{:+}", -42));
    assert_eq!(shown("{}", &[int(42)]), format!("{}", 42));
    assert_eq!(shown("{:+.2}", &[real(1.5)]), format!("{:+.2}", 1.5f64));
}

#[test]
fn an_alternate_writes_the_prefix_its_radix_has() {
    assert_eq!(shown("{:#x}", &[int(255)]), format!("{:#x}", 255));
    assert_eq!(shown("{:#X}", &[int(255)]), format!("{:#X}", 255));
    assert_eq!(shown("{:#b}", &[int(5)]), format!("{:#b}", 5));
    assert_eq!(shown("{:#o}", &[int(64)]), format!("{:#o}", 64));
}

// A precision truncates a string, and it counts characters rather than bytes --
// so it never cuts one in half.
#[test]
fn a_precision_truncates_a_string_by_characters() {
    assert_eq!(shown("{:.2}", &[text("hello")]), format!("{:.2}", "hello"));
    assert_eq!(shown("{:.10}", &[text("hi")]), format!("{:.10}", "hi"));
    let wide = text("héllo");
    assert_eq!(shown("{:.3}", &[wide]), format!("{:.3}", "héllo"));
}

#[test]
fn a_width_and_a_precision_are_both_applied_and_in_that_order() {
    let pi = real(std::f64::consts::PI);
    assert_eq!(shown("{:8.2}", &[pi]), format!("{:8.2}", std::f64::consts::PI));
    assert_eq!(shown("{:>8.2}", &[pi]), format!("{:>8.2}", std::f64::consts::PI));
    assert_eq!(shown("{:08.2}", &[pi]), format!("{:08.2}", std::f64::consts::PI));
}

// A width may be an argument rather than a number, which is the one place a
// placeholder reads two of them.
#[test]
fn a_dollar_width_names_the_argument_that_carries_it() {
    let (v, w) = (int(42), int(6));
    assert_eq!(shown("{:1$}", &[v, w]), format!("{:1$}", 42, 6));
    assert_eq!(shown("{:.1$}", &[real(1.23456), int(3)]), format!("{:.1$}", 1.23456f64, 3));
}

// ---- What it says about a bad one -------------------------------------------

// The rest of the line survives, which is the whole reason a mistake is
// reported rather than thrown: a format string with one bad placeholder in it
// still has a beginning and an end the reader wrote.
#[test]
fn a_placeholder_it_cannot_take_is_written_out_as_it_was_written() {
    let (a, b) = (int(1), int(2));
    let (out, wrong) = render("a {} b {:q} c", &[a, b]);
    assert_eq!(out, "a 1 b {:q} c");
    assert_eq!(wrong.len(), 1, "{:?}", wrong);
    assert!(wrong[0].contains("not a kind of formatting"), "{:?}", wrong);
}

#[test]
fn an_argument_that_is_not_there_says_how_many_there_are() {
    assert!(refused("{}", &[]).contains("nothing having been handed over"));

    let a = int(1);
    assert!(refused("{} {}", &[a]).contains("numbered 0"));

    let (a, b) = (int(1), int(2));
    assert!(refused("{5}", &[a, b]).contains("0 to 1"));
}

#[test]
fn a_name_is_turned_down_and_says_why() {
    let a = int(1);
    assert!(refused("{x}", &[a]).contains("a number and no name"));
}

#[test]
fn a_brace_that_closes_nothing_is_said_and_then_written() {
    let (out, wrong) = render("a } b", &[]);
    assert_eq!(out, "a } b");
    assert!(wrong[0].contains("closes nothing"), "{:?}", wrong);
}

#[test]
fn a_brace_that_was_never_closed_is_said_and_the_rest_kept() {
    let (out, wrong) = render("a {:>", &[]);
    assert_eq!(out, "a {:>");
    assert!(wrong[0].contains("never closed"), "{:?}", wrong);
}

// A kind of formatting the value has no impl for. Rust turns these down while
// it compiles; there is no pass here that could, so they are turned down now.
#[test]
fn a_value_that_has_no_such_impl_says_so() {
    assert!(refused("{:x}", &[real(1.0)]).contains("hexadecimal"));
    assert!(refused("{:x}", &[truth(true)]).contains("`{}` or `{:?}`"));
    assert!(refused("{:b}", &[text("hi")]).contains("`{}` or `{:?}`"));
}

// Not a `&dyn Show` at all: what a caller compiled against a different version
// of this file would hand over. It cannot happen while the two are built
// together, and it is the failure that would follow if they were not.
#[test]
fn an_argument_that_is_not_one_is_refused_and_not_read() {
    assert!(refused("{}", &[nothing()]).contains("not a value that can be written"));
}

// A `str` whose bytes are not text. Nothing has looked at them before now --
// the compiler copies a literal and the language has no operation that would --
// so `__rt_show_text` is where it is found out.
#[test]
fn a_string_that_is_not_text_is_refused_rather_than_asserted_into_one() {
    let held = made(Held::Raw(vec![0xff, 0xfe]));
    assert!(refused("{}", &[held]).contains("not text"));
}

// ---- A value written in more than one piece ---------------------------------

// Which is what a struct is and what no primitive is. The pieces come out in
// the order they were written, and the room around them is the room around the
// whole -- a width is what the value is padded to and not what each piece is.
#[test]
fn a_value_of_several_pieces_comes_out_as_one() {
    assert_eq!(shown("{}", &[pieces(&["Point { x: ", "3", ", y: ", "4", " }"])]),
               "Point { x: 3, y: 4 }");
    assert_eq!(shown("[{:>12}]", &[pieces(&["a", "b", "c"])]), format!("[{:>12}]", "abc"));
    // And one that writes nothing is nothing, padded like anything else.
    assert_eq!(shown("[{:>3}]", &[pieces(&[])]), format!("[{:>3}]", ""));
}

// A spec about the *value* -- a kind, a precision, a sign -- said of a value
// that is not one thing. The first piece took it and the rest did not, which is
// the only answer that is not a guess; saying so beats leaving the reader to
// notice that half a struct came out in hexadecimal.
#[test]
fn a_spec_about_the_value_is_refused_where_the_value_is_several() {
    assert!(refused("{:?}", &[pieces(&["a", "b"])]).contains("several pieces"));
    assert!(refused("{:.2}", &[pieces(&["a", "b"])]).contains("several pieces"));
    // The room around it is not about the value, so it is not refused.
    shown("{:>8}", &[pieces(&["a", "b"])]);
    // Nor is a value that wrote once, however particular the spec.
    assert_eq!(shown("{:#x}", &[int(255)]), "0xff");
}
