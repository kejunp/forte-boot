// That a key means the same thing every time it is asked about.
//
// Two rules tie the three operations together and nothing else here matters
// as much: two keys that compare equal must hash the same, or a hash map
// cannot find what it put in; and ordering must be a real order, or a binary
// search over a sorted run walks off in the wrong direction. Both are checked
// over each kind, because each kind reads the bytes differently.

use super::super::super::shape::{Kind, Made};
use super::*;

fn shape(bytes: usize, kind: Kind) -> Made {
    Made::new(bytes, bytes.min(8), kind)
}

// ---- Reading a number ------------------------------------------------------

// The register holding a one-byte key has seven bytes above it that nothing
// wrote, and a `-1` is `0xff` rather than `0xffffffffffffffff`.
#[test]
fn a_narrow_signed_key_is_read_as_its_own_width() {
    let held = shape(1, Kind::Signed);
    let s = held.shape();
    assert_eq!(order(0xff, 0, s), std::cmp::Ordering::Less, "a byte -1 is below nought");
    assert_eq!(order(1, 0xff, s), std::cmp::Ordering::Greater);
}

#[test]
fn a_narrow_unsigned_key_is_read_as_its_own_width() {
    let held = shape(1, Kind::Unsigned);
    let s = held.shape();
    assert_eq!(order(0xff, 0, s), std::cmp::Ordering::Greater, "a byte 255 is above nought");
}

// The bytes above a narrow key are not the key, so two registers that differ
// only up there are the same key.
#[test]
fn what_is_above_a_narrow_key_is_not_part_of_it() {
    let held = shape(4, Kind::Unsigned);
    let s = held.shape();
    assert!(same(7, 7 | (1 << 40), s));
    assert_eq!(hash(7, s), hash(7 | (1 << 40), s));
}

#[test]
fn a_signed_key_orders_the_way_a_number_does() {
    let held = shape(8, Kind::Signed);
    let s = held.shape();
    let mut got = vec![5usize, (-3i64) as usize, 0, (-100i64) as usize, 42];
    got.sort_by(|a, b| order(*a, *b, s));
    let want: Vec<i64> = got.iter().map(|held| *held as i64).collect();
    assert_eq!(want, vec![-100, -3, 0, 5, 42]);
}

#[test]
fn a_float_key_orders_the_way_a_number_does() {
    let held = shape(8, Kind::Float);
    let s = held.shape();
    let mut got: Vec<usize> = [3.5f64, -1.0, 0.0, 100.25]
        .iter()
        .map(|held| held.to_bits() as usize)
        .collect();
    got.sort_by(|a, b| order(*a, *b, s));
    let want: Vec<f64> = got.iter().map(|held| f64::from_bits(*held as u64)).collect();
    assert_eq!(want, vec![-1.0, 0.0, 3.5, 100.25]);
}

// A map has to be able to hold a NaN somewhere, and the somewhere has to be
// the same place every time or a lookup could not find it.
#[test]
fn a_float_that_is_not_ordered_still_has_a_place() {
    let held = shape(8, Kind::Float);
    let s = held.shape();
    let nan = f64::NAN.to_bits() as usize;
    let one = 1.0f64.to_bits() as usize;
    assert_eq!(order(nan, nan, s), std::cmp::Ordering::Equal);
    assert_ne!(order(nan, one, s), std::cmp::Ordering::Equal);
    assert_eq!(order(nan, one, s), order(nan, one, s), "and the same place twice");
}

// Nought and minus nought are one key, or `{0.0: 1}` looked up with `-0.0`
// would miss.
#[test]
fn both_spellings_of_nought_are_one_float_key() {
    let held = shape(8, Kind::Float);
    let s = held.shape();
    let (a, b) = (0.0f64.to_bits() as usize, (-0.0f64).to_bits() as usize);
    assert!(same(a, b, s));
    assert_eq!(hash(a, s), hash(b, s));
}

// ---- Reading bytes ---------------------------------------------------------

#[test]
fn an_indirect_key_is_read_through_its_address() {
    let held = Made::new(16, 8, Kind::Opaque).indirect();
    let s = held.shape();
    let a: [u8; 16] = [1; 16];
    let b: [u8; 16] = [1; 16];
    let c: [u8; 16] = [2; 16];
    assert!(same(a.as_ptr() as usize, b.as_ptr() as usize, s), "the same bytes");
    assert!(!same(a.as_ptr() as usize, c.as_ptr() as usize, s));
    assert_eq!(hash(a.as_ptr() as usize, s), hash(b.as_ptr() as usize, s));
}

#[test]
fn a_string_is_read_through_its_pointer_and_length() {
    let held = Made::new(16, 8, Kind::Str).indirect();
    let s = held.shape();
    let text = b"hello";
    let other = b"hello world";
    let one: [usize; 2] = [text.as_ptr() as usize, 5];
    let two: [usize; 2] = [other.as_ptr() as usize, 5];
    let three: [usize; 2] = [other.as_ptr() as usize, 11];
    assert!(same(one.as_ptr() as usize, two.as_ptr() as usize, s), "five bytes each");
    assert!(!same(one.as_ptr() as usize, three.as_ptr() as usize, s));
    assert_eq!(hash(one.as_ptr() as usize, s), hash(two.as_ptr() as usize, s));
}

#[test]
fn strings_order_by_their_characters() {
    let held = Made::new(16, 8, Kind::Str).indirect();
    let s = held.shape();
    let (a, b) = (b"apple", b"banana");
    let one: [usize; 2] = [a.as_ptr() as usize, 5];
    let two: [usize; 2] = [b.as_ptr() as usize, 6];
    assert_eq!(
        order(one.as_ptr() as usize, two.as_ptr() as usize, s),
        std::cmp::Ordering::Less
    );
}

// ---- The two rules ---------------------------------------------------------

#[test]
fn two_keys_that_are_equal_hash_the_same() {
    for (bytes, kind) in
        [(1, Kind::Signed), (4, Kind::Unsigned), (8, Kind::Signed), (8, Kind::Pointer)]
    {
        let held = shape(bytes, kind);
        let s = held.shape();
        for value in [0usize, 1, 7, 255, 4096] {
            assert!(same(value, value, s));
            assert_eq!(hash(value, s), hash(value, s), "{:?} {}", kind, value);
        }
    }
}

#[test]
fn ordering_is_an_order() {
    let held = shape(8, Kind::Signed);
    let s = held.shape();
    let some = [0usize, 1, 7, (-1i64) as usize, (-9i64) as usize, 1 << 40];
    for a in some {
        assert_eq!(order(a, a, s), std::cmp::Ordering::Equal);
        for b in some {
            assert_eq!(order(a, b, s), order(b, a, s).reverse(), "{} and {}", a, b);
            for c in some {
                if order(a, b, s).is_lt() && order(b, c, s).is_lt() {
                    assert!(order(a, c, s).is_lt(), "{} {} {}", a, b, c);
                }
            }
        }
    }
}

// Different keys mostly hash differently, or every entry would be in one
// bucket and a hash map would be a list.
#[test]
fn different_keys_mostly_hash_differently() {
    let held = shape(8, Kind::Unsigned);
    let s = held.shape();
    let mut seen: Vec<u64> = (0..1000usize).map(|n| hash(n, s)).collect();
    seen.sort_unstable();
    let all = seen.len();
    seen.dedup();
    assert!(seen.len() * 100 > all * 99, "a thousand keys gave {} hashes", seen.len());
}

// ---- Keeping one -----------------------------------------------------------

#[test]
fn a_direct_key_is_kept_as_itself() {
    let mut rt = super::super::super::Runtime::new();
    let held = shape(4, Kind::Signed);
    assert_eq!(take(&mut rt, 42, held.shape()), 42);
}

// The word the caller passed for an indirect key is the address of a slot in
// its frame, which is gone when the call returns.
#[test]
fn an_indirect_key_is_copied_somewhere_that_outlives_the_call() {
    let mut rt = super::super::super::Runtime::new();
    let held = Made::new(16, 8, Kind::Opaque).indirect();
    let one: [u8; 16] = [5; 16];
    let kept = take(&mut rt, one.as_ptr() as usize, held.shape());
    assert_ne!(kept, one.as_ptr() as usize, "it is the caller's, not ours");
    assert!(rt.heap.holding(kept).is_some(), "and it is in our heap");
    assert!(same(kept, one.as_ptr() as usize, held.shape()), "and it is the same key");
}

// ---- What the collector has to see -----------------------------------------

#[test]
fn a_copied_key_is_a_root_and_a_number_is_not() {
    let mut out = Vec::new();
    let held = Made::new(16, 8, Kind::Opaque).indirect();
    roots(0x4000, held.shape(), &mut out);
    assert_eq!(out, vec![0x4000]);

    out.clear();
    let number = shape(8, Kind::Signed);
    roots(0x4000, number.shape(), &mut out);
    assert!(out.is_empty(), "a number is not an address");
}

// A string's characters are somewhere else again, and the collector has to be
// told about both the pair and what it points at.
#[test]
fn a_strings_characters_are_a_root_as_well_as_its_pair() {
    let held = Made::new(16, 8, Kind::Str).indirect();
    let text = b"hi";
    let pair: [usize; 2] = [text.as_ptr() as usize, 2];
    let mut out = Vec::new();
    roots(pair.as_ptr() as usize, held.shape(), &mut out);
    assert_eq!(out, vec![pair.as_ptr() as usize, text.as_ptr() as usize]);
}
