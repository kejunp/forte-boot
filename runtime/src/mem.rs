// Where the heap comes from: whole pages, straight from the kernel.
//
// Nothing here goes through the Rust allocator, and the reason is not purity.
// A collector has to know the exact bounds of every region it may find a
// pointer into -- that is what makes "is this word an address in the heap" a
// question with an answer -- and an allocator that hands out arbitrary
// addresses out of regions it does not name cannot say. So the heap is a small
// number of large, aligned reservations this file makes and remembers, and
// everything above it carves those up.
//
// Two calls, made directly. There is no libc here to make them through: the
// compiler has no notion of linking one yet, and a runtime that pulled one in
// to ask for pages would be a runtime whose first dependency was for its
// simplest need. `syscall` on x86-64 and `svc` on aarch64 is a dozen lines,
// and they are the same two machines `mir::machine` already names.
//
// This is the file that is not portable, and it is deliberately the only one.
// Everything above it takes pages and gives them back and never asks where
// they came from, so a second platform is this file again and nothing else.

use core::arch::asm;

// What this runtime calls a page, which is not what the kernel calls one. Go's
// is 8192 and so is this: a span is a run of these, and the smaller the unit
// the more of them a span table has to hold for the same heap.
pub const PAGE: usize = 8192;

// How much is reserved at once, and what that reservation is aligned to. Being
// aligned to its own size is what lets an address be turned into the
// reservation holding it by a shift, which is the operation the marker does
// once per candidate word and so the one worth making free.
pub const ARENA: usize = 4 << 20;

pub const ARENA_SHIFT: usize = 22;

// ---- The two calls ---------------------------------------------------------

const PROT_READ: usize = 0x1;
const PROT_WRITE: usize = 0x2;
const MAP_PRIVATE: usize = 0x02;
const MAP_ANONYMOUS: usize = 0x20;

#[cfg(target_arch = "x86_64")]
const SYS_MMAP: usize = 9;
#[cfg(target_arch = "x86_64")]
const SYS_MUNMAP: usize = 11;

#[cfg(target_arch = "aarch64")]
const SYS_MMAP: usize = 222;
#[cfg(target_arch = "aarch64")]
const SYS_MUNMAP: usize = 215;

// A failed syscall comes back as the negated error number, and every error
// number is small. Anything in the top page of the address space is one of
// those rather than an address, which is the check libc makes and the reason
// it is a range and not a comparison with -1.
fn failed(out: isize) -> bool {
    (-4095..0).contains(&out)
}

#[cfg(target_arch = "x86_64")]
unsafe fn call6(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize, f: usize) -> isize {
    let out: isize;
    unsafe {
        asm!(
            "syscall",
            inlateout("rax") nr as isize => out,
            in("rdi") a,
            in("rsi") b,
            in("rdx") c,
            in("r10") d,
            in("r8") e,
            in("r9") f,
            // What the instruction takes for itself.
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack)
        );
    }
    out
}

#[cfg(target_arch = "aarch64")]
unsafe fn call6(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize, f: usize) -> isize {
    let out: isize;
    unsafe {
        asm!(
            "svc 0",
            in("x8") nr,
            inlateout("x0") a => out,
            in("x1") b,
            in("x2") c,
            in("x3") d,
            in("x4") e,
            in("x5") f,
            options(nostack)
        );
    }
    out
}

// ---- Pages -----------------------------------------------------------------

// Room that reads and writes as noughts, rounded up to a whole page. `None`
// where the kernel would not give it, which is a thing that happens and not a
// thing to panic about: the caller above knows whether it can collect and try
// again.
pub fn map(bytes: usize) -> Option<*mut u8> {
    if bytes == 0 {
        return None;
    }
    let out = unsafe {
        call6(
            SYS_MMAP,
            0,
            up(bytes, PAGE),
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            usize::MAX,
            0,
        )
    };
    if failed(out) || out == 0 {
        return None;
    }
    Some(out as *mut u8)
}

// Room whose address is a multiple of `align`, which the kernel has no way to
// be asked for. So more than is wanted is taken and the ends given back --
// which costs one extra call at worst and nothing at all when the kernel
// happens to have answered on a boundary already.
pub fn map_aligned(bytes: usize, align: usize) -> Option<*mut u8> {
    let bytes = up(bytes, PAGE);
    let align = align.max(PAGE);
    let wide = map(bytes + align)?;
    let at = wide as usize;
    let want = up(at, align);

    if want > at {
        unmap(wide, want - at);
    }
    let over = (at + bytes + align) - (want + bytes);
    if over > 0 {
        unmap((want + bytes) as *mut u8, over);
    }
    Some(want as *mut u8)
}

pub fn unmap(at: *mut u8, bytes: usize) {
    if bytes == 0 {
        return;
    }
    unsafe {
        call6(SYS_MUNMAP, at as usize, up(bytes, PAGE), 0, 0, 0, 0);
    }
}

// ---- Rounding --------------------------------------------------------------

// Up to the next multiple, which is wanted often enough here and above that
// writing it twice would eventually be writing it two ways.
pub fn up(n: usize, to: usize) -> usize {
    if to == 0 {
        return n;
    }
    n.div_ceil(to) * to
}

// Whether a number is a power of two, which every alignment this runtime deals
// in is and which the shifts above quietly assume.
pub fn two(n: usize) -> bool {
    n != 0 && n & (n - 1) == 0
}

#[cfg(test)]
mod tests;
