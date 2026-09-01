// Where the registers a body wanted actually go.
//
// This is the first point in the compiler where there is not enough of
// something. Every pass before it could make one more of whatever it needed --
// a value, a block, a register -- and none of them had to ask. A machine has
// fourteen integer registers, and a body that wants twenty is not a body that
// can have twenty.
//
// **Linear scan**, and not graph colouring. By here the body *is* a list, which
// is the input linear scan takes; it is a sort and a walk rather than a build,
// a simplify and a select; and what it gives up is the cases where two values
// that are live at the same time could still share a register because their
// live *ranges* are not really one interval. That is a real loss and it is the
// right one to take first: the answer here can be wrong in a way that is
// written down -- an interval is one span, and a value live in two places is
// treated as live between them -- rather than wrong in a way that is not.
//
// An interval is the first place a register is written or read and the last,
// and everything between. For a straight run that is exactly its life. Round a
// loop it is not: a value written at the bottom of a loop and read at the top
// is read *earlier* in the list than it is written, so its interval is the
// whole loop rather than a wrap. Taking the lowest and the highest of both
// gives that, which is why nothing here treats a definition as a beginning.
//
// A call is what makes the rest of it. The registers a call may write are the
// caller-saved ones, so a value that is live *across* a call cannot be in one
// of those -- it would be gone when the call came back. Such a value is given a
// callee-saved register, or, if there is none to give, the frame.
//
// What this does not do is write the prologue and the epilogue. Nothing here
// moves an argument out of the register it arrived in, and nothing saves a
// callee-saved register before using it. Both are real and neither changes
// where anything goes -- they are instructions around the body rather than
// decisions about it -- so they belong with whatever turns a listing into an
// object file. That is `mir::asm`, and it writes both out of what this
// decided: the callee-saved registers it has to put back are the ones this
// handed out, and where an argument goes is where this said the parameter
// lives.
//
// What this also does not do is model a register an *instruction* insists on.
// x86-64 has two -- a division writes `rdx:rax` and a shift counts in `cl` --
// and neither is a register this knows to keep clear, so `mir::asm::x86_64`
// pushes whatever is in the way and puts it back. That is three or four
// instructions on every division and every shift, and taking them away is a
// change here rather than there: an allocator would have to be able to say
// "not this register, across this instruction", which is a thing linear scan
// can be taught and this one has not been.

use std::collections::HashMap;

use super::linear::{Line, Linear};
use super::machine::{Class, Machine, Reg};
use super::mir_nodes::*;

// Where one register ended up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Where {
    In(Reg),
    // In the frame, because there was no register to be had when it was wanted.
    Spilled(MIRFrameId),
    // Nothing ever writes it and nothing ever reads it, so it needs nowhere.
    // A register the lowering made for a value the SIR named and nothing used.
    Nowhere,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Allocation {
    // One answer per register of the body, by its id.
    pub at:      Vec<Where>,
    // How many had to go in the frame.
    pub spills:  usize,
    // How many were wanted at once at the worst point, which is what says
    // whether a machine with more registers would have helped.
    pub most:    usize,
}

impl Allocation {
    pub fn of(&self, reg: MIRRegId) -> Where {
        self.at.get(reg).copied().unwrap_or(Where::Nowhere)
    }
}

// What a register is alive for: the first line that mentions it and the last.
#[derive(Debug, Clone, Copy)]
struct Span {
    reg:    MIRRegId,
    from:   usize,
    to:     usize,
    class:  Class,
    bytes:  usize,
    // Whether a call stands inside it, which is what stops it going in a
    // register the call may write.
    across: bool,
}

// Allocates `held`, appending a slot to its frame for everything spilled.
pub fn allocate(held: &mut Linear, m: Machine) -> Allocation {
    let mut spans = {
        let calls = calls_at(held);
        spans(held, &calls)
    };
    spans.sort_by_key(|span| span.from);

    let mut at: Vec<Where> = vec![Where::Nowhere; held.regs.len()];
    let mut ints: Vec<Reg> = m.ints.to_vec();
    let mut floats: Vec<Reg> = m.floats.to_vec();
    // The spans holding a register now, kept in the order they end so that
    // expiring them is a walk from the front.
    let mut active: Vec<Span> = Vec::new();
    let mut given: HashMap<MIRRegId, Reg> = HashMap::new();
    let (mut spills, mut most) = (0usize, 0usize);

    for span in spans {
        // Everything that has ended gives its register back.
        while let Some(first) = active.first().copied() {
            if first.to >= span.from {
                break;
            }
            active.remove(0);
            if let Some(reg) = given.remove(&first.reg) {
                free_of(&mut ints, &mut floats, reg.class).push(reg);
            }
        }
        most = most.max(active.len() + 1);

        // A value live across a call has to be somewhere a call keeps -- a
        // caller-saved register would be gone when the call came back.
        let want = free_of(&mut ints, &mut floats, span.class)
            .iter()
            .position(|reg| !span.across || m.keeps(*reg));

        if let Some(which) = want {
            let reg = free_of(&mut ints, &mut floats, span.class).remove(which);
            given.insert(span.reg, reg);
            at[span.reg] = Where::In(reg);
            keep(&mut active, span);
            continue;
        }

        // Nothing to be had. The one that ends furthest away is the one worth
        // putting in the frame: it is holding a register for the longest, and
        // so is the one whose register buys the most by being taken.
        let furthest = active
            .iter()
            .enumerate()
            .filter(|(_, held)| held.class == span.class)
            .filter(|(_, held)| {
                given.get(&held.reg).is_some_and(|reg| !span.across || m.keeps(*reg))
            })
            .max_by_key(|(_, held)| held.to)
            .map(|(which, held)| (which, *held));

        match furthest {
            Some((which, worst)) if worst.to > span.to => {
                active.remove(which);
                let reg = given.remove(&worst.reg).expect("an active span holds one");
                let slot = spill(&worst, &mut held.frame, m);
                at[worst.reg] = Where::Spilled(slot);
                spills += 1;

                given.insert(span.reg, reg);
                at[span.reg] = Where::In(reg);
                keep(&mut active, span);
            }
            // Nothing active ends later than this one does, so taking a
            // register from any of them would buy less than it cost.
            _ => {
                let slot = spill(&span, &mut held.frame, m);
                at[span.reg] = Where::Spilled(slot);
                spills += 1;
            }
        }
    }

    Allocation { at, spills, most }
}

// Into the active list, which is kept in the order the spans end.
fn keep(active: &mut Vec<Span>, span: Span) {
    let at = active.partition_point(|held| held.to <= span.to);
    active.insert(at, span);
}

fn free_of<'a>(
    ints: &'a mut Vec<Reg>,
    floats: &'a mut Vec<Reg>,
    class: Class,
) -> &'a mut Vec<Reg> {
    match class {
        Class::Int => ints,
        Class::Float => floats,
    }
}

// Where every call stands, so that a span can be asked whether one is inside
// it.
fn calls_at(held: &Linear) -> Vec<usize> {
    held.lines
        .iter()
        .enumerate()
        .filter(|(_, line)| {
            matches!(line, Line::Inst(MIRInst { kind: MIRInstKind::Call { .. }, .. }))
        })
        .map(|(at, _)| at)
        .collect()
}

// The lowest and the highest line that mentions each register.
//
// Not "from the definition to the last use": round a loop the definition is
// *later* in the list than a use of it, and reading the definition as the
// beginning would give a span that ends before it starts. The lowest and the
// highest of everything covers both, and over a loop that is the whole loop --
// which is what being live round one means.
fn spans(held: &Linear, calls: &[usize]) -> Vec<Span> {
    let mut low: Vec<Option<usize>> = vec![None; held.regs.len()];
    let mut high: Vec<Option<usize>> = vec![None; held.regs.len()];
    let mark = |reg: MIRRegId, at: usize, low: &mut Vec<Option<usize>>,
                    high: &mut Vec<Option<usize>>| {
        if reg >= low.len() {
            return;
        }
        low[reg] = Some(low[reg].map_or(at, |held| held.min(at)));
        high[reg] = Some(high[reg].map_or(at, |held| held.max(at)));
    };

    // A parameter is filled by the caller, so it is alive from the first line.
    for &reg in &held.params {
        mark(reg, 0, &mut low, &mut high);
    }

    for (at, line) in held.lines.iter().enumerate() {
        match line {
            Line::Label(_) => {}
            Line::Inst(inst) => {
                for reg in uses(&inst.kind) {
                    mark(reg, at, &mut low, &mut high);
                }
                if let Some(def) = inst.def {
                    mark(def, at, &mut low, &mut high);
                }
            }
            Line::Term(term) => {
                for reg in term.uses() {
                    mark(reg, at, &mut low, &mut high);
                }
            }
        }
    }

    (0..held.regs.len())
        .filter_map(|reg| {
            let (from, to) = (low[reg]?, high[reg]?);
            let one = held.regs[reg];
            Some(Span {
                reg,
                from,
                to,
                class: one.class,
                bytes: one.bytes,
                across: calls.iter().any(|&at| at > from && at <= to),
            })
        })
        .collect()
}

// Room in the frame for one that could not have a register.
fn spill(span: &Span, frame: &mut Vec<MIRSlot>, m: Machine) -> MIRFrameId {
    let bytes = span.bytes.max(1);
    frame.push(MIRSlot {
        bytes,
        align: bytes.min(m.word).max(1),
        name: format!("%{}", span.reg),
        spill: true,
    });
    frame.len() - 1
}

#[cfg(test)]
mod tests;
