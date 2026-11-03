//! Bounded formal proofs via the Kani model checker.
//!
//! Compiled **only** under `cargo kani` (`#[cfg(kani)]` gates the whole module),
//! so the normal build and the runtime crate carry no `kani` dependency.
//!
//! The crown-jewel invariant for a safety-critical analysis tool is
//! **losslessness**: the parser must never lose, alter, or invent source bytes.
//! Kani proves this exhaustively for all inputs up to a bounded size — a
//! machine-checked guarantee suitable for review by a defense customer.
//!
//! Run with: `cargo kani -p trailtracker-eval`

use trailtracker::lang::rust::parser::parse;

/// For every byte string of length up to `N` drawn from a structural alphabet,
/// the CST reconstructs the source exactly and parsing does not panic.
#[kani::proof]
#[kani::unwind(8)]
fn losslessness_is_total() {
    const N: usize = 5;
    // A small but adversarial alphabet exercising delimiters, quotes, comments,
    // and identifier/whitespace bytes — the cases where losslessness is hard.
    const ALPHABET: &[u8] = b"(){}[]\"'/*# \n;:a0";

    let len: usize = kani::any();
    kani::assume(len <= N);

    let mut bytes = [b'a'; N];
    for b in bytes.iter_mut().take(len) {
        let idx: usize = kani::any();
        kani::assume(idx < ALPHABET.len());
        *b = ALPHABET[idx];
    }

    // The slice is ASCII by construction, hence valid UTF-8.
    let src = core::str::from_utf8(&bytes[..len]).unwrap();
    let tree = parse("kani.rs", src);

    let mut rebuilt = String::new();
    tree.root.reconstruct(src, &mut rebuilt);
    assert!(rebuilt == src, "CST must reconstruct source exactly");
}

// ---------------------------------------------------------------------------
// K3c schema obligations (ADR-0007): each rewrite rule's once-stated argument
// that ANY application matching its recognizer preserves behavior, encoded
// over a bounded semantic model. These prove the SCHEMA over the model; the
// model-to-Rust mapping is a recorded assumption (ADR-0007, assumption 6).
// Per-application structural verification lives in src/rewrite/cert.rs.
// ---------------------------------------------------------------------------

/// A tiny deterministic register machine: the model's "statement".
fn k3c_apply(state: i32, op: u8) -> i32 {
    match op % 4 {
        0 => state.wrapping_add(1),
        1 => state.wrapping_mul(2),
        2 => state.wrapping_sub(3),
        _ => state ^ 5,
    }
}

/// `dead-branch-elim` v1 schema (ADR-0007): for every bounded program
/// `[pre] if LIT { then } else { els } [post]` with a LITERAL condition,
/// splicing the live branch in place of the `if` yields the identical final
/// state — the dead branch never contributes, and the literal test itself is
/// effect-free by construction.
#[kani::proof]
#[kani::unwind(6)]
fn k3c_dead_branch_schema() {
    const N: usize = 3;
    let lit: bool = kani::any();
    let init: i32 = kani::any();
    let pre: [u8; N] = kani::any();
    let then_ops: [u8; N] = kani::any();
    let else_ops: [u8; N] = kani::any();
    let post: [u8; N] = kani::any();

    // Before: the branch statement is executed.
    let mut before = init;
    for op in pre {
        before = k3c_apply(before, op);
    }
    if lit {
        for op in then_ops {
            before = k3c_apply(before, op);
        }
    } else {
        for op in else_ops {
            before = k3c_apply(before, op);
        }
    }
    for op in post {
        before = k3c_apply(before, op);
    }

    // After: the licensed splice — the live branch's statements in place.
    let mut after = init;
    for op in pre {
        after = k3c_apply(after, op);
    }
    let live = if lit { then_ops } else { else_ops };
    for op in live {
        after = k3c_apply(after, op);
    }
    for op in post {
        after = k3c_apply(after, op);
    }

    assert!(
        before == after,
        "splicing the live branch must preserve the final state"
    );
}

/// `loop-to-iterator` v1 schema (ADR-0007): with a single reaching definition
/// of the accumulator, no early exit, and the accumulator unread in the body,
/// the loop is exactly a left fold — and `map` / `filter_map` + `collect` are
/// the `Vec::push` specializations (guarded and unguarded). The emitted
/// closures reuse the original expressions, so per-element order is shared by
/// construction; the model checks value equality over all bounded inputs.
#[kani::proof]
#[kani::unwind(6)]
fn k3c_loop_fold_schema() {
    const N: usize = 3;
    let xs: [i32; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    let init: i32 = kani::any();
    let sel: u8 = kani::any();
    let step = |acc: i32, x: i32| -> i32 {
        match sel % 3 {
            0 => acc.wrapping_add(x),
            1 => acc ^ x,
            _ => acc | x,
        }
    };

    // Fold form: `let mut ACC = INIT; for x in ITER { ACC op= EXPR }`.
    let mut acc = init;
    for &x in xs.iter().take(len) {
        acc = step(acc, x);
    }
    let folded = xs.iter().take(len).copied().fold(init, step);
    assert!(acc == folded, "the loop is exactly a left fold");

    // Map form: unguarded `push`.
    let mut pushed = Vec::new();
    for &x in xs.iter().take(len) {
        pushed.push(x.wrapping_mul(2));
    }
    let mapped: Vec<i32> = xs.iter().take(len).map(|&x| x.wrapping_mul(2)).collect();
    assert!(pushed == mapped, "push == map+collect");

    // Filter-map form: guarded `push` (`if COND { push }`, no else).
    let t: i32 = kani::any();
    let mut guarded = Vec::new();
    for &x in xs.iter().take(len) {
        if x > t {
            guarded.push(x.wrapping_mul(2));
        }
    }
    let filtered: Vec<i32> = xs
        .iter()
        .take(len)
        .filter_map(|&x| if x > t { Some(x.wrapping_mul(2)) } else { None })
        .collect();
    assert!(guarded == filtered, "guarded push == filter_map+collect");
}

/// `redundant-clone-elim` v1 schema (ADR-0007): a store of owned slots models
/// the bindings; `Some(v)` = a live owned value, `None` = moved out. Slot 0 is
/// the cloned binding `x`, slot 1 the move target `y`, the rest unrelated
/// state.
///
/// - BEFORE: `y = x.clone()` — the source slot keeps its value AND the target
///   receives an equal owned copy.
/// - AFTER: `y = move(x)` — the target receives the value, the source becomes
///   `None` (a moved-out binding; any read of it would be the bug).
///
/// The recognizer's licensed precondition, supplied here as an assumption, is
/// the CPG-proven last-use fact: **no operation after the clone point reads
/// slot 0**. Under that assumption every bounded program observes the
/// identical final state. Dropping the assumption breaks the proof (a read of
/// slot 0 sees `Some(v)` before and `None` after) — the harness is exactly the
/// one-sidedness argument: conservative may-reach DATA_DEP can only
/// over-report readers, so a "no reader after" conclusion licenses the move.
/// The Clone/Drop trait contract (clone's only effect is the copy; drop
/// releases what clone acquired) is a recorded assumption (ADR-0007), not part
/// of the model.
#[kani::proof]
#[kani::unwind(6)]
fn k3c_clone_elim_schema() {
    const SLOTS: usize = 3;
    const OPS: usize = 3;
    let x0: i32 = kani::any();
    let mut init: [Option<i32>; SLOTS] = [None; SLOTS];
    init[0] = Some(x0);
    for s in init.iter_mut().skip(2) {
        *s = Some(kani::any());
    }

    // BEFORE-world: y = x.clone(); the source stays live.
    let mut before = init;
    before[1] = before[0];

    // AFTER-world: y = x (move); the source is gone.
    let mut after = init;
    after[1] = after[0].take();

    // The rest of the program: bounded reads folding into one observable.
    // The last-use fact from the CPG becomes the model assumption: no read
    // of slot 0 after this point.
    let mut obs_before: i32 = 0;
    let mut obs_after: i32 = 0;
    for _ in 0..OPS {
        let slot: usize = kani::any();
        kani::assume(slot < SLOTS);
        kani::assume(slot != 0); // the PROVEN last-use: x is never read again
        obs_before = obs_before.wrapping_add(before[slot].unwrap_or(0));
        obs_after = obs_after.wrapping_add(after[slot].unwrap_or(0));
    }

    assert!(
        obs_before == obs_after,
        "with no read of the cloned binding after the clone point, move == clone"
    );
}

/// Schema obligation for `if-let-to-match` v1 (ADR-0007): `if let PAT =
/// PLACE { A } else { B }` and `match PLACE { PAT => { A } _ => { B } }`
/// compute identical results for EVERY value of the scrutinee.
///
/// The model: an arbitrary `Option<u8>` scrutinee (the two-way refutable
/// pattern shape — matched-with-binding vs. not-matched — is exactly what
/// the desugar must preserve), with both branch bodies folding the binding
/// (or the else path) into one observable. The recognizer's licensed
/// precondition — the scrutinee is a place expression, so no temporaries
/// exist whose drop order could differ between the two forms (the Rust 2024
/// `if let` temporary-scope change) — is structural: places produce no
/// value to drop, so the bounded model has nothing to model on that axis
/// and the equality below is the whole argument.
#[kani::proof]
fn k3c_if_let_match_schema() {
    let scrutinee: Option<u8> = kani::any();
    let arm_seed: u8 = kani::any();
    let else_seed: u8 = kani::any();

    // BEFORE-world: the if-let-else form.
    let before: i32 = if let Some(x) = scrutinee {
        i32::from(x) + i32::from(arm_seed)
    } else {
        -i32::from(else_seed)
    };

    // AFTER-world: the emitted match form (pattern arm, then `_`).
    let after: i32 = match scrutinee {
        Some(x) => i32::from(x) + i32::from(arm_seed),
        _ => -i32::from(else_seed),
    };

    assert!(
        before == after,
        "if-let-else and its match desugar agree for every scrutinee value"
    );
}
