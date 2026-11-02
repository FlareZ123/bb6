# Agent 11: exact blank-entry stopping gate for holdout C

**Status:** kernel-checked intermediate reduction. This does **not** prove nonhalting, halting, or a bound on BB(6), so it belongs in `im-results/`, not `results/`.

## Machine and formalized source

Target six-state two-symbol machine:
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

Upstream Google DeepMind's [Lean-certified reduction](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean) establishes that the blank tape enters counter state `B(5,0,1)` in 12 raw steps and proves `isHalt_iff_acceleration` for its `next` map. The local `CLine.lean` exactly copies the published nine cases into `nextC : Nat × Nat × Nat → Option (Nat × Nat × Nat)`, with constructors replaced by triples. The source maps were compared line by line; the upstream module itself is **not imported** into this standalone proof, so a kernel-checked cross-module equality bridge is still desirable.

Earlier work: `im-results/agent8-rank-barriers/CriticalReach.lean` independently proves that this blank-entry acceleration stops iff it reaches `(0,2j,5)` for some `j`. It also proves the weighted-rank monotonicity used here. The present proof further reduces the exact reachable guard.

## Exact new reduction

Let `Reach` be finite forward reachability under `nextC`, starting at `(5,0,1)`. The main theorem `BB6CLine.stops_iff_thin` proves:

```text
(∃ s, Reach s ∧ nextC s = none)
    ↔
(∃ j : Nat, Reach (0, 2*j, 4*j+10)).
```

Equivalently, the first counter must be zero and the second counter even, with **third counter exactly twice the second plus ten**. This is a blank-start statement quantifying over arbitrarily many transitions and all natural `j`, rather than a bounded computation or synthetic-start construction.

Proof sketch:

1. Define the *wing* `W(a,k,c) := c=a+5 ∧ (a+k)%2=0`. The old `(0,2j,5)` halt guard lies in `W`; every wing state deterministically descends via the high-counter decrement branch to this guard.
2. For any `nextC s = some t` with `W(t)`, prove by exhaustive symbolic case split that either `W(s)`, `s=(1,4,0)`, or `s=(0,2j,4j+10)`.
3. The exceptional state `(1,4,0)` is unreachable from the exact blank entry. Initial three states are precisely `(5,0,1)`, `(5,1,0)`, `(3,1,3)`, and after the third successful transition the monotone rank `R=a+2k+c` is at least 10, whereas `R(1,4,0)=9`.
4. Any reachable wing state must therefore have entered through the thin line. Conversely, `(0,2j,4j+10)` advances to `(4j+2,2,4j+7)`, which lies in the wing and reaches the old guard after `4j+2` sweep calls.
5. Independently classify incoming transitions to the final `c=2` layer: only `(0,0,0)` and `(0,2j,5)` can enter. Rank excludes the first from the blank entry; `nextC s=none` iff `s.c=2`.

This yields `guard_iff_thin`, `halting_layer_iff_thin`, and `stops_iff_thin`, plus the supporting predecessor and rank invariants.

## Verification

`CLine.lean` is standalone and imports only the bundled `Std`. It compiled with **Lean 4.36.0-rc2**. The `#print axioms` outputs for all three main theorems are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The GitHub file's complete content was cross-checked against the locally compiled source modulo a comment-only change (matching full character length and FNV-1a fingerprint).

## Next research obligation

Establish or refute `∀ j, ¬ Reach (0,2*j,4*j+10)` from the initial `(5,0,1)`, preferably through a genuine modular or symbolic return-map invariant for reachable zero-first-counter sections. The new diagonal gate allows attacks on a specific relation among the two other counters, rather than the whole `c=5` even-`k` guard.

No blank-tape machine classification or BB(6) bound is claimed.

## Second, stronger gateway theorem

The fully Lean-checked theorem `stops_iff_reset_or_side` sharpens the diagonal condition to the disjunction `∃ j≥1, Reach (2*j+1,3*j+4,0)` or `∃ m, Reach (0,2*m,12*m+23)`. The proof is preserved with SHA256-verified reconstruction in `gates-lean.tar.xz.b64` and `reconstruct.py`, with complete explanations in [RESET-GATEWAY.md](./RESET-GATEWAY.md). It remains an intermediate blank-entry criterion, with both target families undecided.

## New all-time modular invariant and infinite exclusions

The strongest proved statement is now `stops_iff_stronger_gates`: stopping iff a reachable reset `(2*j+1,3*j+4,0)` exists with `j>=1` and `j%4 != 1`, or a reachable side gate `(0,4*n,24*n+23)` exists with `n>=1`. This uses the global reachable invariant `c>=4 ∧ (a+k)%4>=2 → k%2=c%2`, fully Lean-checked for all transitions, and excludes two infinite modular subfamilies. Sources, SHA-256 verified reconstruction and mathematical limitations: [PARITY-GATES.md](./PARITY-GATES.md). **Both remaining classes remain unclassified.**
