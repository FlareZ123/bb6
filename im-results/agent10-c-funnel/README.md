# Machine C: Lean-verified halting funnel and two feeder families

**Status:** intermediate formal reduction for an unresolved BB(6) machine. This does **not** decide its blank-tape behavior, improve BB(6) bounds, or prove that either feeder is unreachable.

Target Turing machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The transition function `nextC` copies the three-counter accelerator published in Google DeepMind's Cryptids `BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`. The accelerator starts from `(a,k,c)=(5,0,1)`, and is undefined exactly when `c=2`. The upstream library already establishes the connection between that original six-state machine and its counter acceleration. Our standalone Lean file does not import the upstream module, so the cross-file equality is by source comparison, rather than by a new kernel-checked bridge.

## Main exact result

Define finite accelerated reachability `Reach` via zero or more successful `nextC` transitions. Define `blankHalts` as reaching a state where `nextC` returns `none`.

Lean 4.36.0-rc2 checks `BB6Agent10.blank_halts_iff_feeder`:

```lean
blankHalts ↔
  ∃ s, Reach (5,0,1) s ∧
    (s = (1,4,0) ∨ ∃ j : Nat, s = (0,2*j,4*j+10))
```

The exact halting question has therefore been reduced to reachable membership in **one fixed state** or a **one-parameter arithmetic family**. Both are genuine blank-entry reachability obligations.

The proof uses the "funnel" `c=a+5 ∧ (a+k)%2=0`. Every such state deterministically sweeps to `(0,a+k,5)`, a known halting precursor. Case analysis over every `nextC` transition proves that a predecessor of a funnel state either belongs to the same funnel or is precisely one of the two feeder forms above. The blank entry lies outside the funnel. A separate terminal-layer lemma establishes that no other halting route can arise: the alternative predecessor `(0,0,0)` is unreachable because no successful step produces it. This also makes the claimed equivalence **bidirectional**, rather than merely a necessary condition.

This complements Agent 8's `CriticalReach.lean` theorem relating halting to reachable `(0,2*j,5)`. It offers an earlier-entry target family for backward-closure or arithmetic invariant investigations. Both feeder branches must be excluded before a nonhalting claim is justified.

## Formal certificate

* Artifact: `Funnel.lean.xz.b64` (XZ-compressed, base64-encoded complete Lean source).
* Recovery: `unpack.py`, which checks the SHA-256 and writes `Funnel.lean`.
* Original Lean source: 10,413 bytes, SHA-256 `3094b6c7f7ba871fb6e13c10a1955e53bd4f0b6ebd410d3390e867d916225c1c`.
* Verification: Lean 4.36.0-rc2, `lean Funnel.lean`; the source imports only `Lean.Elab.Tactic.Omega`, requires no Mathlib and has no `sorry`.
* Kernel axiom audit for `blank_halts_iff_feeder`: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## Open proof targets

1. Exclude `Reach (5,0,1) (1,4,0)`.
2. Exclude `Reach (5,0,1) (0,2*j,4*j+10)` simultaneously for all natural `j`.
3. Formally integrate the standalone theorem with upstream Cryptids rather than relying on independent copies of the macro-transition function.

These are open obligations. Do not promote this intermediate criterion to `results/` as a BB(6) decision.

Author: Agent 10, 2026-11-02.
