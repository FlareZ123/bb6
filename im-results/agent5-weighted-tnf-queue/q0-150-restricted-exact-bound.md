# A 2,675-machine finite subset with candidate exact busy-beaver maximum 13,007,747

**Status (2026-11-28):** the combinatorial membership census is exact and reproducible; the maximum ordinary halting score is **currently a well-supported candidate**, not yet an aggregate kernel-accepted theorem, because the independent short-leaf Lean source batch is still in progress. This is only an explicit **restricted** family, not all six-state machines and not Canonical40.

Let `P` denote the explicitly enumerated 107 distinct one-hole partial tables in [q0-150-complete-frontier.json](q0-150-complete-frontier.json), taken from frozen source-normalized q0-150 run 46031415066 (zero capped leaves, 5,905,429 candidate tree nodes). Let `F` be the union, over p in P, of its 25 complete two-symbol/six-state machines obtained by choosing a HALT or one of 24 ordinary transition instructions at p's sole unspecified slot.

An explicit exhaustive 107×25 word comparison shows **every completed table in F is distinct**, so **|F| = 2,675**, including exactly **107** full machines containing a HALT instruction. The other 2,568 complete machines have no HALT transition at all and therefore syntactically run forever. This finite-table counting conclusion depends only on explicit literal tables, not on trust in the exhaustive source search tree. Reproduce with [audit-q0150-restricted-score.cjs](audit-q0150-restricted-score.cjs).

Of the 107 HALT-completed machines:
- The exact one-hole first-query primitive executions of **102** machines reach the missing slot, so their HALT-completed versions stop on the immediately following step. **97** are short (at most 37,402 nonhalting primitive steps before querying the hole), checked by new [generator](generate-q0150-short-leaves.cjs) whose independent 16-shard original-source CI is run [46093648366](https://github.com/FlareZ123/bb6/actions/runs/46093648366). At least three shards had completed successfully by 01:42 UTC; the full suite has **not** yet been established. The other **five long finite** cases already have original-source Lean-certified Covers, including three new accepted `LongSweep3/4/5` proofs from [run 46090041659](https://github.com/FlareZ123/bb6/actions/runs/46090041659).
- The other **five** HALT-completed machines have independent original-source Lean nonhalting Covers `Raw11Q0Sweep150`, `Raw11Q0Double150`, and `Raw11Q0Frame150Rules.M0/M1/M2`; the known-move orbits never query their HALT slots.

The largest first-undefined query is **13,007,746** assigned nonhalting transitions, for
```
1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---
```
and its HALT-completed machine therefore attains **13,007,747 total ordinary steps** under the standard convention of counting the halting transition. All other 101 finite first-hole cases query their missing slot earlier. Thus the candidate identity is
```
max { number of ordinary steps until halt of m : m ∈ F and m halts } = 13,007,747.
```

A new general original-source theorem [ExactOneHoleOrdinary.lean](ExactOneHoleOrdinary.lean), currently submitted for source checking in run [46094660931](https://github.com/FlareZ123/bb6/actions/runs/46094660931), derives `OrdinaryBound (n+1)` directly from a first-hole certificate. It is deliberately distinct from the existing `WeightedBound (n+6)`, whose extra five units account for possible blank-delay normalization and cannot by itself prove the sharper ordinary maximum. The [short-case generator](generate-q0150-short-leaves.cjs) now emits both weighted `safe` and exact ordinary `exact` Lean theorems, pending source-level checker acceptance.

**Do not promote the restricted exact maximum to a theorem or to `results/` before all 107 cases and the combined bound have a source-level check.** Even after that step, mapping these source-normalized branches to the global accepted Canonical40 exhaustive covering must be proved separately.
