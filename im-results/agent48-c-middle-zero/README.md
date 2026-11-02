# Agent 48: complete zero-middle-counter shape for Machine C

**Status (2026-11-02):** formally checked all-natural structural invariant of the exact local Machine C blank-entry acceleration. It does not decide Machine C or BB(6) and belongs in intermediate research.

Original accelerated transition definition: `im-results/agent11-c-line/CLine.lean`, blank entry `(5,0,1)`, `BB6CLine.Reach` is its inductive reflexive-transitive forward reachability.

## Result

Every reachable state `(a,0,c)` belongs to the following explicit union:

1. `(5,0,1)`;
2. `(1,0,2*k+2)` for some natural `k`;
3. `(4*k+5,0,d+4)` for natural `k,d`.

In particular, **`a % 4 = 1`** at every reachable state with middle counter zero. Every `(4*t+3,0,c)` and every `(a,0,0)` is unreachable, uniformly for all natural parameters.

The proof analyzes *all incoming original accelerated branches*; three branches can produce a zero middle counter, and all their outputs are enumerated. This is stronger than the previously source-proved parity restriction `reached_kzero_odd` in Agent21's `CBack.lean`. It may help prune symbolic predecessor trees (for instance, with k=0 leaves previously known only to require odd a), but its effect on unexplored Machine C gateway residues has **not** been established. The union is an overapproximation of actual reachable configurations: the result does not assert that each displayed shape is actually reachable.

## Verification and dependencies

- Proof file: [KZeroMod4.lean](./KZeroMod4.lean).
- Manual-only workflow: [agent48-c-middle-zero.yml](../../.github/workflows/agent48-c-middle-zero.yml).
- [Successful original-source CI 41427303952](https://github.com/FlareZ123/bb6/actions/runs/41427303952), using Lean 4.36.0-rc2; copies and compiles **unmodified** `im-results/agent11-c-line/CLine.lean` before the new file.
- Local independent Lean compilation also passed against an exact copy of the requisite source `nextC` and `Reach` declarations.
- Source theorem `BB6.Agent48.reached_middle_zero_shape` audited to exactly `[propext]`; `reached_middle_zero_mod4`, `no_middle_zero_3mod4`, `no_both_middle_and_right_zero` audited to `[propext, Quot.sound]`. No new axioms, `sorry`, or bounded-run assumptions.
- For the original six-state machine semantic link, Agent21's independent original-source bridge [CI 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481) established the machine/acceleration correspondence. This file checks only the local source-defined `Reach` lemma and does not duplicate that end-to-end bridge.

## Next

Integrate the exhaustive k=0 shape as a pruning predicate into the existing symbolic C inverse engine, compare closed family counts to previously proved and quotient-excluded residue sets, and seek genuinely new critical-gateway exclusions. Preserve negative or duplicate searches in intermediate files rather than promoting them to `results/`.
