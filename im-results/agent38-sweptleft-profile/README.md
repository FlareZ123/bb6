# Swept-left tape profile

This directory contains an independent source-level proof attempt for the
four-region physical tape profile of the original TM63 counted left sweep.

## Main statement

`SweptLeftProfile.lean` proves that if `leftOnes T h n` and
`T (h+1) = false`, then `sweptLeft n T h` has four regions:

1. `x < h - n + 1`: the original tape is unchanged;
2. `x = h - n + 1`: the cell is blank;
3. `h - n + 2 ≤ x ≤ h + 1`: every cell is one;
4. `x > h + 1`: the original tape is unchanged.

The proof is an induction on the exact recursive definition of
`sweptLeft`, using `leftOnes_tail` and the one-cell update `holeThree`.
It is pointwise on the infinite tape; it does not assume a finite tape or
approximate the sweep by a bounded window.

## Relationship to existing work

The intended consumer already exists:
`im-results/agent24-champion-time/PositiveZFirstCycleToSecondPrefix.lean`
composes the first positive-z q4 cycle with the second-cycle prefix through
`q4Tail`. That proof obtains the same four-region profile through the
existing `s0LeftSweep_shift` theorem and its private
`s0LeftSweep_eq_sweptLeft` bridge.

Consequently, this standalone induction is an **alternative helper**, not a
missing dependency of Agent 24's composition. Do not redo that composition
or add another workflow for this file. Reuse this theorem only if a public,
direct `sweptLeft` profile is independently useful to another proof family.

## Status

**Intermediate source draft; not Lean-compiled.** The local shell and Python
execution tools in the authoring invocation returned tool-level ClientError.
The optional Agent 7 preflight request was cancelled after discovering the
existing Agent 24 composition. No compile or axiom-audit claim is made.

Do not move this helper to `results/` unless its exact import closure compiles
under Lean 4.36.0-rc2, its transitive axiom profile is audited, and it
contributes something beyond the existing `s0LeftSweep_shift` route.
