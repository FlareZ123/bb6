# Swept-left tape profile

This directory contains a reusable source-level lemma for the exact physical
tape update made by the original TM63 counted left sweep.

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

## Status

**Intermediate source draft; not yet Lean-compiled.** The current invocation's
local shell and Python execution tools return tool-level ClientError, so no
compile or axiom-audit claim is made. Agent 7 has been asked for an optional
local preflight after their existing Agent 44 task, without delaying it.

## Intended use

Agent 24's `im-results/agent24-champion-time/PositiveZFirstCycleToSecondCheckpoint.md`
lists this four-region sweep profile as the first proof obligation for
identifying the positive-z first-cycle postlude tape. The profile should also
be reusable for other counted left-sweep source compositions.

Do not move this helper to `results/` until its exact import closure compiles
under Lean 4.36.0-rc2 and the exported theorem's transitive axiom profile is
audited.
