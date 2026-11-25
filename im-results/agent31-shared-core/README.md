# Agent 31 shared-core roster and suffix-frame work

This directory contains **intermediate, champion-independent proof interfaces**. None of the roster modules here is an exact BB(6) result: every `exact_at_target` theorem leaves all retained `Cover` premises and an attaining blank-start witness explicit.

## Roster layers

- `CanonicalTwoParentRosterOnly.lean`: rebuilds the raw107+raw114 bounds and the 76-entry quotient dichotomy without importing the champion-specific `Canonical77ExactComposition` or `TM63RawUpperInterface`.
- `Canonical75RosterOnly.lean`: applies the source-accepted raw117 cut to the 76-entry roster. Its intended interface is 75 residual Covers at any target B≥7014, plus an attaining witness.
- `Canonical75Raw112RosterOnly.lean`: alternative 75-entry roster obtained by removing the raw112 parent, with target B≥100000.
- `Canonical74Raw107Raw114Raw117Raw112RosterOnly.lean`: combines the raw117 and raw112 cuts. Its `decide` proofs test that the raw112 parent remains distinct after the raw117 cut and that exactly 74 representatives remain. This is a draft until source-compiled.

The 75/74 counts and raw112 membership are intentionally executable Lean checks, not assumptions. If a count or membership proof fails, inspect the actual quotient representative rather than weakening the theorem.

## Right-suffix frame lemma

`../agent31-three-hole-tnf/RightFrame.lean` adds `SafeRight` and `run0_append_right_of_safe_eq`. It proves that a finite run on an explicit right-tape prefix extends unchanged under every opaque appended suffix, provided every rightward move consumes a cell from the visible prefix. This is intended for recursive counter encodings such as the raw112 high stack.

The frame theorem and its exact-output corollary were tested locally with Lean 4.36.0-rc2 against reconstructed zipper definitions. The repository import closure is being checked through the existing raw112 carry CI workflow.

## Current evidence status (2026-11-25)

- Raw112 original-semantics carry/sibling audit: run 45595822219 passed; the two `never` theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Raw112 full parent-cover audit: run 45596113340 was in progress at last check. Its intended theorem is a `Cover (WeightedBound 100000)` for the raw112 parent.
- Right-suffix frame plus sibling audit: run 45597008330 was queued at last check.
- Shared canonical raw107/raw114/ champion audit: run 45591337117 was still compiling its shared closure at last check.

Do not treat the pending runs or draft roster modules as source-accepted until their CI artifacts and theorem axiom profiles are available.
