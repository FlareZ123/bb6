# Authentic #429 blank-root connection to the canonical Junc frontier

**Status: source-composition candidate; original-source CI for this new combined module is pending.** This dossier intentionally remains under `im-results/`. It does not claim an all-time nonhalting theorem or a BB(6) bound.

## Exact root-connected statement

`RootToJunc.lean` composes three existing source-level components:

1. The literal original #429 table is identified pointwise with the repository's canonical `target429` table by `BB429RootEntry.source429_eq_target429`.
2. The authentic blank A-root reaches physical `J(0,0)` after 35 successful raw steps. Its head is 3, and the entire two-sided tape is `jTape 0 0` translated by 3.
3. The original-source high-zero theorem `BB429High0Physical.j_high0_to_junc_raw 0` takes canonical `J(0,0)` to `junc 0 0 12` in 110 steps, with head displacement -6.

Translation invariance and the head-maximum monitor composition yield the combined 145-step statement:

```lean
runWithHeadMax target429 145 blank =
  some (translatedJ 0 12 (-3), 12)
```

The endpoint is exactly represented by `junc 0 0 12`, has physical head -3, has a mark at coordinate 12, and is blank at every coordinate strictly greater than 12. Thus the cumulative maximum head coordinate and the endpoint's rightmost marked cell both equal 12 at this authentic-root checkpoint.

The proof is deliberately compositional: the first 35-step segment has monitored maximum 6; the 110-step high-zero segment, started at the physical J(0,0) head 3, has monitored maximum 12; the generic monitor law combines them with `max 6 12 = 12`. The complete endpoint tape is transported through `Represents` and `represented_junc_eq_translatedJ`, not inferred from a finite window.

## What this closes, and what it does not

This closes the missing interface between the 35-step authentic blank-root entry and the already source-certified high-zero J/Junc macro. It supplies an exact, physical Junc checkpoint for future history-sensitive proofs.

It does **not** prove the universal premise in `BB429FreshFrontier.all_C_zero_at_record_head_implies_nonhalt`: every genuine C/0 entry must occur at or beyond all earlier head positions. A finite root checkpoint is not an all-time invariant.

A concrete next gap is visible in the chart dynamics. Starting from `J(0,12)`, two high-three branches reach `J(9,0)`; this lies outside the five-way `chartStep_complete` domain `2*u ≤ w+1`. The low-J deficit-18 continuation and the history-sensitive head maximum through that region must be closed, or a genuine C/01 halt witness must be found. Do not infer nonhalting from the current checkpoint.

## Verification

The new module imports the existing root-entry bridge, high-zero physical return, high-three translation theorem, and canonical Junc representation. The combined proof must be compiled against their actual repository modules with Lean 4.36.0-rc2 and its printed theorem axioms checked for `sorryAx`. The manual-only workflow `.github/workflows/agent18-429-high0.yml` is being extended to include this combined audit. Until that run succeeds, treat the new theorem as a formal proof candidate, not as an independently CI-certified result.
