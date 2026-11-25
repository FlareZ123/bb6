# Exact-seed active-branch projection audit for the #623 S-windows

**Status:** reproducible finite computational diagnostic; not an all-time theorem and not a proof of nonhalting.

## Scope and method

The audit covers the exact high-level root states (D_n) for (34\le n\le 10000), inclusive (9,967 states). For each state it constructs the S-window from
[
x=2(p-3q)-\gamma_s,\qquad y=6q,
]
using the existing sector constants and the (B=34\ell(S)+122) window convention.

For each window word:

1. `ResetPatternDFA.json` locates its first accepting reset.
2. `ResetPostStateDFA.json` identifies the exact paired carry seed selected by the root word.
3. The exact seed is propagated through the suffix using `PostResetCarryPairClosure.json`.
4. In parallel, `PairCarrySynchronizingSubsetDFA.json` propagates the universal image of all 66 post-reset paired seeds through the same suffix.
5. The actual outgoing branch of (D_n\to D_{n+1}) is read from the exact phase record in `SWindowEdgeRecords.json`; the universal image is projected onto its active (L)- or (R)-carry coordinate.

This deliberately uses the phase record's branch field, not the sign of (p-3q).

## Results

| Quantity | Count |
|---|---:|
| S-windows checked | 9,967 |
| Reset-DFA failures | 0 |
| Missing exact post-reset seeds | 0 |
| Exact final carries outside the universal image | 0 |
| Non-singleton universal suffix images | 84 |
| Active-branch projection singleton | 21 |
| Active-branch projection ambiguous | 63 |

The active-branch projection-size histogram among the 84 non-singleton images is:

| Projection size | Windows |
|---:|---:|
| 1 | 21 |
| 2 | 47 |
| 3 | 10 |
| 4 | 3 |
| 18 | 2 |
| 36 | 1 |

Breakdown by the recurrent component of the subset automaton (or transient states):

| Component | Windows | Active projection singleton | Active projection ambiguous |
|---|---:|---:|---:|
| B1 | 13 | 4 | 9 |
| B2 | 36 | 11 | 25 |
| B3 | 2 | 0 | 2 |
| B5 | 7 | 1 | 6 |
| B7 | 6 | 0 | 6 |
| transient | 20 | 5 | 15 |
| **Total** | **84** | **21** | **63** |

## Interpretation and limitations

The exact root-selected carry is contained in the universal suffix image in all 9,967 cases. Thus the 63 ambiguous active projections are ambiguity in the universal over-approximation, not evidence that the actual root carry is unknown. The exact seed replay selects one active state in every case.

The result does **not** show that the 63 ambiguous cases synchronize, that the same component persists under the next S-window transformation, or that the reset property holds beyond the finite range. The 84 cases are a useful target set for exact-seed transition analysis; they do not close the induction needed for BB(6).

## Reproduction

From the repository root:

```sh
node im-results/agent27-623-root-scan/active_branch_projection.js
```

The script checks the expected totals and emits the 63 ambiguous cases with their exact active state and universal active-state set. Inputs are the six JSON files named in the method above, plus the root recurrence and window construction encoded in the script.
