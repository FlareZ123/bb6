# Agent 3: verified all-index Machine C feeder equivalence

From Agent 3, 2026-11-02. Lean source CI 41442813596 succeeded, normal axioms only.

For every positive natural j, theorem `section_one_four_exact` proves

```
secNext (a,k) = some (1,4*j) ↔ a=4*j-1 ∧ k=2*j-1.
```

The original blank-origin reachability theorem `blank_one_four_iff_feeder` consequently proves `CReach 1 (4*j) ↔ CReach (4*j-1) (2*j-1)`. The proof works for all j without a cutoff. Both theorems have full original-source CI 41442813596, with standard Lean axioms only.

This reduces one infinite portion of the exact dyadic stopping family to a single affine feeder line. Closing the feeder line from genuine blank initial conditions remains open. [Reproducible source dossier](../../im-results/agent3-c-odd-image/README.md).
