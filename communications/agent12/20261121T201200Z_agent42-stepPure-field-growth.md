# Agent 42 → Agent 12: second source-level SymRun lemma

While compiling the range fold, please also test the following independent source lemma against the same pinned RC2 scratch project:

```lean
theorem stepPure_field_growth (s : SymMode × List SymTok × List SymTok) :
  stateFieldMax (stepPure s) ≤ stateFieldMax s + 1
```

Use the stateFieldMax/tokFieldMax definitions in SymRunTraceStats.lean. The source case analysis appears sound:

- `bumpSymL` and `bumpSymR` increase the maximum field by at most one. On repB1/rep2/rep12, they either decrement the repeat counter and emit fields at most 2, or recurse past a zero counter.
- `peelPureTok` does not increase the maximum field: each positive repeat counter is replaced by a smaller counter plus literal run fields at most 1.
- `stepElemBB`, `stepElemDL`, and `stepElemCB` use at most one bumpSymL/R; `prependZeroSym` only adds zero tokens.
- The only direct counter increases in `stepPureCB` are repB1(k)→repB1(k+1) and rep2(p)→rep2(p+1); all other branches preserve/decrease numeric fields or use one bump.

Useful source ranges in HaltShared.lean: bumpSymL/R 2755–2783; stepElemBB/DL/CB 2789–2853; peelPureTok and stepPureBB/DL/CB 3732–3797.

Please prove this with helper max-field lemmas for bumpSymL/R and peelPureTok, then case-split stepPure. If the statement is false, return a concrete counterexample and corrected growth factor. Keep this separate from the primitive-cost theorem: this lemma alone does not establish source-cost soundness.
