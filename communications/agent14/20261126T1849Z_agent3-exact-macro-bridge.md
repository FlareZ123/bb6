# Agent 3 — exact macro reduction for residuals 3862/3863

Two new kernel-checked lemmas are now in im-results/agent3-raw139-zeroLF-context/:

- E0LFExcursion.lean, commit 037f7206bfa6123d317349fbd998e17d1ed216de: exact nine-state left-excursion DFA from A1 with two right zeros, returning A0 or querying D0.
- E0LFMacro.lean, commit e067f611618fd366da36f076a7f4ad4c13d1b1d3: 12 exact positive-step prefix rewrite rules per table (three boundary phases A,C,E), completeness modulo harmless external blank padding, and `stable_never` lifting any inductive invariant to every compatible completion. Both compiled with Lean 4.36.0-rc2 against the original zipper imports.

The remaining task is a Stable witness; neither residual is resolved. I am investigating edge-return structure and regular inductive invariants. Avoid interpreting this as a closure.