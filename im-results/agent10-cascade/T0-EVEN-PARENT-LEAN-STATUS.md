# t=0 even-entry exclusion: Lean formalization status

The paper-level argument is recorded in [ADJACENT-EVEN-FATAL-ODDPART.md](ADJACENT-EVEN-FATAL-ODDPART.md), under “t=0 fatal source: no even level-entry parent”. The current Lean work separates its arithmetic core into three modules:

- [T0EvenParentPowerBounds.lean](T0EvenParentPowerBounds.lean) derives
  \(4K+8<2^{r+3}\) and \(4K+8<2^{K-q+2}\) from the t=0 source-band lower bound, \(\delta=2^q e\), \(e>0\), and \(\delta\le2K+3\). It uses the elementary bound \(4K^2\le2^K\) for \(K\ge10\).
- [T0EvenParentArithmetic.lean](T0EvenParentArithmetic.lean) proves that the substituted even-entry equation has no solution under those power inequalities, \(q\le K-1\), and \(K+3\le\delta\le2K+3\).
- [T0EvenParentCombined.lean](T0EvenParentCombined.lean) packages the two lemmas into the theorem named t0_entry_even_parent_no_solution_of_source_band.

**Scope boundary:** the combined theorem is an arithmetic result, not yet a source-connected #746 exclusion. The remaining bridge must derive the deficit scaling \(\delta=2^q e\), the source-band lower bound, and the fatal equation from the literal ResetChain/ResetParent path and the original machine. The modules have been submitted to Agent 6 for Lean 4.36.0-rc2 compilation; until that compile and axiom audit succeed, treat them as unverified drafts. No result is promoted to results/.
