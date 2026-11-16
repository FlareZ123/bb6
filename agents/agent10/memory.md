

### 2026-11-16 addendum: t=1 Q-parent scan correction and inverse-tree scope

The t=1 Q-parent source equation is
\[
9d=32\cdot2^K+(2K+7)-(2K+7)2^{j+1},\qquad
q=4d-8\cdot2^K-K-5.
\]
The `-5` is important: t=1 means (q+K) is odd, so the floor in ((q+K)/2) contributes the parity correction. Reducing the equation modulo 18 gives the full necessary residue table:
- (K\bmod18=2,3\Rightarrow j\bmod6=0);
- (K\bmod18=8\Rightarrow j\bmod6=4);
- (K\bmod18=14,9\Rightarrow j\bmod6=2);
- (K\bmod18=15\Rightarrow j\bmod6=4).

A corrected exact-integer Python inverse-parent experiment enumerated all Q candidates with (K\le2000), using all six residue classes, odd d, and the source band. It found 110,250 candidates, none root-reachable in the exact even/odd parent relation; maximum inverse depth 11, maximum ancestor level drop 8, maximum odd exponent 9, maximum odd-edge count 4, and maximum tree size 13. This is only finite exploratory evidence, not an all-time theorem. The earlier scan that used only (j\equiv0\pmod6) and (q=4d-8\cdot2^K-K-6) was incomplete/off by one; its counts and conclusions must not be reused. A correction was sent to Agent 7 in `communications/agent7/20261116T1120Z_agent10-qparent-scan-correction.md`.

For the Q candidate, the exact deficit identity is
\[
D_K(q)=8\cdot2^K+K-q
=\frac{16\cdot2^K+10K+17+(2K+7)2^{j+3}}9
>\frac{16}{9}2^K.
\]
This gives a useful local structural fact: if q has an even parent at the same level K, that parent has level-K deficit (2D_K(q)>\frac{32}{9}2^K), above the maximum deficit (2\cdot2^K+K+1) for another same-level even-parent edge. So there cannot be two consecutive same-level even-parent edges at the top of a Q-candidate ancestry. This is not yet a root-exclusion proof; odd-parent ancestry remains the hard part.

### 2026-11-16 addendum: t=0 even-entry arithmetic formalization

The paper-level t=0 no-even-parent argument in `im-results/agent10-cascade/ADJACENT-EVEN-FATAL-ODDPART.md` has been translated into a self-contained Lean arithmetic core at `im-results/agent10-cascade/T0EvenParentArithmetic.lean` on branch `agent10/t1-q-fatal-source-20261116`. The theorem `Agent10T0Parent.t0_entry_even_parent_arithmetic_no_solution` assumes the exact substituted entry equation, (q\le K-1), (K+3\le\delta\le2K+3), and the two source-derived power inequalities (4K+8<2^{r+3}) and (4K+8<2^{K-q+2}), and proves contradiction. Agent 6 has been asked to compile it and report the axiom profile, alongside the existing `T1QParentFatal.lean` request. The power inequalities and the ResetChain/source bridge still need to be wired into Lean; do not report the t=0 exclusion as fully formalized until that is done.

The local Lean archive reconstruction was attempted from the two uploaded zip fragments and failed because the concatenated archive is truncated (embedded tar.zst size exceeds concatenated size by about 32 MB); no local `lean` executable was recovered. Do not repeat the same unzip attempt. Use Agent 6's working runtime or the targeted CI fallback.

### Next actions

1. Obtain Agent 6's compile result for `T0EvenParentArithmetic.lean` and `T1QParentFatal.lean`; repair only concrete Lean errors.
2. Formalize (2^K\ge4K^2) for (K\ge10), then derive the two power inequalities from the t=0 source-band lower bound and (delta=2^q e), (1\le e\le2K+3). Refactor the arithmetic theorem to consume the source-band bound rather than assume the power inequalities.
3. Connect the t=0 level-entry even-parent hypothesis and deficit scaling to `ResetChain`; then the special t=0 branch can be closed at the source-connected level.
4. Continue t=1 Q-parent root intersection only after Agent 7 responds; do not repeat finite forward scans or residue catalogues. The synthetic inverse tree is not an all-time decision.
