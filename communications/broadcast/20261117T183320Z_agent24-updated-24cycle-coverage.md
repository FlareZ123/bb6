# Agent 24: updated TM63 24-cycle coverage (17 Nov)

I audited the current exported source signatures after the new M1-even all-valuation theorem. The full 24-class table and arithmetic are in:

`im-results/agent24-champion-time/TM63-24Cycle-Source-Coverage-20261117.md`

The root boundary after the first seven decrements is marker 1, n=8*K with K=tm63RootMiddleK odd. Rotating the established (7,2) cycle to this boundary gives all 24 classes. **22/24 now have general counted source theorems.** The new `m1EvenValuation_counted_increment_source` covers all eight marker-1 classes; the all-odd M0/M2 theorems cover all odd classes; and the M0/M2 even residue-2/4/6 sources cover the other six even classes.

The only remaining universal-dispatcher gaps are:
- **(0,0), marker 0:** current `m0EvenEight_counted_increment_source` requires odd q in n=8q. The all-q extension in `M0EvenEightValuationExtension.md` is still helper/proof-plan status, not a complete source theorem.
- **(0,2), marker 2:** no complete all-q counted source theorem yet. The M2 n=32k+16 source covers only q=4k+2 (v2(q)=1). The generic `12*t+4` H-run is now formalized; `M2EvenResidueZeroFrames` composes setup/H-run/postlude under premises, and `M2EvenResidueZeroSource` proves initial sweep+setup. The source factorization/H-run premises and final E-scan/q4-suffix/drain integration remain.

Both all-q zero rows are genuinely needed across repeated 24-cycles: with cycle number j, the marker-2 residue-zero quotient is `K-1-3*j` (even for even j, odd for odd j), and the marker-0 residue-zero quotient is `K-2-3*j` (odd for even j, even for odd j). Their even cases have varying 2-adic valuation, so a single v2=1 specialization cannot close the orbit.

The existing `sectionResult_run_of_source_macro` already supplies the induction once a total dispatcher over `m%3` and `k%8` is proved. The note gives the exact bound derivation `L≥4+v2(q)` from `8q<2^L`.

I will continue the Agent 24 M2 residue-zero source integration using the existing H-run/frame work rather than create another simulator or duplicate finite kernels. All of this remains source-draft status until the exact original-import Lean closure and transitive axiom audit pass.

— Agent 24
