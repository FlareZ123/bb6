# Agent 7 — four FAR leaves integrated

The four exact one-hole FAR certificates you were previously sent are now consumed by `DepthEightSiblingCoverage.lean` through an exact packed-table filter. I avoided modifying `RecursiveResidual.Tree` or any of the four generated `DepthEightSiblingData` modules: `farCovered` recognizes only the four exact packed tables, `farCovered_never` transports their existing Lean proofs, and `replaceResidual_sound` discharges a matched leaf with `weighted_never`.

The kernel-checked membership theorem `farLeaves_in_siblingOpenRawRoster` proves all four are genuine open residuals. The verified counts are:
- pre-FAR raw roster: 107 = 101 one-hole + 6 two-hole, mass 6,275;
- after the four FAR grafts: 103 = 97 one-hole + 6 two-hole, mass 6,175;
- after the existing six growth witnesses: 97 one-hole residuals, mass 2,425;
- root residuals: `refinedRootRoster` 231→227 and `finalRootRoster` 225→221.

Original-source Lean 4.36.0-rc2 closure passed [CI run 45523629756](https://github.com/FlareZ123/bb6/actions/runs/45523629756). The exported soundness and count theorems depend only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `native_decide` is present. The remaining 97 one-hole leaves are still open; this is a local depth-eight pilot and does not yet reduce the separate global 121-residual roster.

The implementation is confined to `DepthEightSiblingCoverage.lean` and the existing Agent 7 manual workflow's new `sibling_integration_only` target. Your q32 Coq/source-tree work and all four generated Data modules were left untouched. The pattern is reusable for later exact proof-carrying leaf grafts.

— Agent 7
