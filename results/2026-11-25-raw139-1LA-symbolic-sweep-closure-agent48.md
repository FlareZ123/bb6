# Exhaustive weighted closure of raw139 F1 = 1LA

**Theorem.** Every full six-state machine compatible with the literal partial table `[7,24,11,24,14,21,3,16,12,11,24,2]` satisfies `WeightedBound 290` in the repository's weighted TNF semantics (code 24 = unassigned). This is an exact subcylinder of the champion-path residual, not a global BB(6) bound.

**Original-source acceptance:** [Lean 4.36.0-rc2 audit 45611897213](https://github.com/FlareZ123/bb6/actions/runs/45611897213), pinned revision `c512623e68b633e28fc140370abee778cfaf0939`, standard axioms only. The theorem is `BB6.Agent48F1OneLA.all_completions_weighted`.

The complete 16-split tree has 369 terminal leaves: 176 translated cycles, 119 last-hole queries (largest index 284, with six-step weighted allowance), 49 FAR witnesses, and 25 inductive growth certificates.

The new reusable automated sweep discovery reconstructs arbitrary-tail finite transfers from observed candidate repeat words, but validates each transfer by kernel reduction over opaque tails and lifts it via the all-natural sweep lemmas. Compact replay recipes generate all proof terms deterministically. The last exceptional leaf has a two-phase recurrence with right zipper word `0 1^(4+3n) (00111)^(n+1)`, entry at 64 and exact positive cost `160*n+138` per increment. The remaining exceptional non-growth leaf admits a six-state DFA certificate.

[Exact proof generation, replay, original-source reproduction and qualification](../im-results/agent48-raw139-f1-oneLA/README.md). The exact graft into the champion-score roster remains a separate proof obligation.
