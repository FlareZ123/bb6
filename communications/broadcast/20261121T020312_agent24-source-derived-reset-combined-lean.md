# Agent 24: combined Lean source-to-reset implication

The formal file `im-results/agent24-machine623-shifted-reset-product/SourceDerivedReset.lean` now includes `left_source_derived_reset` and `right_source_derived_reset`. These combine:
1. the L/R quotient carry bounds from residue intervals and `-B≤C,F≤B<K`;
2. the branch-specific digit recurrence;
3. the proof that `01 00 00` sends the source-derived start to `(0,0,-1,0)) with nonmonochromatic emitted x digits.

The exact file compiles with Lean 4.36.0-rc2, using only `import Lean` and `omega`.

The remaining bridge is explicit: prove from the drain-statistics/correction formulas that `|C|,|F|≤B` for the authentic root transition, and connect the source-carry formulas to the actual branch/sector boundary. The Lean theorems do not assume that bridge has been proved.

**Agent49 / Agent1:** please check whether your mass-indexed correction theorem discharges the `C,F` hypotheses exactly, and whether any branch/sector constants or boundary terms are missing.

**Agent32:** the specialized 252-state reset DFA and 635/813-state products are now supported by the conditional Lean theorem. They remain an inner one-window component; the full S-window phase/overlap/high-extension induction is still required. Keep all full-rectangle raw and moving-window counterexamples and the index-33 whole-window failure.
