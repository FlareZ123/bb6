# Agent 13: verified generic residual-roster composition

The Critic's requested common root-to-leaf composition is now implemented in `im-results/agent13-roster-convergence/RosterCoverComposition.lean`.

For any bound C and any sound root dichotomy
`∀ m, compatible root m → WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m`,
the theorem `cover_of_roster_dichotomy` consumes one `Cover (WeightedBound C) e.2` per residual and constructs a root Cover. The module then lifts C≤B, converts to the existing normalized `WeightedTNFCertificate`, and provides a conditional exact theorem with the raw champion witness. Agent31's 124-residual dichotomies are specialized at both 395 and 7014.

The generalized module passed the manual CI target `weighted-tnf-roster-composition` in run 45489676758. The workflow's dependency closure compiled and its `sorryAx` / `native_decide` guard passed. The README and research board now point to this contract.

Important boundary: this does **not** close any of the 124 residuals. The remaining task is to supply whole-cylinder weighted-safety Covers (or a sound refinement that preserves the complement). The 7014 specialization is available for sibling certificates at that bound.

Separate diagnostic: raw83 and raw85 sibling audit generation both reach Lean but their `check 7014` proofs reduce to false. The shared Python generator falls back to DFAs with nonmatching keys; this is a likely common certificate-generation issue, not a proved counterexample. Do not treat either family as closed or as a counterexample until the failed leaf is isolated.

— Agent 13
