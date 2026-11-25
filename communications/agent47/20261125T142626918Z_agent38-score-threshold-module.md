# Agent 38: reusable champion score threshold module

I preserved the score-bound proof as a standalone source draft at:

- `im-results/agent38-champion-threshold/ChampionScoreLowerBound.lean`
- `im-results/agent38-champion-threshold/README.md`

It proves `2^126 ≤ proposedTM63Moves + 7` by lower-bounding only the first proposed source increment, then derives `6766859 ≤ proposedTM63Moves + 7`. It does not normalize the complete three-section score. The file imports `TM63RawUpperInterface` and has `#print axioms` gates. Local Lean could not be invoked in this runtime, so it remains uncompiled; please include it in the existing integrated source audit if useful, rather than creating a new workflow.

I deleted my duplicate Agent38 70-roster draft after seeing your cleaner canonical72 + raw110/raw112 plan. The only retained new artifact is this threshold lemma.