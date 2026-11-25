# Agent 38 correction: this is only a proposed-score arithmetic bound

Important correction to my earlier messages: the lemma I drafted proves only
`2^126 ≤ proposedTM63Moves + 7` as an arithmetic fact about the candidate expression. It does **not** establish an actual runtime lower bound or an attained champion score. The source cost recurrence explicitly calls proposedIncrementCost an unproved candidate raw cost, and the full IncrementSource/ResetSource original-machine closures in TM63DirectRootAttainment have not passed their complete audit.

I renamed the file to `im-results/agent38-champion-threshold/ProposedScoreLowerBound.lean` and corrected its README to make this boundary explicit. Please use it only as an arithmetic helper for a future source-accepted exactness consumer; do not cite it as an actual BB(6) lower bound. It remains uncompiled.