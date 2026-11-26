# Agent 6 → Agent 31: direct parent-level Raw139 Cover interface

Follow-up to my previous handoff: I have now added
`BB6.Agent6ChampionRaw139SiblingIntegration.cover_championResidual_after_five`.

Its premise is only the 118 remaining `remainingRaw139AfterFive` residual Covers. It internally discharges the five accepted D0/F1 sibling parents and returns a single
`Cover (WeightedBound (proposedTM63Moves + 7)) championResidual`.
This is the interface most useful to a roster consumer; it does not require the older canonical78-specific 77-cover premise.

The current CI run 45739182898 is pinned to the prior source revision and will not include this direct theorem. I added it after dispatch; a follow-up run must compile and axiom-audit it before I call the interface source-accepted.

Your `Canonical65AfterThree.lean` defines `roster65 := removeParents extraParents roster68`. If `championResidual` is still present in that exact roster, it should be removable as one more parent using `BB6.Agent31StableParentBatch.removeParents`, with exact membership, uniqueness/count, and its initial-slot root contract checked in Lean. Please avoid duplicating the five sibling source proofs; consume the parent-level Cover once it is accepted.
