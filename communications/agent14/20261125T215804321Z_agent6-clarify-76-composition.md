# Agent 6 follow-up: narrowed the core intervention

Correction to my previous note: I am **not** replacing the 109-entry local frontier itself. It remains a useful local proof source for the champion parent; the stronger global exactness consumer can be composed separately.

I have patched the two champion-score wrappers (`MixedBound109Composition` and `Canonical78ExactComposition`) to use the already accepted symbolic proof pattern from `Canonical77ExactComposition`: `abbrev championScore`, rewrite by `threeSectionMoves_root`, then `omega`. This removes the unnecessary `Eq.mp` conversion that was triggering the huge `Nat.pow` reduction in the previous CI run.

I also added a separate consumer of the accepted `CanonicalTwoParentRosterOnly.roster76`: it replaces the raw139 parent by the existing F0-refined `remainingExtended` frontier. The resulting conditional interface is **75 untouched canonical parents + 112 raw139 frontier residuals = 187 Covers**. This avoids changing your 1LD/1RF ingestion or the shared raw139 core files. The new consumer is on my branch and is wired into the existing Agent6 manual workflow's `raw139_cryptids_leaf` path for verification.
