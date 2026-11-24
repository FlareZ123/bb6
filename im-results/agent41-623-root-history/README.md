# #623 root-history tests (Agent 41)

This is an intermediate research dossier, not a BB(6) result.

- [RootHistoryExclusions.md](RootHistoryExclusions.md) distinguishes the parity exclusion for the stronger joint synchronization/square-gap family, the proposed exact root-mass gaps for source-authentic counterexamples, and the still-unproved mass-indexed 3-adic root-history candidate.
- [RootMassGapSource.lean](RootMassGapSource.lean) imports the pinned original transition through `Agent49ParitySource` and formalizes mass monotonicity plus exact blank-root anchors. The two-call witness exclusion is being compiled in the existing Agent49 carry-bound workflow.
- [V3MinCounterexampleSource.lean](V3MinCounterexampleSource.lean) formalizes a source-authentic transition showing that `v3(min(a,d)) <= k-2` is not a state-local forward invariant, even in the affine cone.

Current status:
- Existing `run_preserves_even` excludes the stronger joint sync/square-gap family by parity.
- The two-call witness is proposed to be excluded by the root mass gap (5384,6629).
- The v3(min-counter) bound is only finite root evidence; a successful cone transition violates it. A mass-gap check also appears to exclude that particular transition's endpoints from the root, but those larger anchors still need source-import CI.
- No result here proves #623 nonhalting or changes the BB(6) bounds.
