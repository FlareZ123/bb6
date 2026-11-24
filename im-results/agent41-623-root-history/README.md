# #623 root-history tests (Agent 41)

This is an intermediate research dossier, not a BB(6) result.

- [RootHistoryExclusions.md](RootHistoryExclusions.md) distinguishes the parity exclusion for the stronger joint synchronization/square-gap family, the proposed exact root-mass gaps for source-authentic counterexamples, and the still-unproved mass-indexed 3-adic root-history candidate.
- [RootMassGapSource.lean](RootMassGapSource.lean) imports the pinned original transition through `Agent49ParitySource` and formalizes mass monotonicity plus exact blank-root anchors. The two-call witness exclusion is being compiled in the existing Agent49 carry-bound workflow.
- [V3MinCounterexampleSource.lean](V3MinCounterexampleSource.lean) formalizes a source-authentic transition showing that `v3(min(a,d)) <= k-2` is not a state-local forward invariant, even in the affine cone.

Current status:
- Existing `run_preserves_even` excludes the stronger joint sync/square-gap family by parity.
- `RootMassGapSource.lean` now proves a generic mass-monotonicity lemma from the source theorem `next_strict_mass`, and contains exact root anchors at indices 23,24,77,78,79,80,81,83,84. The resulting skipped intervals are used to exclude the two-call witness, both v3 state-local counterexamples, and all source/target endpoints of the three ell=20 cone-only transitions. Pinned-source CI run 45373221495 compiled this module successfully; the theorem audit contains no `sorryAx`. The overall workflow failed afterward in Agent49's separate carry-audit module at its `root_run_38`/`root_run_39` computations.
- The simple v3(min-counter) bounds are not state-local: explicit source transitions violate both v3<=k-2 and the weaker v3<=k. The finite blank-root trace still suggests a stronger root-history property, but it is not proved.
- The nine-state `DrainState × Fin 3` product for `R_full mod 3` has been assessed and communicated to Agent 1. The source bridge already has the key `r=ones+twos` theorem; its upstream compile blocker remains in `DrainValuationNormalForm.lean`.
- No result here proves #623 nonhalting or changes the BB(6) bounds.
