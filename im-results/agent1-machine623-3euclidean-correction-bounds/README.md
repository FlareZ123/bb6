# Agent 1 — #623 complementary affine-buffer and gap-cocycle work

**Status: intermediate research only.** Nothing here proves that the blank-root orbit is nonhalting, and nothing determines BB(6).

## Contents

- [ComplementBuffer.md](ComplementBuffer.md) — exact conditional statement of the complement-to-strong-right theorem, its scope limitation, and the synthetic counterexample D(126,23) -> D(96,91) -> Halt. The two near-diagonal families are not an exhaustive set of possible terminal states.
- [DrainDigitStack.md](DrainDigitStack.md) — exact ternary digit-stack analysis of evalA, including the early-exit case when the initial low-order run of ternary 1s is longer than the first counter. The failure congruence is source-proved; the full success normal form has not yet been packaged as a Lean theorem.
- [RootRayGapCocycle.md](RootRayGapCocycle.md) — exact two-statistic recurrence for the branch-specific old-ray terminal distance, using signed first-counter drop D and outer drain count r. It includes the exact output-side predicate, all eight gap/scale updates, and the mod-3 reduction. This is an algebraic consolidation, not a Lean-verified new theorem.
- [ComplementBufferSource.lean](ComplementBufferSource.lean) — source draft for the complement-to-strong-right theorem. Do not claim CI certification without checking a successful pinned source run.

## Current mathematical bottleneck

The root terminal envelope says an immediate predecessor of a terminal state must lie in the old affine cone. It does not force the terminal state into either near-diagonal family. The explicit synthetic trajectory D(126,23) -> D(96,91) -> Halt has an old-cone predecessor and terminal third counter 91, but the terminal state has a=d+5. The genuine root problem is to exclude all source-certified terminal windows from old-cone predecessors in all four sectors.

A promising direction is to combine the exact gap cocycle with the 3-adic residue-separation observation in [Agent32's message](../../../communications/agent41/20261117T074927Z_agent32-3adic-terminal-residue-observation.md). The remaining challenge is to control D and r along the authentic D(0,7) orbit strongly enough to prove that the residue of the branch-specific distance cannot enter the logarithmic terminal window.

## Source dependencies

- Agent41: im-results/agent41-623-3euclidean/DrainValuationNormalForm.md
- Agent22: im-results/agent22-623-root-ray-20k/ExactRayCorrectionRelations.lean
- Agent49: im-results/agent49-parity623/TerminalRatio4Source.lean, CanonicalRayRootDistanceArithmetic.lean, ExactEvenSectorSource.lean, ExactOddSectorSource.lean
- Agent8: im-results/agent8-623-inverse/RootGapScaleDynamics.md

All source-derived claims should be kept distinct from finite replay evidence and algebraic notes that have not been source-compiled.
