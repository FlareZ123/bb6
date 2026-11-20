# Agent 1 — #623 complementary affine-buffer and gap-cocycle work

**Status: intermediate research only.** Nothing here proves that the blank-root orbit is nonhalting, and nothing determines BB(6).

## Contents

- [ComplementBuffer.md](ComplementBuffer.md) — exact conditional statement of the complement-to-strong-right theorem, its scope limitation, and the synthetic counterexample D(126,23) -> D(96,91) -> Halt. The two near-diagonal families are not an exhaustive set of possible terminal states.
- [DrainDigitStack.md](DrainDigitStack.md) — exact ternary digit-stack analysis of `evalA`, including the early-exit case when the initial low-order run of ternary 1s is longer than the first counter. The failure congruence is source-proved; the evaluator-only full success normal form remains a mathematical derivation. The separate whole-drain source-to-transducer bridge is in `DrainDigitStatsSource.lean`.
- [DrainDigitTransducer.md](DrainDigitTransducer.md), [DrainDigitStatsSource.lean](DrainDigitStatsSource.lean), and [DrainDigitSourceBridge.lean](DrainDigitSourceBridge.lean) — a three-state weighted ternary transducer plus source-linked theorems for successful budgeted `drainB` calls. In particular, `drainB_digit_transducer` proves the exact first- and second-counter identities in terms of output-digit counts. Combining it with Agent 22's `drainB_weighted_exact` gives the evaluator-call count as the number of nonzero output digits. This closes the per-drain source/digit-statistic bridge; the authentic-root phase invariant and its all-time closure remain open.
- [RootRayGapCocycle.md](RootRayGapCocycle.md) — exact two-statistic recurrence for the branch-specific old-ray terminal distance, using signed first-counter drop D and outer drain count r. It includes the exact output-side predicate, all eight gap/scale updates, the compact absolute-value cocycle Y'=|Y-2T|-6q', the additive X-coordinate on left branches, the D-free sector-adapted H update, the mod-3 reduction, a middle-block 3-adic certificate candidate, and a sharpened necessary terminal-predecessor strip of width 23n+140 (with the underlying D/r depth bounds source-compiled in Agent8's successful agent8-623-third-affine workflow. The complete four-sector cocycle and root nonhalting argument remain intermediate. This is an algebraic consolidation, not a root nonhalting proof.
- [ComplementBufferSource.lean](ComplementBufferSource.lean) — source draft for the complement-to-strong-right theorem. Do not claim CI certification without checking a successful pinned source run.
- [SignedCoordinateNormalForm.md](SignedCoordinateNormalForm.md) and [SignedCoordinateNormalForm.lean](SignedCoordinateNormalForm.lean) — exact signed-coordinate normal form for the four-sector affine cocycle. It factors the branch matrices through a common index-three map and an involution, then rewrites the update as a branch-independent w-coordinate and a signed old-residual v-coordinate. The self-contained Lean file was compiled locally with Lean 4.36.0-rc2; it does not close the root orbit.
- [SynchronizingWordScan.md](SynchronizingWordScan.md), [synchronizing_word_scan.js](synchronizing_word_scan.js), and [synchronizing_reset_subwords.cpp](synchronizing_reset_subwords.cpp), [synchronizing_reset_subwords_small_start.cpp](synchronizing_reset_subwords_small_start.cpp) — finite diagnostic scan of the 3-adic carry transducers. Across 9,968 root states (indices 33–10,000), both branch automata synchronize for all admissible initial carries and all nine previous digit pairs; every root word contains a common reset subword of length at most 4, ending within the first 12 symbols when the Lean-proved one-extra-digit carry bound is used. The broader carry scan also works with reset lengths up to 6 and depth 13. This is computational evidence, not an all-time invariant.

- [FatalSpectrumPullback.md](FatalSpectrumPullback.md) — exact pullback of the source-verified odd/even fatal-spectrum predicates through one canonical transition, plus branch-sensitive logarithmic bounds on the successor gap. See also [FatalSpectrumPullbackSource.lean](FatalSpectrumPullbackSource.lean) for the Lean consumer; this sharpens the generic output-gap interface but does not decide the authentic root.

## Current mathematical bottleneck

The per-drain source-to-digit bridge is now formalized in `DrainDigitStatsSource.lean`: for every successful `drainB` call satisfying its source ternary budget, `drainB_digit_transducer` gives the exact digit-weighted counter update. Together with Agent 22's weighted source theorem, this identifies the full evaluator-call count with the number of nonzero transducer output digits. The source bridge is local to a successful drain; it does not prove that the authentic blank-root orbit remains in budget or avoids a failure transition.

The remaining root problem is to prove an all-time, source-derived invariant for the authentic `D(0,7)` orbit, including the S-indexed moving-window boundary phase, the full carry rectangles, the one-low/three-high window shift, and the terminal-window exclusion. The 20,000-step replay, the 9,968-transition S-window reset diagnostic, and the observed phase sets remain finite evidence, not an induction theorem.
## Source dependencies

- Agent41: im-results/agent41-623-3euclidean/DrainValuationNormalForm.md
- Agent22: im-results/agent22-623-root-ray-20k/ExactRayCorrectionRelations.lean
- Agent49: im-results/agent49-parity623/TerminalRatio4Source.lean, CanonicalRayRootDistanceArithmetic.lean, ExactEvenSectorSource.lean, ExactOddSectorSource.lean
- Agent8: im-results/agent8-623-inverse/RootGapScaleDynamics.md

All source-derived claims should be kept distinct from finite replay evidence and algebraic notes that have not been source-compiled.


## Exact global-proof dependency and scope

The target is the pinned original Cryptids #623 machine
1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA, blank start A, whose accelerated section root is D(0,7). The machine is an authenticated open leaf in the existing global depth-four frontier; see im-results/agent8-623-frontier/README.md and the successful source/frontier runs recorded there. This work is therefore an **upper-bound-side root subproblem**, not a lower-bound candidate-score calculation.

The exact missing authentic-root quantifier is: for every n, the source run from D(0,7) is still present, equivalently no section state reaches a source failure transition. A proof of that statement would be consumed by Machine623HaltCylinder.machine623_full_cylinder_if_never in im-results/agent13-residual-frontier/Machine623HaltCylinder.lean, classifying the 25 completions of the authentic 11-row cylinder (24 are already source-proved never-halting; the remaining completion is the original #623 machine).

**Scope caution:** this root theorem alone does not classify all 25^8 completions of the broader four-row depth-four open leaf. It decides the distinguished authentic machine and its 25-machine source cylinder; a separate exhaustive or uniform argument is still required to close the entire global leaf and hence the universal BB(6) upper bound. The cocycle and terminal-window work here should be judged by whether it closes the exact D(0,7) all-time theorem, not by the number of intermediate identities.
