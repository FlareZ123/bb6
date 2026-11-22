# Cryptid root stack: source-faithful countdown and growth candidate

**Status: intermediate computational research.** The previous blanket withdrawal of the root trace was based on an incorrect reading of the pinned source. `mode_DL_0_n_closed` token-normalizes right-head 1, but `mode_DR_n_n_closed` token-normalizes only right-head 0; positive DR right heads take the ordinary branch. The #490 mirror and #85 evaluator swaps cancel, so the blank-root stack seed is `DR(L=[0,0],R=[1])`. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the exact source clauses and correction.

The simulators have been restored to the source-exact DR split. A persistent-list V8 replay reproduces the root checkpoints through macro 1,153,484. More importantly, the first root-connected DR/G/B growth seed occurs earlier, at macro 1,131,748. Its entry is now decomposed into the c=1 corridor `D_484(1) → F(1939) → G(1939) → H(1939)`, 483 repetitions of a 38-successor H-padding macro, and one 179-successor H-base macro. The subsequent 76-successor insertion macro adds B to an arbitrary right suffix. The source-transcribed raw costs are 93,556 raw TM steps from `D_484(1)` to the first growth seed, then 254 raw TM steps per insertion. These are computational proof targets, not kernel-checked Lean theorems or an original-TM nonhalting proof.

## Current research map

- [ModeDRBranchAudit.md](./ModeDRBranchAudit.md): exact source distinction between DL and DR; refutes the alleged 19-step/36-step DR-head-one cycle; records the root-connected H-family entry and raw-step decomposition.
- [RootCountdownGrowth.md](./RootCountdownGrowth.md): countdown family, reset, c=1 corridor, H-padding/H-base induction, first DR/G/B seed at macro 1,131,748, and tail-parametric 76-successor growth.
- [TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md): source-level corrections to `tok_EL_1` and the CR `1,1` token suffixes. Its later root-status discussion predates the DR-branch correction; use ModeDRBranchAudit for current status.
- [fast_root_stack_sim.js](./fast_root_stack_sim.js): persistent-list interpreter with the source-exact mode rules.
- [verify_root_corridor_macro.js](./verify_root_corridor_macro.js): finite regression checks for the source branch, countdown samples and costs, reset, c=1 corridor, H-padding, H-base, root entry, 76-step growth, and raw-step totals.
- [HPhaseGrowth.md](./HPhaseGrowth.md): separate H-phase CR macro. Its 76-step insertion identity remains a projected-system result and is not the root-connected route used by the H-padding/H-base construction.
- [RootCorridorMacro.md](./RootCorridorMacro.md): shared-corridor and c=1 family analysis underlying the root entry. Distinguish finite regression evidence from the still-unproved quantified lemmas.
- [../agent48-cryptid-root-cycle/DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md): preserved historical report, now withdrawn by the source audit.

## Formal status and next step

No Lean compile or transitive axiom audit has been performed for this root-growth candidate. The local shell has continued to fail before executing commands, so CI has not been used as a substitute for local preflight. The next mathematical task is to formalize the quantified D_n corridor and reset, c=1 exit, H-padding and H-base identities, and arbitrary-suffix 76-step insertion; then compose them through the exact #490/#85 evaluator and discharge the initial token-normalizer event. Keep stack-successor counts separate from raw TM steps and from a theorem about the original machine.
