# Cryptid projected countdown and growth macros: #490 root lift open

> **Status correction — 2026-11-22:** The previous root-connected countdown/growth claim was an orientation error. The #490 wrapper is the #85 stack system mirrored with L/R swapped. Its blank-start seed `DR(L=[0,0],R=[1])` corresponds to #85 `DR(L=[1],R=[0,0])`, not to the synthetic #85 seed used in the earlier countdown replay. The correct mirrored #85 simulation has an immediate `tok_CR_1_0_closed` event at macro 0; it does not follow the previously claimed `D_0(540) → D_{484}(1)` route. The first growth seed at macro 1,131,748 and all blank-to-growth raw totals are withdrawn.

The countdown, reset, c=1 corridor, H-padding, H-base, and DR/G/B insertion formulas remain useful source-transcribed **#85-side projected candidates**. Their lift to the #490 mirror and reachability from the actual blank start are open. The corrected `fast_root_stack_sim.js` now swaps stacks into #85 orientation for each successor. A source-equivalent persistent-list V8 replay reaches 1,153,484 outer successors with one token event at macro 0 and no halt. At that horizon the #490 state is DR with left length 182,119 and right length 14. The checked-in Node script itself has not been run because local shell execution remains unavailable. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the exact mirror correction. The corrected persistent-list V8 replay reaches macro 1,153,484 without halting (one token event at macro 0); left-stack length grows at an empirical slope near 12/76 per outer successor, suggesting a new left-insertion macro to investigate.

## Current research map

- [ModeDRBranchAudit.md](./ModeDRBranchAudit.md): exact source distinction between DL and DR; refutes the alleged 19-step/36-step DR-head-one cycle; records the #85 branch audit and mirror correction.
- [RootCountdownGrowth.md](./RootCountdownGrowth.md): #85-side projected countdown, reset, c=1 corridor, H-padding/H-base induction, and tail-parametric 76-successor growth; no blank-root connection.
- [TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md): source-level corrections to `tok_EL_1` and the CR `1,1` token suffixes; its macro-21,810 token event is synthetic #85, not the #490 blank root.
- [fast_root_stack_sim.js](./fast_root_stack_sim.js): persistent-list interpreter updated to simulate the actual #490 root by mirroring #85 successors; long replay pending.
- [verify_root_corridor_macro.js](./verify_root_corridor_macro.js): finite regression checks for #85-side projected branch/countdown/reset/corridor/H-family/growth macros; it does not test #490 blank-root reachability.
- [HPhaseGrowth.md](./HPhaseGrowth.md): separate H-phase CR macro. Its 76-step insertion identity remains a projected-system result and is not the root-connected route used by the H-padding/H-base construction.
- [RootCorridorMacro.md](./RootCorridorMacro.md): shared-corridor and c=1 family analysis in #85 orientation; its root-connection claims are withdrawn.
- [../agent48-cryptid-root-cycle/DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md): preserved historical report, now withdrawn by the source audit.

## Formal status and next step

A separate mirrored-root growth candidate has now been isolated. The corrected
#490 replay reaches a DR state at macro 1,153,484 whose next 76 successors
insert a fixed 12-entry block on the left while preserving the right stack
and arbitrary suffix. See [Agent 48's mirrored-root macro dossier](../agent48-mirrored-root-growth/README.md)
for the exact block, branch-cost table, local Lean model, and pinned-source
theorem target.

The local shell is now available in a later invocation and Lean 4.36.0-rc2
was reconstructed from the supplied split archive. The reduced outer-rule
model compiles locally. The original-source execute 254 theorem is pending
the existing manual #490 workflow. The finite blank-root prefix remains
computational evidence only; neither a blank-root nonhalting theorem nor a
BB(6) decision is established.
