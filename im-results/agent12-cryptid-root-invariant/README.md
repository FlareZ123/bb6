# Cryptid root stack: source-faithful countdown and growth candidate

**Status: intermediate computational research.** The previous blanket withdrawal of the root trace was based on an incorrect reading of the pinned source. `mode_DL_0_n_closed` token-normalizes right-head 1, but `mode_DR_n_n_closed` token-normalizes only right-head 0; positive DR right heads take the ordinary branch. The #490 mirror and #85 evaluator swaps cancel, so the blank-root stack seed is `DR(L=[0,0],R=[1])`. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the exact source clauses and correction.

The simulators have been restored to the source-exact DR split. With the independently source-audited token-normalizer corrections retained, a persistent-list V8 replay reproduces the root checkpoints through macro 1,153,484 and reaches the candidate DR/G/B growth family. The countdown samples, finite reset, and 76-successor tail-insertion tests also pass. These are source-transcribed computations, not kernel-checked Lean theorems and not yet an original-TM nonhalting proof.

## Current research map

- [ModeDRBranchAudit.md](./ModeDRBranchAudit.md): exact source distinction between DL and DR; refutes the alleged 19-step/36-step DR-head-one cycle; records the restored source-transcribed replay.
- [RootCountdownGrowth.md](./RootCountdownGrowth.md): root prefix, countdown samples, reset, 50,000-successor entry, and candidate 76-successor growth macro.
- [TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md): source-level corrections to `tok_EL_1` and the CR `1,1` token suffixes. Its later root-status discussion predates the DR-branch correction; use ModeDRBranchAudit for current status.
- [fast_root_stack_sim.js](./fast_root_stack_sim.js): persistent-list interpreter with the source-exact mode rules.
- [verify_root_corridor_macro.js](./verify_root_corridor_macro.js): finite regression checks for the source branch, countdown samples, reset, and growth macro.
- [HPhaseGrowth.md](./HPhaseGrowth.md): separate H-phase macro; its previous falsification relied on the same incorrect DR right-head-one branch and needs its entry path checked independently.
- [RootCorridorMacro.md](./RootCorridorMacro.md): historical corridor analysis; the previous blanket withdrawal used the same branch misreading. Do not rely on every corridor identity until it is re-run against the restored interpreter.
- [../agent48-cryptid-root-cycle/DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md): preserved historical report, now withdrawn by the source audit.

## Formal status and next step

No Lean compile or transitive axiom audit has been performed for this root-growth candidate. The local shell has continued to fail before executing commands, so CI has not been used as a substitute for local preflight. The next mathematical task is to formalize the exact source mode clauses and token closures, then prove the quantified countdown, finite reset, long root entry, and arbitrary-suffix 76-step insertion. Keep stack-successor counts separate from raw TM steps and from a theorem about the original machine.
