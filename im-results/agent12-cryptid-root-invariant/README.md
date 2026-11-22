# Cryptid #490 / D0: corrected source audit and surviving countdown

**CRITICAL WITHDRAWAL — 2026-11-22**

The previous no-swap root replay and 76-step growth route are withdrawn. The projected CR transition function in `NoSwapGrowth.lean`, `fast_root_stack_sim.js`, and `verify_root_corridor_macro.js` mistranscribes the pinned #85 source branches for CR left prefixes `1,0`, `1,1`, and `1,≥2`; it also has the wrong empty-list bump. The `rfl` theorem in `NoSwapGrowth.lean` proves only that incorrect projected function. See [Agent 12's critical correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).

## Confirmed source facts

- The #490 and #85 `evalStackCfg` argument reversals cancel under the mirror. For every mode `m`, #490 `evalStackCfg m L R = mirrorCfg f (#85.cfg_m L R)`, with `f = ![5,4,2,0,1,3]`.
- The #490 blank-entry theorem gives the exact seven-raw-step entry to the mirror of #85 `DR(L=[0,0],R=[1])`.
- The first two DR successors are ordinary source branches: raw time 7 `DR([0,0],[1])`; execute 4 reaches `DR([0],[1,0])) at time 11; another execute 4 reaches `DR([],[1,0,0])) at time 15.
- The corrected #490/D0 raw-time-36 alignment is recorded in [DeepMindStackReduction.md](../agent32-cryptid-padding/DeepMindStackReduction.md). The cross-library initial-configuration lemma still needs exact dependency compilation.
- The direct `D_n(c)` countdown recurrence in [RootCountdownSweep.md](./RootCountdownSweep.md) uses only CR-left-zero and CR-empty, plus ordinary EL/DL/DR branches. It survives the specific CR transcription correction as a source-branch derivation and bounded replay, but is not yet a quantified Lean theorem.

## Research map and evidence status

- [RootCountdownSweep.md](./RootCountdownSweep.md): the surviving direct countdown sweep decomposition; proof architecture and bounded computation, not yet compiled.
- [RootCountdownGrowth.md](./RootCountdownGrowth.md): historical root-growth dossier, explicitly withdrawn except for the confirmed orientation/entry facts and its link to the surviving countdown.
- [ModeDRBranchAudit.md](./ModeDRBranchAudit.md): pinned-source DR branch distinction and the corrected initial DR steps only; it does not validate the full root path.
- [NoSwapGrowth.lean](../agent48-no-swap-projection/NoSwapGrowth.lean): **withdrawn projected model**. Its CR clauses are not source-exact; do not use its `growth76` theorem as evidence.
- [fast_root_stack_sim.js](./fast_root_stack_sim.js) and [verify_root_corridor_macro.js](./verify_root_corridor_macro.js): historical replay/checker using the incorrect CR transition function; root indices, macro counts, and token-event locations are untrusted.
- [RootCorridorMacro.md](./RootCorridorMacro.md): historical shared-corridor and c=1 identities from the withdrawn projected model; do not rely on them.
- [TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md): source-level token-normalizer corrections; these do not establish that the blank-root trajectory reaches a token checkpoint.
- [HPhaseGrowth.md](./HPhaseGrowth.md): separate projected H-phase macro; it also requires a fresh audit against the corrected source transition rules before being used.
- [Agent 35's RootRightGrowthMacro.append.lean](../agent35-cryptid-mirror-cancellation/RootRightGrowthMacro.append.lean): its `root_evalStackCfg_DR` definitional normal form is correct, but the macro theorem target is invalid because its endpoint came from the mistranscribed projection. Do not dispatch its current workflow.

## Next mathematical work

1. Replace the projected CR cases with the exact source equations in #85 `mode_CR_n_n_closed` lines 928–953 and set the first-coordinate empty bump to `[0]`, matching `bumpPairHead []=[(0,0)]).
2. Audit every remaining projected branch and token closure against the pinned source before trusting a simulator.
3. Recompute the blank-root continuation from the confirmed raw-time-15 DR state. Do not reuse the withdrawn 22,099-step prefix, 1,131,748 growth seed, 76-step insertion, or associated raw totals.
4. Formalize the direct `D_n(c)` sweeps in the #85 module and lift them with `reachesPlus_mirrorCfg` (Stack.lean lines 359–365). Then establish whether the corrected root trajectory reaches a countdown state or a halting cylinder.

No complete blank-root-to-cylinder path, infinite orbit, halting proof, nonhalting proof, or BB(6) value is currently established.