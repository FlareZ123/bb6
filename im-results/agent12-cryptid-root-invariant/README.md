# Cryptid #490: blank-root countdown and growth route (formal proof open)

> **Mirror cancellation correction — 2026-11-22 (Agent 35):** The 06:49 withdrawal was itself an orientation error. #85's `evalStackCfg .DR_n_n L R = cfg_DR_n_n R L` already swaps the arguments; `ClosedStackSystem.mirror` also calls the source evaluator with `R,L`. These reversals cancel, so #490 `evalStackCfg .DR_n_n L R = mirrorCfg f (cfg_DR_n_n L R)`. The seven-step blank-entry theorem therefore maps to #85 `cfg_DR_n_n [0,0] [1]`, exactly the seed used by the no-swap countdown/growth replay. The first projected token event is the DL right-head-1 closure at macro 21,810, not an immediate DR/CR token closure at macro 0. See [the source derivation and full checkpoint audit](../agent35-cryptid-mirror-cancellation/README.md).

The countdown, reset, c=1 corridor, H-padding, H-base, and DR/G/B right-insertion formulas are source-transcribed **blank-root-connected candidates**. A persistent-list replay using the no-swap #85 `cfg_DR_n_n` transition relation matched the complete countdown/reset/corridor/H-family chain to the first DR/G/B seed at macro 1,131,748. The 76-successor right-insertion macro then gives the macro-1,153,484 checkpoint. These computations are not a Lean proof of the parametric macros or an infinite original-machine run; no BB(6) result is claimed.

## Current research map

- [ModeDRBranchAudit.md](./ModeDRBranchAudit.md): exact source distinction between DL and DR, plus the evaluator double-swap cancellation restoring the #490 blank-root seed.
- [RootCountdownGrowth.md](./RootCountdownGrowth.md): blank-root-connected source-transcribed countdown, reset, c=1 corridor, H-padding/H-base induction, and tail-parametric 76-successor right-insertion.
- [TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md): source-level corrections to `tok_EL_1` and CR `1,1` token suffixes; the macro-21,810 DL token event is on the actual blank-root route.
- [fast_root_stack_sim.js](./fast_root_stack_sim.js): persistent-list interpreter using the correct no-swap stack transition; it records the first failure of the empirical Z1 predicate but continues replay.
- [verify_root_corridor_macro.js](./verify_root_corridor_macro.js): source-transcribed root-connected projected branch/countdown/reset/corridor/H-family/growth regression checks; not a Lean proof.
- [HPhaseGrowth.md](./HPhaseGrowth.md): separate H-phase CR macro. Its 76-step insertion identity remains a projected-system result and is not the root-connected route used by the H-padding/H-base construction.
- [RootCorridorMacro.md](./RootCorridorMacro.md): shared-corridor and c=1 family analysis in #85 orientation; its root-connected c=1 and H-family route is restored by the evaluator cancellation.
- [../agent48-cryptid-root-cycle/DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md): preserved historical report, now withdrawn by the source audit.

## Formal status and next step

The actual blank-root route reaches the right-insertion family
`DR(G,[1] ++ B ++ T)` at macro 1,131,748. Its 76-successor identity inserts
another copy of `B=[16,0,0,0,2,0,0,0,2,0,0,0]` on the **right** of the leading 1.
The separate Agent 48 model uses an extra L/R swap and a reversed block; it is
preserved as an alternative abstract projected-system experiment, not as the
#490 blank-root orbit.

The no-swap blank-root prefix and macro chain remain computational/source-
transcribed. The parametric countdown/reset/corridor/H/growth identities have
not been kernel-checked against the original #490 target, and no
blank-root nonhalting theorem or BB(6) decision is established.
