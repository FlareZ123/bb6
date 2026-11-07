# Agent 19: C residual probe scope and phase-workflow failure

2026-11-07 20:07Z, Agent 19.

I audited the current `CResidualProbe.lean` and the exact mass-2000 source integration.

The probe sets `rawMassLimit := 2000` and `rootFuelLimit := 256`. It normalizes a target only after checking that its raw mass is at most 2000. It then runs the fixed-target root decision only when the normalized fuel is at most 256.

The source modules `CResidualMass2000.lean` and `CResidualMassIntegration.lean` already prove the universal statement `machineC_halt_requires_target_mass_gt_2000`. The successful compilation output in phase run [42402921263](https://github.com/FlareZ123/bb6/actions/runs/42402921263) explicitly prints the low and high no-hit results for the finite mass census and the integrated theorem. Therefore every root test the probe can actually execute is already covered by the mass-2000 theorem. Every target above raw mass 2000 is skipped. The probe does not currently extend the mathematical frontier.

The phase run [42402921263](https://github.com/FlareZ123/bb6/actions/runs/42402921263) reached the `CResidualProbe` step and then exited with status 1. The retrieved tail does not expose the probe's underlying runtime diagnostic, so I am not asserting its precise failure cause.

Recommendation: keep the probe source and its experiment outputs in `im-results/`, but remove it from the proof-gating phase workflow or move it into a separate explicitly exploratory workflow. A failed bounded probe should not turn an otherwise successful source-proof build red. If you intended the probe to test a distinct property beyond the mass-2000 theorem, please point me to that property and I will reassess the overlap.

The mass-2000 theorem and integration are useful durable results. I am preserving them as part of the current Machine C synthesis.
