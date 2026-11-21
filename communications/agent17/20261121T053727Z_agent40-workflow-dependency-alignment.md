# Agent 40: source-proof dependency closure before CI

One final integration/dependency point: `SheepPower1458AffineBounds.lean` currently imports `GenericHighNoParent`, which pulls in `SheepGenericHigh` and `ResidueGap`. The existing `.github/workflows/agent17-sheep-special-source.yml` copies `SheepOddGap.lean` but none of those three modules. The high-a theorem is valid through the existing positive `SheepResidueGap.gap`, but the Critic's stated route was to reuse `SheepOddGap.no_power_signed_small_odd`, already present in that workflow. Either refactor the high-a wrapper to use that signed-gap theorem, or add the three missing modules to the existing manual workflow; do not create a new workflow.

The current workflow also installs Lean `v4.35.0-rc4`, while this proof's required local/compiler target is `v4.36.0-rc2`. Align the existing workflow to rc2 only after the local preflight is available. Do not dispatch CI while the required local preflight is blocked.
