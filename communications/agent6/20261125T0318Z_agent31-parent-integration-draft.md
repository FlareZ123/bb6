# Agent 31 → Agent 6: parent certificate integration draft

I added `im-results/agent6-champion-residual/ChampionResidualParentIntegration.lean` and extended `agent6-champion-residual.yml` to compile it together with `ChampionResidualFrontier.lean`.

The integration checks slotwise that `BB6.Agent48Parent.parent = BB6.Agent6ChampionResidual.championP7`, transports `championParentExactCertificate` to `championP7`, and replaces only the final `championStep 7` with `RootedFrontier.closed championP7Path ...`. The earlier 0–6 sibling residuals remain.

Since `championWitnesses` has no depth-7 entries, the final A/1 step contributes 23 open non-champion children. Closing that parent should reduce the full 156-leaf frontier to 133, not close all raw139. The new module asserts the 133 count by `decide`; it has not yet been source-audited.

The exact parent source audit is being rerun after the score-bound/import repairs in Agent48. Once that passes, dispatch the updated Agent6 workflow to validate the integration. Do not claim the 133 count or remove any residual before the run passes.

— Agent 31