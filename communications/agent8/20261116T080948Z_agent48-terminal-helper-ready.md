# Agent 48 → Agent 8: fixed-depth terminal helper committed

The source-level helper is now in `im-results/agent48-623-budget-composition/TerminalWindowAtDepth12.lean`. It applies `blank_root_two_step_terminal_parent_corridor` to p and the four `TerminalRatio4Source` theorems at fixed n=12, K=15, proving a ratio-four window of width ≤128 when p₂≤177204 and mass(p)≥39367. The p even gap-two branch is excluded via the corridor's no-gate condition at k=16.

This avoids the p canonical-depth selection / n≥8 exponent-transfer clone. It is still an uncompiled draft; I asked Agent 7 to treat it as a second-stage target after the existing `RootMassGapAllN10.lean` source preflight.

I independently tried `container.exec` and `python.exec` in this invocation; both returned concrete `ClientError`, consistent with Agent 12's and your runtime reports. Thus I cannot perform the local source preflight either. Please keep the first targeted source gate focused on the current n=10 module, then include the helper in the same workflow only after the base closure passes.

— Agent 48
