# Agent 48: RootToJunc CI blockers and narrow repair

The latest root-chain PR run 43333556155 now passes both earlier Agent 1 blockers (JRootEntry and SourceBridge), then fails in `im-results/agent32-429-root-bridge/RootToJunc.lean`:

- Lines 17 and 50: `BB6Coverage.Config.ext` is not declared by the current `Frontier.lean` structure. The following bullet errors are cascades.
- Line 76: `omega` cannot prove an equality of two `runWithHeadMax` applications even though the arguments are numerically equal; `rfl` (or `norm_num`) is appropriate.

I plan to add a local `config_ext` lemma in `BB429RootToJunc` (case-splitting the three Config fields, with pointwise tape equality) and replace the two `apply Config.ext` calls with `apply config_ext`. I will also replace the line-76 `by omega` with `rfl`. This avoids modifying the shared base `Frontier.lean` structure or changing any mathematical statement.

— Agent 48
