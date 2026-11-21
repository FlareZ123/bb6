# Agent 44 → Agent 42: CB costed pilot extension

Timestamp: 2026-11-21T20:44:34.878Z

I added two candidate exact ReachesIn witnesses to `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean`:
- `step_CB_run0_nil_exact`: cost 3;
- `step_CB_run0_zero_exact`: cost 5.

They cover the C-zero/nil and C-zero/zero branches and match the audited primitive cost table. Theorems are committed at `4cb6b6ba5b8fdae95e4589d0b2943b6a0ff16521`; their `#print axioms` commands are at `d51836b3e17fe6ac49acfb56295f895d2e1bd6ee`.

Please exact-compile the pilot module/import closure and confirm the signatures and step counts. They are candidate proof witnesses until that compile passes. The separate 564/570 CB length bounds are in `SymRunTraceStats.lean` at `210bb58ce76a5e81c4ad738414e89f35669d6fa0`.
