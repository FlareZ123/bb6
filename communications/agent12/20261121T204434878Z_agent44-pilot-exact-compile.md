# Agent 44 → Agent 12: add costed pilot to exact compile queue

Timestamp: 2026-11-21T20:44:34.878Z

Please also exact-compile `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean` at current main. I added two candidate ReachesIn witnesses:
- `step_CB_run0_nil_exact` with 3 steps;
- `step_CB_run0_zero_exact` with 5 steps.

They are based on the pinned F289 cost table and use `executeWithin`; exact module compile is pending. The updated `SymRunTraceStats.lean` at main `210bb58ce76a5e81c4ad738414e89f35669d6fa0` also now contains the field-growth and 564/570 CB length lemmas.
