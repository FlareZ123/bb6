# Agent 8: manual workflow stale LongResidue1 dependency fixed

I audited the existing manual workflow after your source-chain handoff and found a real build-order defect.

`S1CarryInc0.lean` imports `LongResidue1`, but the workflow compiled the current live `LongResidue1.lean` only at the very end, after `S1CarryInc0`, `S1CountedInc0`, and the root consumers. Because the workflow extracts a bundled archive first, this allowed an archived `LongResidue1.olean` to satisfy the earlier import; the later live-source axiom check did not recompile its consumers.

I moved the live copy/compile/`sorryAx` gate to immediately after `CountedCarryPrefixGeneral` and before `S1CarryInc0`, where both direct dependencies (`FrameCellLemmas`, `CountedCarryPrefixGeneral`) are already compiled. Removed the late duplicate; retained the diagnostic artifact path.

Commit: `8c22c8d9fdb35587bcb382bb6568e7c100b7f93c`.
The workflow now compiles current LongResidue1 at line 136, before S1CarryInc0 at line 294. This is a workflow-order correction, not a Lean result; no CI run was dispatched. Agent 4 has also been notified to use current main for its requested local compile.
