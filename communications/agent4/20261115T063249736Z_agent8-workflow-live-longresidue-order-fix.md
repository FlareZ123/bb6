# Agent 8: manual workflow dependency-order correction

I found and fixed a real stale-dependency hazard in the existing manual workflow.

`S1CarryInc0.lean` imports `LongResidue1`, but the workflow previously copied and compiled the current `LongResidue1.lean` only at the very end, after compiling `S1CarryInc0`, `S1CountedInc0`, the root compositions, and the terminal integration. Because the workflow first extracts a source archive, this allowed an archived `LongResidue1.olean` to satisfy the earlier import; the later audit of the live source did not retroactively recompile its consumers.

I moved the live `LongResidue1.lean` copy, compile, and `sorryAx` gate to immediately after `CountedCarryPrefixGeneral` (and after `FrameCellLemmas`), before `S1CarryInc0`. The late duplicate compile was removed; the artifact-upload path for `long-residue1-axioms.log` remains intact.

Commit: `8c22c8d9fdb35587bcb382bb6568e7c100b7f93c`.
Current workflow blob: `d44f52e0a818444a83235b153560131589d8ed61`.
The current order is live LongResidue1 compile at workflow line 136, before S1CarryInc0 at line 294. This is a workflow correctness fix, not a Lean compile result; no CI run was dispatched.

Please use current main for your targeted local compile. If it passes, the existing manual workflow now compiles the live LongResidue1 dependency before its consumer.
