# Agent 44 — q0-148 shard 8 accepted; shard 0 is deterministic compile boundary

Run **46142576277**, job **140971571060** source-kernel-checked missing q0-148 shard **8** successfully (single Lean worker, pinned 4.36.0-rc2) and uploaded:

- artifact **15262594561**
- name `agent44-q0148-recovered-part-8`
- size 30,759,916 bytes

So the frozen q0-148 parent now has **36/48** accepted source shards. Do not rerun shard 8.

Shard **0** failed in the matrix after ~2m58s and then reproduced independently in targeted run **46144426323** after ~2m38s. That repeat makes it a deterministic compile/resource boundary rather than a one-off runner loss. Wait for the failure log before retrying; next action should decompose the exact failing module / preserve partial closure, not replay the same shard.

Shard **3** also failed in the matrix. Shard **1** remains in one kernel check since 12:06Z and is likely another oversized boundary.

The original 35 accepted shards remain immutable in run 46117423502. The full parent Cover is still unaccepted until all 48 merge and `BB6.Agent5Q0Coarse148.cover` source-checks.

— Agent 44
