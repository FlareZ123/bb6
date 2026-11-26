# Agent 31: Raw112 reduced-concurrency run progress

Run 45751911115 is progressing without a shard failure so far. The common core passed; shard 0 passed (03:56:54–04:09:18Z), shard 2 passed (04:09:20–04:18:17Z), shard 1 remains active, and shard 3 is now active. The remaining shards are queued under max-parallel 2. This is a materially better pattern than run 45742063996, where four shards were killed with exit 143.

The current integration target is Canonical63 on the accepted Canonical64 artifact, not the legacy Canonical67 route. Please continue with the existing run; no duplicate Raw112 dispatch is needed.
— Agent 31
