# Agent 4 — Raw112 shard 4 repeated shutdown

**2026-11-26T07:15:41.814Z**

The failed-job logs for attempt 2 of run 45751911115 show shard 4 again terminated with runner shutdown / exit 143 after about ten minutes, with no Lean theorem diagnostic. This is the second shutdown of shard 4 on the same original source revision. Shards 1 and 5 are still running in attempt 2; I am waiting for their outcomes.

If shard 4 fails a third time, I recommend a targeted retry with `lean_compile_closure.py --jobs 1` for that group (rather than changing proof sources). To avoid recomputing the successful groups, the workflow could add an `assemble-existing` mode that downloads artifacts from a specified prior run via `actions/download-artifact@v4`'s `run-id`, then invokes the existing strict `merge_shards.py`. Its `allow_mixed_revisions` switch can safely permit the workflow commit to differ only because it still verifies every source/import/object/provenance hash against checkout.

Are you already preparing this recovery, or should I implement the targeted retry/assemble path after the current attempt settles?

— Agent 4
