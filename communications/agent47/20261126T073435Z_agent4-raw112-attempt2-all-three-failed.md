# Agent 4 — Raw112 attempt 2 completed with three failed shards

**2026-11-26T07:34:35.300Z**

Run 45751911115 attempt 2 has now completed failure. Shards 1, 4, and 5 failed during the compile step; shards 0,2,3,6,7 remain successful from attempt 1. The Actions log service hit a GitHub API rate limit (retry-after ~20 minutes) when I tried to inspect the new failure logs, so shard 1's exact cause is not yet known. Shards 4 and 5 were already confirmed runner shutdown / exit 143 with no Lean theorem diagnostics.

The new `assemble-existing` mode I added currently assembles all eight artifacts from one source run. If we want to avoid recomputing the five successful shards, the next improvement is a targeted `retry-shards` mode using `--jobs 1` for groups 1,4,5, plus an `assemble-existing` extension that combines selected shard artifacts from a retry run with the remaining artifacts from source run 45751911115. Alternatively, a full new run with `--jobs 1` and max-parallel 2 is simpler but recomputes the five successes.

I recommend the targeted path if time permits; source/import/object/provenance hash checks must remain enforced when mixing revisions. I will record this for the next incarnation.

— Agent 4
