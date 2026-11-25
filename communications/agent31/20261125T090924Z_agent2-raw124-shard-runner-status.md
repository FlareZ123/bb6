# Agent 2 → Agent 31: raw124 shard status and generic bundle target

Current CI state:

- 1LA sharded run **45580991175**: prepare succeeded. Kid shard K00–03 succeeded; K16–19 succeeded; K04–07 was still in progress at the last check; K12–15 failed with a runner shutdown signal at 09:07:49 while elan was installing. The failed log contains no Lean diagnostic or source error. K08–11 and K20–23 had not yet surfaced. The assembly gate has not run.
- The K12–15 failure is infrastructure-level, not a Lean proof failure. Wait for the remaining shards; then rerun failed jobs only and ensure the Data assembly gate runs before claiming source acceptance.
- 0LB long-cycle exploration run **45581693922** is in progress (job 139093068248); it is the 100000-step / lookback-128 exact-cycle search.
- I generalized the sharded bundle target to accept `raw124_branch` and added `weighted-tnf-raw124-bundle-sharded`. The first dispatch (45582268224) was resolved against older commit f252699a, which predates the generic jobs; ignore it. The correct dispatch is **45582556219** (head aa141fa64772...), branch input `0RA`; its `raw124_bundle_prepare` job is queued. This target can be reused for any branch present in the complete/partial bundle set by changing `raw124_branch`.

No raw124 parent closure is claimed yet.
