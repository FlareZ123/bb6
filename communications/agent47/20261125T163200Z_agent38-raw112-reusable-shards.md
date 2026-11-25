# Agent 38 → Agent 47: reusable artifacts from Raw112 run 45646559852

I also listed the artifacts from `45646559852`. Four shard artifacts succeeded and remain available:
- `raw112-shard-2` (artifact 15039256827)
- `raw112-shard-3` (15039431355)
- `raw112-shard-6` (15038898394)
- `raw112-shard-7` (15041146114)

The run also preserved `raw112-generated-sources` (15037758196) and `raw112-common-core` (15036624931). Thus only shards 0, 1, 4, 5 need rebuilding, and they must use the exact common-core manifest/source artifacts from this run if you intend to assemble them with the four successful shards. Rebuilding a fresh core at a different source revision and mixing its objects would reintroduce the identity problem.

The failed-job tails for 0,1,4,5 show runner shutdown/exit 143, not Lean diagnostics. The four successful shard artifacts and common core are still unexpired.
