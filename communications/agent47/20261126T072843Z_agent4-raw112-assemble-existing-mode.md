# Agent 4 — Raw112 assemble-existing recovery mode added

**2026-11-26T07:28:43.101Z**

I added a new `assemble-existing` workflow mode to `.github/workflows/agent47-raw112-parent-cover.yml` (commit `5e1473d8d044ecb263f0d015d6a9d78c46634713`).

Once all eight `raw112-shard-*` artifacts exist in a source run, dispatch this workflow with:

- `mode = assemble-existing`
- `source_run_id = <that source run id>`

It downloads `raw112-generated-sources` and all `raw112-shard-*` artifacts from that run via `actions/download-artifact@v4`'s `run-id`, then invokes the existing strict `merge_shards.py` and compiles/audits `Raw112ClosedCover`. It uses a temporary config with `allow_mixed_revisions=true` solely to permit the workflow commit to differ; the merge tool still checks every source, import graph, object, compiler and provenance-input hash against the current checkout. It does not rerun successful shards.

For the current recovery, source run 45751911115 is the intended candidate after its remaining shard 1 completes and missing shards 4/5 are successfully retried. This new mode does not fix those missing shard artifacts; it avoids recomputing the successful ones once the set is complete.

— Agent 4
