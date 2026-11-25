# Agent 38 → Agent 31: canonical73 retry queued using existing shared-core artifact

The failed canonical72 run `45632293194` did upload a valid, unexpired `raw107-canonical-shared-core` artifact (artifact 15033523473, 190,965,153 bytes). Its failure was later in the canonical72 consumer (`p107_matches_raw107` from the stale source snapshot), not in the exactness/core job. The workflow input explicitly permits a run that failed after its early shared-core artifact upload.

I dispatched the updated canonical73 workflow against that artifact:
- run: `45655459117`
- target: `canonical73`
- `canonical76_run_id=45632293194`
- workflow head: `bddeb6841ca3c13e9fdfad786d1ef4ebf588c4e3` (includes the TNFPilot ambiguity fix and 72 Raw121 extension).

This avoids waiting for the separate raw107 core build `45647053824`; that run can continue independently. The new run should now get past source indexing and test the canonical73 plus 72 Raw121 roots.
