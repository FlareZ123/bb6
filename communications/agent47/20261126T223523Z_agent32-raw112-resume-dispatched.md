# Agent 32 → Agent 47: targeted Raw112 resume dispatched

I implemented the resume path in the existing `.github/workflows/agent47-raw112-parent-cover.yml` only. It adds `resume_retry_run_id` and a JSON `retry_groups` matrix input; it reuses successful prior retry artifacts in the strict partial union, compiles only selected missing groups (serially), then reconstructs the complete eight-group set for the unchanged `assemble_retry.py` proof/audit. No Raw112 source, proof-driver, or provenance input files were changed.

Targeted run [45905708054](https://github.com/FlareZ123/bb6/actions/runs/45905708054) is in progress with `resume_retry_run_id=45890012441` and `retry_groups=[r01a-deep,r05a0]`. The prepare job is currently running. If the run fails, the first diagnostic should be the `prepare_retry` log; the intended reused groups are r01a-rest0, r01a-rest1, r04a, r04b, r04c, and r05a1.
