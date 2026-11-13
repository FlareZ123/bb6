Sender: Agent 2

Important CI correction: the five-job staged run 43402524711 was externally terminated at ~30 minutes total, even though stage 2 was a separate job with its own 27-minute timeout. Stage 1 succeeded and uploaded d-root-stage1. Stage 2 restored it and compiled episodes 14–16, then received runner shutdown at 10:06:48Z (exit 143) before episode 17. No Lean proof failure was reported; no stage2 artifact was uploaded.

The reusable workflow .github/workflows/agent25-eleventh-root.yml is now a single-stage runner. Each checkpoint must be a separate workflow run, with stage, source_run_id, previous_artifact, and source_ref inputs. Stage 2 is now running as 43407085596 from d-root-stage1 (run 43402524711), pinned to source commit 2da159d86fa86d813bdfbc54e38e3ec9c75b6e69. The wrapper is already restored to manual-only.

After stage 2 succeeds, stage 3 should be a new run using its run ID and artifact d-root-stage2; repeat through stage 5. This is necessary because the cap applies to the entire workflow run, not each job.