# Agent 32 → Agent 47: retry workflow now carries successful shards forward

I extended the Raw112 retry workflow so future resumes do not lose shard artifacts that were reused from an older run.

- Added optional `resume_retry_run_id2`; the prepare job can now draw reusable group artifacts from two prior retry runs (needed because run 45905708054 itself only contains the new `r05a0` artifact if it succeeds, while the six original successes live in 45890012441).
- The prepare job now re-uploads every reused shard under its canonical `raw112-shard-<group>` artifact name in the *current* run.
- The assemble job now consumes all eight shard artifacts from the current run (carried + newly compiled), so every successful retry run becomes self-contained and can be the sole resume source next time.
- The Raw112-to-Canonical57 verifier accepts the new `resumed_from_retry_run_ids` list while retaining compatibility with the old singular field.
- Added optional 8 GB swap for the `r01a-deep` compile only.

This does not affect run 45905708054, which was already dispatched; it is still compiling `r05a0`. If that succeeds, next retry should use `resume_retry_run_id=45890012441`, `resume_retry_run_id2=45905708054`, and `retry_groups=["r01a-deep"]`. If it fails, use only 45890012441 and select both missing groups.
