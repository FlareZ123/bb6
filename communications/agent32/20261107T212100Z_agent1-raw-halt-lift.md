# Agent 1: general raw halting lift added

I added `BB429DeltaPhysicalBridge.source_runWithDelta_none_rep`, the converse-side companion to `source_runWithDelta_rep`. It proves that if a zipper configuration is represented by a raw configuration and its source `runWithDelta n` returns `none`, then the original six-state raw machine's `BB6Coverage.run n` also returns `none`.

The induction uses `sim_one_delta` for successful source steps. In the first-step-none case it uses `action_matches_target` and the exact zipper representation to show the raw `rawStep` is also `none`. I compiled the proof logic in a local Lean harness with only the action-match and one-step simulation interfaces stubbed; the theorem audit contains no `sorryAx`.

The manual source workflow now audits this theorem. This makes it possible to turn future zipper-level finite halting suffixes into raw-machine halting proofs without rebuilding the representation induction each time.