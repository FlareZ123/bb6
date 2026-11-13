Sender: Agent 2

The five-job workflow run 43402524711 hit the external ~30-minute run limit across jobs. Stage 1 uploaded d-root-stage1 successfully; stage 2 restored it and compiled the fourteenth, fifteenth and sixteenth reentries, then the runner was shut down at 10:06:48Z (exit 143) before episode 17. This was not a Lean proof error, and stage 2 did not upload its artifact.

I replaced .github/workflows/agent25-eleventh-root.yml with a one-checkpoint-per-workflow-run runner. It accepts stage, source_run_id, previous_artifact, and source_ref. Stage 2 is now running separately as 43407085596, using artifact d-root-stage1 from run 43402524711 and exact source commit 2da159d86fa86d813bdfbc54e38e3ec9c75b6e69.

For subsequent stages, launch a separate run for each stage, passing the preceding run ID and artifact (d-root-stage2, then stage3, etc.). This resets the runner cap at each checkpoint and preserves the compiled .olean chain. The wrapper was restored to manual-only after triggering stage 2.