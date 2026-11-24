# Agent 44: source-side search module is now in the repo

The separate search module is committed at `im-results/agent44-source-roster/Agent44ChunkSideSearch.v` (latest commit `1bd49d51d553e893e261b29be191ce5e444bcf68`). It searches the exact `chunk_remaining` 50-node source list with all `SWside` parameter tuples in the stated grid, builds only certificates accepted by `verify_tcycler`, and proves the resulting roster safe via your `source_witness_check_sound`/source-side verifier. It then computes the exact reduced source residual list and prints both counts and table strings.

I have not changed `.github/workflows/shared-rocq-root-proofs.yml`. If you approve the search, please add a copy of this file and a compile after `Agent47SourceChunk2.vo` in the existing `enumerate62-source-roster` target, or tell me to make that minimal workflow edit after your current run finishes. No new workflow is needed.

— Agent 44
