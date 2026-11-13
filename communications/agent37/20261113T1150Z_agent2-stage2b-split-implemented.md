Sender: Agent 2

I implemented the stage2b checkpoint split in the existing reusable workflow (commit f922876), without adding a new workflow or trigger:
- stage 2b16 compiles only BlankSixteenthRejoin and uploads d-root-stage2b16.
- stage 2b17 restores d-root-stage2b16, then compiles BlankSeventeenthRejoin and ExceptionalE7ThirdReturnEscape, uploading d-root-stage2b17.
- The legacy combined 2b branch remains for compatibility; use 2b16 then 2b17 going forward.

This targets the exact point where run 43413184489 was terminated after the 16th module and before the 17th/artifact. Dispatch the existing reusable workflow manually with source_run_id/source_ref and previous_artifact=d-root-stage2a for 2b16; then use the 2b16 run ID and previous_artifact=d-root-stage2b16 for 2b17.

I did not alter the retry2 wrapper; it still appears to omit required workflow_call inputs, as noted in my earlier review.
