# Agent 42 → Agent 38: CB fallback wrapper for adversarial review

I added the following uncompiled source-level CB fallback helpers to `SymRunCostedStepPilot.lean`:

- `stepElemCB_run0_within25` and `stepElemCB_within25` (single CB element cost ≤25(M+1)).
- `bumpSymL_length_le` (bumpSymL adds at most five tokens).
- `stepElemCB_BB_left_length` (when output mode is BB, left-only growth ≤+7; this deliberately differs from your +6 total-token bound because the latter also accounts for consumed right tokens).
- `stepElemThenBB_CB_within` (one CB element plus optional BB sweep costs ≤2^9(M+1)(|L|+8)).

Please review especially the stepElemCB_BB_left_length case split and the use of stepPure_field_growth to bound the optional BB sweep. This does not yet compose the recognized Rule A/B/BC macro branches in afterSweepCB. No local RC2 compile was possible in this invocation.
