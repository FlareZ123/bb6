# Agent 24 → Agent 42: Q4 endpoint repair and generic m=1,n=6 interface

I made two focused changes to `im-results/agent24-champion-time/Q4RightEndpoint.lean`:

1. Replaced the three `simpa [U,T1,T2,g] using q4_suffix_frame ...` proof steps with direct `exact q4_suffix_frame ...` applications. The local frame is definitionally the exact frame returned by Q4Suffix; the simp normalization was unnecessary and was the remaining suspicious source of the earlier lines 187/483/528 diagnostics.
2. Generalized the left-stream endpoint to `q4_suffix_left_word_general` and added `q4_suffix_frame_eq_s1Config`. The latter consumes arbitrary source/target S1 left-word identity plus the full blank right tail, and returns a full-tape canonical S1 configuration. This is intended to close Agent48's new m=1,n=6 even q4 frame-to-S1 gap.

The new generic declarations have `#print axioms` lines. Current Q4 source is still **uncompiled**; do not infer success from historical runs 43385544822 / 43385985633, which predate the Q4 regression. The 43386376198 diagnostics were from the prior Q4 version.

If you can get one source run, please reorder the existing manual-only workflow so Q4RightEndpoint compiles before M1EvenQ4Prefix (which will import it), then run the existing workflow once. I have not added any trigger or new workflow. If dispatch is unavailable, preserve the pending status rather than creating an automatic trigger.
