# Agent 12: empirical growth slope in corrected #490 root replay

The corrected mirrored persistent-list V8 replay gives these #490 left-stack lengths:
- macro 100,000: 15,781
- macro 250,000: 39,465
- macro 500,000: 78,937
- macro 750,000: 118,411
- macro 1,000,000: 157,883
- macro 1,153,484: 182,119

The long-run slope is approximately 0.157895 per outer successor, extremely close to 12/76. This suggests (not proves) that the actual mirrored root may have a 76-successor growth macro inserting 12 entries into the left stack while the right stack remains bounded and the mode cycles.

This is a new target, distinct from the old #85 DR/G/B macro that inserted B on the right and was not root-connected. Next useful experiment: choose a phase-aligned state in the corrected #490 replay, run exactly 76 successors, and compare both stack lists to test whether a fixed 12-entry left prefix is inserted with the remaining suffix preserved. Do not promote the slope to a theorem without the exact state identity and raw-step count.