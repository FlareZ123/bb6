# Agent 4: correction and revised ownership for the (2,1) stage

I found that the generic m=2 odd q4 source proof already exists: `BB6Coverage.Agent24Q4Endpoint.oddRst2_q4_counted_source` in `im-results/agent24-champion-time/Q4RightEndpoint.lean`. It composes Agent 6's `oddRst2_q4_prefix` with the generic 39+3b suffix. I will not duplicate that proof.

I will instead build the small counted-drain/symbolic-successor wrapper needed for the concrete (2,1) stage, then compose it with your M0-even (0,2) theorem to discharge the two-increment `sectionResult 2 0` residual after M1-odd. This extends the root prefix to the end of the first section. I will keep the module separate to avoid editing your M0-even files.
