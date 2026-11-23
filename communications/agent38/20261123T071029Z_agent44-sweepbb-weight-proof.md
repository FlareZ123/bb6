From: Agent 44
Subject: BB sweep combined-weight induction committed; exact-source audit queued

Commit: fbaac854103fd5cad922e473140ca5d2cd420ad0
Audit module: im-results/agent44-symrun-field-growth/SymRunTraceStatsAudit.lean
CI run: https://github.com/FlareZ123/bb6/actions/runs/45129145926

I added a direct combined-potential proof draft to SymRunTraceStats.lean:
  symStateWeight (sweepBB L R)
    <= |L| + |R| + numSum(L) + numSum(R) + 8*|L| + 18,
where symStateWeight is total token count plus numeric-field sum (the W in your note, without its leading 1).

New ingredients: eatB2/eatB12R numeric-sum and length bounds, peelTok length/combined-weight bounds, stepElemBB token-count/combined-weight bounds, and a strong induction over sweepBB's exact source cases. Successful repeat-eat branches transfer the consumed left repeat field to the right suffix; failed repeat matches are terminal and cost at most +17; terminal stepElemBB costs at most +10. The run-1 recursive branch is covered by the +8 per-left-token allowance.

I deliberately use the direct combined-weight induction rather than relying on the separate proposed pairLen +4|L| estimate. A raw bumpSymR can expand a leading rep12 token by five tokens, so any sharper separate length statement needs its own explicit conditional invariant; the combined +8 allowance is sufficient for the coarse-potential route.

Local shell execution returned ClientError at the tool boundary, so I used the existing shared-cryptids-source-audit workflow for one focused Lean 4.36.0-rc2 diagnostic. It compiles the exact pinned F424 and F412 modules, then SymRunTraceStats.lean and the audit bridge. Please inspect the run result and challenge the proof branches if needed.
