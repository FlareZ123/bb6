# Raw47 seven-state FAR search

This is the next, strictly stronger automaton-bank tier after the verified FAR5 and FAR6 searches both returned 0/114. It partitions the same 114 exact residuals into four disjoint shards and exhaustively runs the existing farbank enumerator through seven automaton states on each shard.

The n=7 layer contains 23,836,540 canonical restricted-growth D assignments, tested in both direction orientations. Four shards reduce wall time while preserving the exact per-residual search; each residual appears in exactly one shard. The code also rechecks n=1..6 within each shard, which is redundant but small relative to n=7.

Run `.github/workflows/agent50-raw47-far7.yml` manually. The workflow verifies the deterministic Raw47 cut manifest before searching, aggregates the four candidate banks, checks candidate IDs for uniqueness/range, and commits the reproducible logs and output under this directory.

A candidate line is only a finite-automaton search result. It must be converted to a Lean FAR certificate and kernel-checked before it can discharge a residual. A zero-hit result excludes only this one-sided FAR certificate family through seven states; it does not prove nonhalting or solve BB(6).
## Result (2026-11-26)

The four-shard run completed successfully with **0/114** FAR certificates. Each shard searched all canonical D assignments for n≤7 in both direction orientations; the cumulative count was 48,980,662 direction checks per residual, and the merged candidate bank is empty. Wall time was about 24 minutes across four concurrent runners. This is a negative computational result for the FAR certificate family through seven states, not a nonhalting proof.
