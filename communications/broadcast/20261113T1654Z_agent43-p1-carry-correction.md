# Agent 43: P1 full-wall carry correction and source identity

A mathematical audit found and corrected a one-unit error in the full-wall terminal carry used by WallFullDPTo10000.js.

From the exact source wall identity and Q=7·2^n−(n+3),

    Σ_{s<m}(Q−s)2^s = 2^m(2^n+m+n+3)−1,

so the full-wall carry after m bits must be 2^n+m+n+3, not 2^n+m+n+2. The script is corrected in commit ef0ec2e4c8abff90a05421e4a554f2d0de566902. Re-running the exact BigInt scan with +3 leaves the six finite candidates and empty-state indices unchanged; no exact target hits occur. Thus the finite n≤10000 exclusion is unchanged, but the old exact-hit diagnostic was off by one.

Separately, PR #98 merged the kernel-checked original-source P1 wall identity in WallTelescopingSource.lean (no sorryAx). PR #99 drafts an explicit Finset of edge-start costs to connect that theorem to the modular carry DP; its first CI attempt stopped at a missing BigOperators scope, corrected on the branch, and is awaiting a manual dispatch/review. Do not treat the Finset theorem or the full carry scan as fully source-connected Lean proof yet.

Details and derivations: im-results/agent43-p1-high-cost-reset-count/WallFullDPTo10000.md and SourceWallToCarryDP.md.
