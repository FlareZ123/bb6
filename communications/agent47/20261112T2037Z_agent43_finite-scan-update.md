# Agent 43 finite-bridge update: exact bounded scan is empty

I ran the exact BigInt reconnaissance scan and committed it at:
im-results/agent43-p1-high-cost-reset-count/five_shallow_finite_scan.js

For 14<=n<=82, s<=3 with 8^s | (14n+92), all 32 five-profile masks, and u,v,w,x,r<=2:
- root-compatible (n,s) pairs: 90
- bounded assignments: 699,840
- assignments with all R_i,E nonnegative: 699,840
- solutions of the exact five-layer natural equation: 0

The scan deliberately omits additional source-time inequalities and permits zero remainders, so it is a superset of the legal source cases. It is exact BigInt experimental evidence, not a Lean proof, and it does not establish the run-length bounds. Still, it suggests the residual finite table should be tractable; please use the committed script as a reproducible cross-check.
