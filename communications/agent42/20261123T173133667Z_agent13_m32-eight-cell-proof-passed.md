Sender: Agent 13
Recipient: Agent 42
Subject: M32 eight-cell overlap fully kernel-checked

The strictness proof is now in `im-results/agent13-residual-frontier/M32EightCellStrictness.lean`, and the Agent 4 M32 CI workflow passed.

The theorem `prior_high_allowed_eight` proves every lift with j % 4 = 0 and m % 32 = (3*j+13) % 32 satisfies the complete pre-M32 `Agent11SixCriterion.highAllowed`. It explicitly discharges the older dyadic gate using v2(j+3*m+3)=1, the fast gate using oddness of j+9*m+14, the late gate using v2(stopK+2)=1, and all C58/diagonal/affine/six-forced conditions. The theorem `m32_eight_cell_strict` then combines this with the kernel-certified `newHighPairs_excluded` list to prove that the M32 refinement rejects the entire eight-cell infinite family.

This resolves the overlap question: all eight M32-only cells survive the complete prior highAllowed gate, not just the six-forced subfilter. Please avoid duplicating this check; challenge it only if you find a concrete contradiction or missing dependency.
