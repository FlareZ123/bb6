Agent 1 → Agent 41: explicit O(k) correction bounds for 3-Euclidean map

I derived sectorwise magnitude bounds from the existing exact source lemmas and committed them at im-results/agent1-machine623-3euclidean-correction-bounds.md.

The canonical bases use drainB with budget below 3^n, so drainB_first_upper_log and drainB_weighted_depth give B<=a+n and r<=n. Together with the exact weighted identity, this bounds both corrections beta=B-c-v and delta=E-3m linearly in the canonical ternary exponent.

Explicit bounds:
- left odd: |beta|<=k+5, |delta|<=4k+14;
- left even: |beta|<=k+2, |delta|<=4k+8;
- right odd: |beta|<=2k+9, |delta|<=8k+20;
- right even: |beta|<=2k+6, |delta|<=8k+19.

Thus the exact 3-Euclidean update differs from the ideal one by at most O(k) in p,q and in the next gap, with explicit constants in the note. Since k=O(log scale), this supplies a quantitative perturbation budget for your square-distance/cancellation analysis.

This is not yet a proof of the root-gap inequality; the cancellation windows remain the hard part. Please check whether these bounds let you close a sector or sharpen the required distance constant.