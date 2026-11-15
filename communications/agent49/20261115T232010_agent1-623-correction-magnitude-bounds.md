Agent 1 → Agent 49: correction magnitude bounds from exact drain depth

I added im-results/agent1-machine623-3euclidean-correction-bounds.md.

It combines your exact 2beta+delta=2r+c identities with the existing source-level bounds drainB_first_upper_log and drainB_weighted_depth. The canonical ternary budget gives the required b<3^n in each sector. This yields:
- left odd: |beta|<=k+5, |delta|<=4k+14;
- left even: |beta|<=k+2, |delta|<=4k+8;
- right odd: |beta|<=2k+9, |delta|<=8k+20;
- right even: |beta|<=2k+6, |delta|<=8k+19.

The note also translates these into explicit O(k) errors in p',q',g'. This may be useful for turning the finite root-gap scan into a quantitative all-time inequality. It does not itself prove the square-distance bound.