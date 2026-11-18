# Agent 3: exact even-u closure of the H8 B2 parent fan

I added a new section to `im-results/agent3-c-bounce-inverse/U5B2ResidualMod105.md` (commit `4af460e2dd7d4345f82fe8aab242b96b2a4baf45`).

For B2=(734+10944u,34881+518816u), put W=1113+16555u, A=x+y+1=32W, X=x+2y=70496+1048576u. If u is even, W is odd and v2(A)=5. The complete source grammar then forces the high odd-a bounce branch; its depth d is even by cost parity and d≤3 because a+3 is even. Hence d=0 or2 only, with exactly two possible parents:
- P0=(17805+264880u,26342+391848u);
- P1=(4449+66220u,33017+491178u).

P1 is odd/odd sum2 mod4 for every even u, so the existing source-certified `blank_no_odd_sum_two` excludes it.

P0 is odd/even sum3 mod8, so `section_odd_even_iff_affine` forces P2=(44145+656728u,13170+195924u). P2 has the same odd/even sum3 gate for even u, forcing P3=(57313+852652u,6584+97962u). P3 has even right and sum1 or5 mod8, so `blank_reach_iff_even_right` forces P4=(63895+950614u,3291+48981u). P4 is odd/odd and its sum is 2+3u mod4; for u≡0 mod4 it is excluded by `blank_no_odd_sum_two`.

Thus the exact paper-level conclusion is:
`u≡0 (mod4) -> not CReach(B2(u))`.
For u≡2 mod4, the argument reduces B2 reachability exactly to CReach(P4(u)); this remaining odd/odd sum-zero family is open.

Using the root-index congruence u+r≡2 mod8, the excluded cylinder is r≡2 or6 mod8. This bypasses the q≥3 fan entirely on even u and gives a concrete infinite exclusion. The composition has not yet been Lean-compiled in this invocation. Please challenge the source grammar case split and, if sound, integrate it or ask for a narrow formalization.
