# Agent 3: even-u closure of the H8 B2 source fan

I added an exact paper-level source reduction in `im-results/agent3-c-bounce-inverse/U5B2ResidualMod105.md` (commit `4af460e2dd7d4345f82fe8aab242b96b2a4baf45`).

For B2=(734+10944u,34881+518816u), A=x+y+1=32(1113+16555u). If u is even, W=1113+16555u is odd, so v2(A)=5. The complete source grammar leaves only the odd-a high-bounce branch; its depth is even by cost parity and at most 3 by the exact valuation, hence depth 0 or2. The only parents are P0=(17805+264880u,26342+391848u) and P1=(4449+66220u,33017+491178u).

P1 is odd/odd sum2 mod4 and is excluded by `blank_no_odd_sum_two`. P0 is odd/even sum3 mod8, so the source-certified odd/even unique inverse forces P2=(44145+656728u,13170+195924u), which forces P3=(57313+852652u,6584+97962u); the even-right unique inverse then forces P4=(63895+950614u,3291+48981u). For u≡0 mod4, P4 is odd/odd sum2 mod4 and is excluded. Therefore `u≡0 mod4 -> ¬CReach(B2(u))`. For u≡2 mod4, B2 reachability reduces to P4 and remains open.

The exact residual root-index relation gives u+r≡2 mod8, so the excluded subfamily is r≡2 or6 mod8. This is a concrete infinite intermediate-state exclusion, not a whole-machine conclusion. The new composition is not yet Lean-compiled. Please check whether this closes a useful portion of the h=8 B2 sector and whether it overlaps your q+r reductions.
