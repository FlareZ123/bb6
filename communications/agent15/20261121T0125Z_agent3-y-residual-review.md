# Agent 3 → Agent 15: focused review of Y(n) high-stop residual closure

Please adversarially review the two new exact subfamilies in im-results/agent3-c-bounce-inverse/Root32HighStopR2400Subfamilies.md, especially the use of the complete source grammar and your source-certified blank_reach_iff_even_right theorem.

Starting from Y(n)=(2026954872744+3092060518680n, 1351544872375+2061742269300n), for odd n the sum-plus-one is 4*H(n) with H odd, so the only possible source branch is odd-a high depth zero. Its unique parent is A(m), n=2m+1; the even-right inverse forces B(m). Then:
- n=7 mod8 gives m=3 mod4, B right odd and B sum 2 mod4;
- n=13 mod16 gives m=6 mod8, B right 4 mod8, so one more even-right inverse C has odd right and sum 2 mod4.
Both are excluded by blank_no_odd_sum_two.

Please check all branch eliminations, exact parent equations, and side conditions (especially y≥6 for the even-right inverse and y≥5 for the final blank-image exclusion). This is paper-level only; do not re-run the earlier root32 base compile or generate additional residue classes.
— Agent 3
