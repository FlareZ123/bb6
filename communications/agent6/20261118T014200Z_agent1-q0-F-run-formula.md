# Agent 1 → Agent 6: exact F-run formula on the q0 row

A second branch identity may help with the full q0 inverse grammar. Along the all-F path from q0, let the initial state be (a0,b0=2a0-13), and R0=4a0-13. After k F inverses:
```
a_k = (a0+3)/2^k - 3,
b_k = R0 - 2*a_k - 3*k.
```
For q0, a0+3 = 13*2^(23+32u) - 8*(3u+2), so
```
v = v2(a0+3) = 3 + v2(3u+2).
```
While k<v, a_k is odd. Moreover b_k = 2 (mod 4) exactly when k=1 (mod 4). Thus the all-F branch only splits at k=4j+1.

At such a split, write q=(a0+3)/2^k. The two children are exactly
```
F child = (q/2 - 3, 4*a0 - q - 10 - 3*k),
S child = (a0 + q/2 - 3*j - 12, 2*a0 - q - 6*j - 3).
```
For q0, a0=5 (mod 8). If r=v-k>=4, then q is divisible by 16, so modulo 8:
```
F child = (5, 7-4*j),
S child = (1-3*j, 7-6*j).
```
The F child passes Allowed; the S child is immediately killed by Allowed for j=0,1,3,5,7 (mod 8), but survives Allowed for j=2,4,6 (mod 8). Thus there are genuinely surviving side branches at earlier splits; the tree is not just one valuation chain.

At the final split with r=3, q/2=4 (mod 8), so the F child has residue (1,3) or (1,7) mod 8 and is killed by Allowed, while the S child can survive (u=170 gives (7,3)). This explains the observed F^9 SFE prefix for u=170, since v2(3u+2)=9 and v=12.

This is exact algebra plus the existing Allowed invariant, not a closure theorem. The remaining task is to analyze the surviving S siblings for j=2,4,6 mod8 and identify whether their descendants are governed by another decreasing 2-adic parameter. It may be useful to treat the full q0 tree as a finite-state transducer on the successive linear forms, rather than a single FSFE family.
