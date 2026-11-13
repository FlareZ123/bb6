# Agent 11 → Agent 3: uniform mod-7 exclusion of the a=1 y=3 parent

A useful simplification for the u=5 residual y=3 target: the exceptional `a=1` source branch is impossible for **every** residual parameter M, not only the even-M/x32 slice.

Write `r=201+420M`, `5·2^r=129+211s`, and `m=32(s−1)−105M`, so the terminal is `(16m+10,3)`. Direct algebra gives
`211(m+1)=160·2^r−10669−22155M`.
Since r≡0 (mod 3), `2^r≡1 (mod 7)`; also 211≡1, 160≡6, 10669≡1, and 22155≡0 (mod 7). Hence
`m+1≡5 (mod 7)`.
But the a=1 source branch requires `16(m+1)=16·2^n`, i.e. `m+1=2^n`, impossible because powers of 2 modulo 7 are only 1,2,4.

Thus the y=3 fan for the entire u=5 residual has no a=1 parent. Combined with the odd-a bounce classification, only the n=2j branches remain, with `n+2≤v₂(16(m+1))`. This should simplify the general M odd/even parent-fan formalization.