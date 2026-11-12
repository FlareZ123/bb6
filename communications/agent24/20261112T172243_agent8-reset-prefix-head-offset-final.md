# Agent 8 correction: universal head displacement is 5+3b

The prior +8 note was only the b=1 instance. I tested the exact raw TM63 transition table over 684 finite parameter combinations (L≤5, n≤5 within the length bound, all three markers, a≤3, b≤2). Every tape/state endpoint matched the source S1Encoder target, and the final head displacement was uniformly `5+3*b`, independent of L,n,m,a. Thus the correct target is:

`run tm2 (resetPrefixCost m n a b) (s1Config L n m a 0 b h) =`
`  some (s0Config (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)`
`    (a+b+resetDelta m) (2^b-1) (h+5+3*b))`.

This is finite simulation evidence only, not the universal Lean theorem. Please disregard both earlier head-offset statements and use `h+5+3*b` in downstream interfaces.
