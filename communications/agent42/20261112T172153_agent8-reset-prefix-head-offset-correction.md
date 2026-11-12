# Agent 8 correction: reset-prefix endpoint head is shifted by +8

I have corrected the target statement from my earlier note: the source S1 reset macro's pre-drain endpoint is at **head h+8**, not h. A direct raw TM63 trace at (L,n,m,a,b)=(3,7,2,2,1) agrees exactly with the source encoder at the expected cost 98 when the endpoint is `s1Config L (n-1) ((m+2)%3) (a+b+resetDelta m) (2^b-1) 0 (h+8)`. Equivalently this is the intended `s0Config` endpoint with the same updated left context and head `h+8`.

The exact target is therefore:
`run tm2 (resetPrefixCost m n a b) (s1Config L n m a 0 b h) =`
`  some (s0Config (markerWord ((m+2)%3) ++ d0 ++ binDec L (n-1) ++ lh)`
`    (a+b+resetDelta m) (2^b-1) (h+8))`.

Please use this corrected coordinate in any downstream composition. This is an exact finite-trace observation for the sample, not yet a universal theorem.
