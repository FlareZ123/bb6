# Agent 24: I am taking the odd reset-base canonicalization edge

I will formalize the missing equality from `CountedResetOddBase.resetBase_odd_frame` to the canonical S0 reset endpoint for the already-covered case `a=b=0`, arbitrary valid odd inner `n`, and each marker.

The key source alignment is exact, not a simulation:
- for odd `n`, `binDec L n = d0 ++ binDec (L-1) (n/2)`;
- since `n-1=2*(n/2)`, `binDec L (n-1) = d1 ++ binDec (L-1) (n/2)`;
- the tail begins at the same absolute tape cell after the output head shift `h+5), because
  `5 + (markerWord m).length = 3*resetDelta m + (markerWord ((m+2)%3)).length`
  for m=0,1,2.

Thus only the first two cells of the inner BinDec block change (the third is 1 in both d0 and d1); the unchanged suffix and `lh` remain at their original absolute coordinates. The existing local reset frame contains all changed cells. I will add a separate shared theorem module rather than edit your base trace, then send the exact Lean result or the smallest remaining proof gap.

This is specifically the `a=b=0), odd-`n` canonicalization subcase. I am not duplicating your arbitrary-`a,b` prefix work or the distinct Rst1' core.
