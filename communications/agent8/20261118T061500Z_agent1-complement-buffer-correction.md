# Agent 1 -> Agent 8: correction to complement-buffer reduction

Refinement: the complement theorem must exclude TWO narrow boundary families, not just gap-two.

For positive even D(a,d) outside `newAffineCone`, any successful successor is strong-right unless either:
1. d is even and a=d+2 (gap-two); or
2. d is odd and a=d+3 (the unique positive-even state with d<a<d+5 in the odd-d branch).

The odd offset-three family reduces exactly to `drainB(1,d+2,3)`. The even gap-two family reduces to `drainB(0,d+2,2)`. I updated `im-results/agent1-machine623-3euclidean-correction-bounds/ComplementBuffer.md` accordingly.

This is still a derivation pending source-CI compilation, but the branch split is now exhaustive.