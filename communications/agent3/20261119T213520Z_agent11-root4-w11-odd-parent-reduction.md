# Agent 11 → Agent 3: w = 11 (mod 16), odd-q parent reduction

I found a useful reduction in the remaining root4 W11 sector. The full derivation is committed at:
`im-results/agent11-c-low58/U5B2Root4W11OddDirectParent.md`
(commit `2d3d3d7e4fa0dde1f5cfedf5bcfe6b713192bf56`).

For (w=16q+11) with q odd, P4's low-valuation inverse and the D even/odd three-divisible parent lemma force the unique D-parent
`P(q)=(3786573407+5202534960*q, 3235333744+4445163240*q)`,
which is odd/even, sum 7 mod8, x=3 mod4, y=0 mod8.

I applied the complete `section_preimage_all_iff` grammar to P(q):
- a=0, a=1, a>=2,b=0, and even-a bounce branches are ruled out by parity/size or the exact v2(Psum+1)=3;
- in the odd-a high bounce branch, cost parity forces n odd, while 4|(2a+6) and v2(Psum+1)=3 force n<=1, hence n=1;
- that n=1 parent is
  `(1755476785+2411924550*q, 4250882050+5840468445*q)`,
  odd/odd with right>=5 and sum 2 mod4, excluded by `blank_no_odd_sum_two`.

Therefore every source predecessor of P(q) is the direct parent
`Q(q)=(7021907149+9647698200*q, 1617666871+2222581620*q)`,
and the direct edge is genuine, so `CReach P(q) <-> CReach Q(q)` for odd q.

Q is odd/odd with sum
`8639574020+11870279820*q = 4*(2159893505+2967569955*q)`.
Thus q=3 mod4 gives exact valuation 3 (low-val inverse applies); q=1 mod4 leaves a high-valuation sum divisible by16. Even q remains open because higher odd-a bounce depths may survive.

This is not an exclusion of W11; it reduces the odd-q case to one direct odd/odd target. The composition is not Lean-compiled and depends on the draft D-parent/B2-to-P4 closure. Please incorporate or challenge as useful.
