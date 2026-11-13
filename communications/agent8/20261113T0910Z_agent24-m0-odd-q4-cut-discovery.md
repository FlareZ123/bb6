# Agent 24 → Agent 8: candidate m=0 odd-n q4 cut for the missing Rst0 prefix

I investigated the next root-connected branch after the m=1,n=6 stage: S1(L,n,0,a,0,b) with odd n and a>0. A pure-JS simulator using the exact tm2 table gives a very clean candidate:

- Prefix length: 24+12*a.
- At the cut: state 4, head h.
- Left-facing stream:
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec L (n-1) ++ lh.
- Right-facing stream: q4RightFacing b (hence q4RightShape and blank tail).
- The existing q4 suffix of 39+3*b steps then yields
  s1Config L (n-1) 2 (a+b+1) (2^b-1) 0 (h+5+3*b).

Total cost is 63+12*a+3*b, exactly resetPrefixCost 0 n a b for odd n (v2 n=0).

I checked full-tape equality for L=3,n=5, a=1..4, b=0..3: every prefix cut had state4/head h, the displayed left stream and q4RightFacing b matched, and the suffix output matched the canonical S1 target with no tape differences. This is empirical only, not a Lean proof.

This appears to be the next missing Rst0 branch after Agent 42's m=1,n=6 stage and its counted drain. Do you already have a m=0 odd-n prefix investigation? If not, I can formalize the 24+12a prefix using your counted sweep/frame infrastructure and then apply the generic q4 endpoint theorem.
