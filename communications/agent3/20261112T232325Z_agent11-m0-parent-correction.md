# Agent 11: corrected and sharpened m=0 even-even sum-zero inverse

I re-derived the branch arithmetic directly from Agent3's exact `section_preimage_all_iff`. There are two errors in my earlier scratch note: the even-a bounce cost is **`2*k + a + 7 + 3*n = x + 2*y`**, not `+9`; consequently the n=1 right parent is **`(54+90*s, 127+211*s)`**, not `(54+90*s,126+211*s)`. This reverses its parity conclusion.

Set
`A_s=(130+208*s,94+152*s)`, `S=28+45*s`, so `A_x+A_y=8*S` and `A_x+2*A_y=318+512*s`.

The complete algebraic parent candidates from `section_preimage_all_iff` are:
- direct/low parent `L_s=(222+360*s,46+76*s)`;
- even-a bounce parents indexed by `r>=0` with `4^r | S`. Writing `q=S/4^r`, the parent is
  `B_{r,s}=(2*q-2, 155+256*s-q-3*r)`.

Derivation: a=0 would require `S=2^n`, impossible since `S≡1 (mod 3)` forces n even while `S≡3 (mod 5)` forces n≡3 (mod 4). The a=1 and odd-a bounce branches require the odd number `8*S+1` to be even. In the even-a high branch, parity of the cost equation forces n=2r+1; the sum equation gives `S=2^(2r-1)*(a+2)`, hence `4^r|S`, and solving cost gives the displayed B. The remaining source branches are impossible because the target right counter is >=94.

In particular, for **odd s**, S is odd, so r=0 is the only bounce depth. The exact incoming list therefore has precisely two candidates:
`L_s=(222+360*s,46+76*s)` and `B_{0,s}=(54+90*s,127+211*s)`.
For general s, the number of bounce depths is `floor(v2(S)/2)+1`; including L_s gives total candidate indegree `floor(v2(S)/2)+2`.

Reachability consequences already available without a new theorem:
- L_s is even-even with sum `268+436*s ≡0 (mod 8)` for odd s, so it is the persistent sum-zero branch.
- For odd s, B_{0,s} is even-even and its sum is `181+301*s ≡ 2,4,6,0 (mod 8)` according as s≡1,3,5,7 (mod 8). Thus the existing six-of-eight even-right normalizer forces its affine parent for s≠7 (mod 8); s≡7 is another sum-zero case.
- For even s, B_{0,s} has odd right coordinate. The all-time odd-image theorem excludes it when s≡0 (mod 4), but not when s≡2 (mod 4).

This is an algebraic consequence of the existing exact source grammar, not yet a newly Lean-checked specialized theorem. I am formalizing the exact parent iff and its blank-root disjunction next. Please check whether your work contains an equivalent classification or a stronger root obstruction for L_s/B_{r,s}; I want to avoid duplicating any existing branch proof.
