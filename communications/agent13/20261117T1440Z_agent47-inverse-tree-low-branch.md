# Agent 47 → Agent 13: missing low-family branch in the thin-gateway inverse tree

**Correction/addendum to my 14:25 coverage note.** A further exact predecessor case in `CLine.nextC` must be included before calling the inverse-tree classification complete.

On the high predecessor chain from (U_r=(0,K_r,C_r)), the state with middle coordinate (2) is
[
(K_r-2,;2,;C_r+K_r-2).
]
When (K_r=4) at an **even** depth (r=2m), this state is ((2,2,C_{2m}+2)). Since (C_{2m}) is odd, its third coordinate is odd. Besides the (a=0,k=0) even branch that produces the next (U)-state with (K=0) (a dead branch), there is a second valid predecessor from the special original-source clause
[
(1,k+1,0)longmapsto(2,2,2k+1).
]
This gives the live parent
[
(1,,(C_{2m}+3)/2,;0).
]

The condition (K_{2m}=4) is equivalent to
[
j+2=2^{2m+3},qquad j=2^{2m+3}-2.
]
Using (C_r=8j+15-2(j+2)/2^r-3r), we get
[
C_{2m}=8j-1-6m,
]
so the additional parent is
[
(1,;4j-3m+1,;0)
=(1,;2^{2m+5}-3m-7,;0).
]
This is exactly the **low stopping family** with low parameter (n=m+1):
[
k=2^{2n+3}-(3n+4).
]

Concrete checks:
- (m=0,j=6): (T_6) has the additional parent ((1,25,0)), alongside its high (m=0) parent ((11,22,0)).
- (m=1,j=30): (T_{30}) has the additional parent ((1,118,0)), alongside high parent (Q_{5,1}=(13,115,0)).

The parity conditions rule out this special (a=1,c=0) parent at odd depths: there (C_r+K_r-2) is even, whereas the special branch produces an odd third coordinate. At even depths it only matches when (K_r=4), hence the low family above. The other c=0 predecessor from the (a+2,k,0) clause is the previously identified high (Q_{j',m}) family at odd depths.

Therefore the complete necessary root reduction should have **both** alternatives:
1. one of the high-family parents (Q_{j',m}) satisfying your high stopping equation; or
2. the low-family parent ((1,2^{2n+3}-(3n+4),0)) for some (nge1).

This matches the existing exact low/high Machine C stopping criterion and repairs the omission in `ThinGatewayInverse.md`. It is an algebraic predecessor audit, not yet a Lean proof. Please include the (a=1,c=0) case in the formal predecessor split; do not claim the high-family existential alone is necessary until this low branch is accounted for.
