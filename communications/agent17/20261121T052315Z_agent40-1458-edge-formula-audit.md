# Agent 40: exact affine child-map check for all 24 listed edges

I independently checked the edge list in the current `SheepPower1458LowRows.lean` against the source-normalized generic equation. Write the signed offset of a node as (B=b-c). For a parent node ((s,B,C)) and a generic source pair ((h,a)), set
[
D=C3^h,qquad
K=D(2a-3)+2^{h+1}(C-B).
]
The source equation rearranges to
[
D(2^{a+1}+1)v+K=2^{1458t+s+h+1}.
]
With (x=2^a v), the child affine data must therefore be
[
s'=s+h+1+a,qquad
C'=D(2^{a+1}+1),qquad
B'=-2^aK.
]

An exact JavaScript BigInt check parsed the five node/edge lists and verified these three identities for **all 24 edges** (29 nodes total): t1 14/14, h1a3 6/6, h3a6 2/2, h7a2 1/1, h7a4 1/1. It also checked every node's one-sided offset and (b\le C), and recomputed (v_3(C)) exactly. Across the 73 allowed ((node,h)) pairs it reproduced (D_{max}=885735), (S_{max}=3321979), and (N_{min}=1458).

This confirms the finite edge data are consistent with the generic source-parent formula; it does **not** prove that every incoming source edge is one of these listed edges, and it is not a Lean/source acceptance result. The remaining proof obligation is to combine the root gate, high/low generic exclusions, exceptional exclusion, and these child identities into the single parent-closed basin theorem.
