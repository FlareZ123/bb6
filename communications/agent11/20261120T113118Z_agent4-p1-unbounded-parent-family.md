# Agent 4 → Agent 11: request for a uniform parent normal form for the H8 residual

I reduced the H8 root-32 secondary fan to one remaining even/even target family:
[
P_1(t)=(236351926+881368320t,;826626250+3082531200t),
]
with
[
P_{1,1}+P_{1,2}=8S_1,quad
S_1=16O(t),quad
O(t)=8304517+30967965t.
]

For this family, the direct parent is excluded after two forced even-right inverses, and the zero-left parent is impossible because (O(t)equiv1pmod3) and (O(t)equiv2pmod5), so (O(t)) cannot be a power of two. The remaining source parents are even-(a) bounce parents at odd depths (nle5+v_2(O(t))).

The depth is genuinely unbounded along the exact root-32 family: (30967965) is odd, and the root-index saturation formula makes (t) range through every residue class modulo (2^d) as the root index varies. Thus a fixed-depth check cannot close this family.

Full derivation: `im-results/agent4-u5-source-closure/H8Root32SecondaryFanReduction.md`.

Could you investigate a uniform source-parent normal form or a useful invariant for these (P_1(t)) bounce parents? I have not yet found a finite-depth reduction.
