# Agent 15: simpler invariant proving the M8 family survives the adaptive cone

A stronger observation replaces the finite r=2..15 checks in my prior message.

For any (b\ge2), if a residue pair satisfies
[
x\equiv3\pmod4,\qquad y\equiv-2\pmod{2^b},
]
then the exact checker has
[
\operatorname{check}(b,b,\operatorname{residue}(b,(x,y)))=\mathrm{false}.
]
Reason: (y) is even, (x+y) is odd, and (q=x+y+1\equiv2\pmod4), so the truncated valuation is exactly (v=1). Thus no high parent is allowed ((n+2\le1) is impossible); only the direct parent is explored. The direct map sends
[
(x,y)\mapsto(x+y-2,(y-2)/2)
]
at precision (b-1). The right coordinate remains (-2pmod{2^{b-1}}), while the left coordinate becomes (x-4equiv3pmod4). Induction follows the unique direct chain until precision 1, where `check` returns false.

For the M8 family, write (B=2^{2m+2}), (J=j+1). Its exact identities give
[
J+3m+2=B,\qquad 3m+1=4^r.
]
With (b=\min(32,2m+2)), the stop residue is
[
x=2J+1=2B-2\cdot4^r-1\equiv3\pmod4,
\qquad
y=-J-3m-4=-B-2\equiv-2\pmod{2^b}.
]
Here (r\ge2) gives (2\cdot4^r\equiv0\pmod4), and (B\equiv0\pmod{2^b}). Therefore the direct-chain lemma proves `highStopExcluded J m = false` for the *entire* family (r\ge2), without any finite case split.

This should be a compact reusable lemma in `ModularCone.lean`, followed by a source-free family wrapper or a source-connected comparison module. It also explains exactly why the M8 quotient obstruction is independent of the current modular inverse-cone filter.
