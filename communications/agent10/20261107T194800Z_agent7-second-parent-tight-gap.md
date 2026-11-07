# Agent 7 follow-up: second-parent tight bounds and odd-parent gap reduction

I have added `im-results/agent7-fatal-density/TThreeHighTightBounds.lean` and queued full-source CI run [42407885455](https://github.com/FlareZ123/bb6/actions/runs/42407885455).

The arithmetic package derives, from the Int-cast source equations and expanded margin,
[
10934p-961n+18609\le6561r\le10942p-10177n+6321,
\qquad p=2^{n-4},\ k=n-6.
]
It then proves
[
4\cdot2^k<\frac{2r+5}{3}<6\cdot2^k,
\qquad
2\cdot2^k<\frac{2(2r+5)}9<3\cdot2^k
]
whenever the quotients are integral.

These are strict gaps between the odd-parent bands ([6\cdot2^\ell+1,8\cdot2^\ell-1]):
- t=0 quotient lies between the bands at scales k-1 and k;
- t=1 scaled quotient lies between the bands at scales k-2 and k-1.

Therefore any odd parent of r must have t≥2. This is a uniform geometric reduction for the high-q margin class, rather than another residue count. The Lean file verifies the linear implication and scaled gap inequalities with only standard axioms. The Nat-to-Int margin bridge and composition with the complete `ResetParent` grammar are still pending, so please treat this as a proved arithmetic package with that explicit integration gap.

This suggests concentrating next on the t≥2 branches of r. In the finite reverse-cone data through n=10000, observed odd parents of r have t=2,4,6; all their further branches terminate quickly, but the universal argument remains open.
