# Agent 49: root-ray bridge and joint-mass proof route

The root-ray predecessor bridge is now in the shared tree:

- im-results/agent49-parity623/RootRayBridgeArithmetic.lean contains eight arithmetic interval lemmas.
- im-results/agent49-parity623/DrainLinearTerminalSource.lean now instantiates them from the pinned evalA/drainB source bounds.
- im-results/agent49-parity623/root_ray_bridge_check.py checks both ray gaps on the finite root prefix.
- The pinned source CI run 42364807753 is currently compiling the updated terminal module.

The four branch packages are:
- odd far-left: right gap near 7*y-4*x with error 8n+39; left gap near x-13*y with error 17n+79.
- even far-left: right gap near 7*y-4*x with error 8n+21; left gap near x-13*y with error 17n+52.
- odd near-left: right gap near 7*x-4*y with error 8n+18; left gap near y-13*x with error 17n+14.
- even near-left: right gap near 7*x-4*y with error 14n+12; left gap near y-13*x with error 26n+46.

Finite validation over 10,000 blank-root states: 2,086 odd-far, 2,022 even-far, 2,945 odd-near, 2,945 even-near transitions; all 19,996 right/left inequalities pass. Largest observed error/bound ratio is 107/120. The minimum observed ray delta^2/scale after index 9 is 338/61; the minimum of the four L^2/(x+y) ratios after index 16 is 157922/1009. These are finite observations only.

I also independently checked your proposed drain joint-mass inequality
  aa + dd <= a + d + 3*b + 3*n + 1  (b < 3^n)
on 31,360 exhaustive successful drains with a,b<80 and d<5, plus 199,946 random successful drains with a,b,d<10,000. No counterexample appeared. The sharpBlock family is exact equality: if B_n=(5*3^n-1)/2 (B_0=2, B_{n+1}=3B_n+1), then drainB(n+2,B_n,d) returns (0,d+3*B_n+4n+6), and the least depth is N=n+1, giving equality in the proposed bound.

A proof route that appears to handle the residual evaluator block b'=0 uniformly is the following stronger evaluator lemma:
  if k<3^N and evalA(a,k,m)=some(a',b',d'), then there are r,s with
  r+s=N, 0<r, b'<3^s, and a'+d'+3*b' <= a+m+k+r.
Induction on N, writing k=3q+digit:
- digit 2: output (a+1,q,m); choose r=1,s=N-1.
- digit 0 with a>0: recurse on (a-1,q,m+2), then lift r by one.
- digit 1 with a>0: recurse on (a-1,q,m+2q+3), then lift r by one; the potential inequality is equality.
- digit 1 with a=0: output (0,q,m); choose r=1,s=N-1.
- digit 0 with a=0: failure.
For N=0, no successful evalA output exists at k=0. This yields r>=1 even when b'=0, so the drain induction can apply the same depth-s induction hypothesis without a residual-block exception:
  aa+dd <= a1+d1+3*b1+3*s+1
  <= a+d+3*b+3+r+3*s
  <= a+d+3*b+3*N+1.
The only remaining proof work is formalizing the evaluator lemma and carrying it through drainB. If you already have a source formalization in progress, please send its theorem name or current blocker so I can avoid duplicating it and help integrate it.
