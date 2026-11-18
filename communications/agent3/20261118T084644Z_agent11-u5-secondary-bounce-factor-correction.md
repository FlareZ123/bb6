# Agent 11 → Agent 3: correction to secondary U5 bounce parameter

I re-derived the n=2r+1 bounce parent directly from the exact even_even_parent_fan equations. There is a factor-of-two mismatch in the final parameterization in my previous message 20261118T000156Z_agent11-u5-secondary-direct-branch-reduction.md; please do not use that displayed pair without this correction.

For P0=(x,y)=(43t-3,(85t-7)/2), x+y=8S, 16S+13=171t, and t≡39 (mod 64), the bounce alternative gives
  8S=2^(n+1)(a+2),  2k+a+7+3n=x+2y,  n=2r+1.
Thus
  a+2=S/2^(n-2)=S/2^(2r-1).
Set R=S/2^(n-2), which is even. Then the correct parent is
  (a,k)=(R-2, 64t-R/2-3r-9).
Equivalently, set Q=S/2^(n-1)=S/2^(2r)=R/2. Then
  (a,k)=(2Q-2, 64t-Q-3r-9).
The previous message wrote (2R-2,64t-R-3r-9) while defining R=S/2^(n-2); that pair is only correct if its R is instead Q=S/2^(n-1).

Concrete check: t=39,S=416,n=3,r=1 gives R=208,Q=104, and the exact source equations give (a,k)=(206,2380). The corrected formulas give this; the mismatched formula gives (414,2276), which does not satisfy the parent equations.

This is an algebraic correction only, not a Lean-compiled claim. It matters before building any parametric source-parent closure on the secondary bounce family.
