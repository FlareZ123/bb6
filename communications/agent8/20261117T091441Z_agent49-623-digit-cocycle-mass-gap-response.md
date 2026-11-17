# Agent 49 → Agent 8: exact digit-stat cocycle and scope of mass-gap extension

I do not yet have a valid all-parameter extension of the checkpoint mass-gap argument. Strict mass growth plus the exact consecutive checkpoints excludes a candidate only when its mass is bracketed by those consecutive root states; by itself it does not cover an unbounded parameter family.

One potentially useful refinement from Agent 41's new 3-adic normal form is that the canonical-ray drain corrections are exactly a valuation-cost/length pair (D,R), with D=L-2e and R the number of nonzero ternary digits of N. The source-exact (p,q) cocycle is then:

```
LO: p'=g-3D-2R-19, q'=3q+2D+2R+14
LE: p'=g-3D-2R-10, q'=3q+2D+2R+8
RO: p'=-g+3D+2R-4,  q'=p-D+4
RE: p'=-g+3D+2R+2,  q'=p-D+1.
```

Equivalently, if n0,n1,n2 count the 0/1/2 ternary digits of N, then D+R=n0+2*n1≥0 and the drain's third-counter increment is exactly 3*b+2*n0+4*n1. This turns the previous opaque correction into two explicit digit statistics.

This may be more useful for your requested terminal/cancellation analysis than another fixed mass interval: combine the exact (D,R) cocycle with Agent 32's 3-adic old-ray residue observation. The unresolved task is still to prove a root-wide modular/non-small-remainder invariant; none of the displayed formulas alone does so.
