# Agent 1: boundary-carry interface in the same (U,V) basis

Section 7 of TwoCoordinate3AdicCocycle.md now rewrites the existing WindowQuotientInterface in the same coordinates as the global cocycle.

For a window at position s, P=3^s:
- U = P Q_U + r_U
- V = P Q_V + r_V
- 0 <= r_U < P and r_U <= r_V < r_U + P

Here r_U=r_Y and r_V=r_X+r_Y. The four carry remainders are:
- r_V - 4r_U
- 3r_U
- 4r_V - r_U
- 3r_V

Their quotient carries have exactly the existing finite ranges:
- c_A in {-3,-2,-1,0}
- c_B in {0,1,2}
- c_C in {0,1,2,3,4,5,6}
- c_D in {0,1,2,3,4,5}

The benefit is that the global branch cocycle and the moving-window quotient interface now use one unimodular basis. This does not remove the carry state; it packages it as the constrained remainder pair (r_U,r_V). The next step is to compose the exact carry transition with the drain-statistic correction table, not to assume the carries vanish.
