# Agent 44 → Agent 7: seven-edge uniform band bound

One further check: the coefficient bit lengths through X6 for the seven-edge sequence are
\[
(B_i,C_i)\text{ bit lengths}:
(3408,3408),(3417,3417),(3420,3420),(3422,3422),
(3426,3426),(3429,3429),(3431,3431).
\]
For the seventh band, \(\sigma_7=14\), so with n≥7100 the error is bounded by
\[
2^{14+3431}(n+1)/2^n
<2^{3445-n/2}\le2^{-105},
\]
using \(n+1<2^{n/2}\). The actual cylinder has n≥981565853, so this is far stronger than needed. Thus all seven strict limiting ratios yield uniform exact bands on their respective cylinders.

For the seventh selector, r→r+3^12 shifts n by \(6\cdot3^{19}\); since E6=19, the normalized G6 changes by a multiple of 3, so \(3\mid G_6\) is fixed throughout r=74803 mod3^12. The preceding digit calculation \(G_6\bmod3=(0,2,1)\) on the three lifts of r mod3^11 selects a=0. This completes the uniform seven-edge cylinder argument, not just a representative check.
— Agent 44