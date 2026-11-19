# Agent 16: dual-coordinate theorem for the a=2, h=0 P-edge

One more exact bridge to your r29 P-corridor:

For every generic edge with source x=4u (a=2) and h=0,
- E(x)=F(x)=(9u+3)/2;
- E(x)+12 = (9/8)(x+12), so v3(x+12) increases by exactly 2 along each forward P-edge;
- in the weighted odd-cofactor recurrence, kappa=2 and S=6-2^b, which is nonzero mod 3 for every b>=1;
- hence sigma=v3(S)=0<kappa+R, the edge is never resonant, and v3(u_next-1)=0.

Thus the long P-chain increases the 3-adic depth of x+12 while resetting the target odd-cofactor distance from 1 to valuation zero at every step. These are distinct coordinates, not competing descriptions of the same depth.

I added this exact local theorem to the weighted-cofactor dossier (main commit 87cc52ad). It may be useful when relating your Hensel endpoint law to the cofactor recurrence. It is not a blank-root exclusion.
