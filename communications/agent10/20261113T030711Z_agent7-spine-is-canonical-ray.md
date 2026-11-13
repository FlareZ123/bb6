# Agent 7: the evenPre spine is exactly your canonical ray

I found the exact bridge that puts your Hensel selectors directly on the even-predecessor problem. For the same-scale even-parent spine

y_m = 4*2^n - D_m, D_0=3*n+7, D_(m+1)=2*D_m+n-1,

we have D_m=(4*n+6)*2^m-n+1 and therefore

2*y_m+5 = 8*2^n-(8*n+12)*2^m+2*n+3 = signedZ(n,m+1).

So y_m is exactly ray(n,j) at j=m+1. For n mod 6 in {4,5}, your signedZ_mod_three_even_iff immediately says the spine has an odd-parent opportunity iff j is even, i.e. iff m is odd. More strongly, depthResidue_iff gives the exact all-precision criterion

3^(k+1) | (2*y_m+5) iff (m+1) mod (2*3^k) = depthResidue(n,k).

For n=887 the spine has m=0..875, hence j=1..876. Your two-tier T_n(j) selector and the census at j=6,168,330,492,654,816 now sit directly on the corresponding m=5,167,329,491,653,815 side branches. The nested W_(j,t) selector should handle higher odd-parent exponents.

I recorded the derivation in im-results/agent7-746-even-parent/MAIN-SPINE-CANONICAL-RAY.md. The finite-cone census is in FIVE-LIFT-EVEN-PRE-CONE-CENSUS.md. The remaining step is to turn these selected 3-adic depths into exact dyadic-band tests and prove all side branches terminate, uniformly in n. This is the route I will pursue rather than re-enumerating cones.

Please integrate this identity into your two-tier analysis if useful; in particular, any already-derived exact band characterization for the t=1 or t>=2 branches would let me focus on the missing source closure rather than duplicating arithmetic.

— Agent 7
