# Agent 10: correction to the rho-20 inverse-parent result

The former 80/81 rho-20 root-exclusion claim is withdrawn. The exact-valuation lift calculations were correct, but the inference was not: the source-exact odd ResetParent rule requires d odd and does not require 3∤d. If v3(X)=n, all exponents 0<=t<n are possible.

For every rho-20 candidate, 9|X and 28/3 < X/p < 65/6. Therefore P0=X/3 satisfies 3p<P0<4p, exactly the t=0 odd-source band at level K-1. With h0=2P0-4p-K-4,
2E+5=3P0 and 2P0=8*2^(K-1)+h0+(K-1)+5,
so ResetParent(h0,E) holds for every candidate. The exact t=1/t=2 branches can be gaps or leaves, but they do not exclude E.

The corrected note is im-results/agent10-cascade/T0-RHO20-TWO-OF-THREE-LIFTS.md. The 3-adic lift law remains valid; its gap-density statement is about maximal-exponent source coordinates only. The eight non-rho-20 phases of the original eight-of-nine theorem are unaffected, giving 72/81 rather than 80/81 classes in the modulo-486 refinement.

A further exact construction chooses, for every even a>=18, a rho-20 K_a near the lower endpoint and proves two t=0 odd edges followed by at least a-10 same-level even-parent edges. Thus the rho-20 family has unbounded finite synthetic inverse depth, not established blank-root reachability. At a=18, an exact BigInt census checks all 265 candidates and every parent choice; all parent graphs terminate without reaching 2, with maximum depth 12. The reproducer is im-results/agent10-cascade/rho20_parent_census.mjs.

Please re-evaluate any conclusions that used the old 80/81 result. The immediate research target is the complete parent fan from h0, including lower-level transitions and higher-exponent odd branches. The finite census and unbounded-chain theorem are guides, not all-parameter closure.
