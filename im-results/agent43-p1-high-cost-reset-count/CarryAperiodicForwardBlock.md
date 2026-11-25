# Modular carry periodicity obstruction and exact forward blocks

## Modular carry aperiodicity

[CarryAperiodic.lean](CarryAperiodic.lean) is kernel-checked with Lean 4.36.0-rc2, ordinary axioms only; [source CI 45590461666](https://github.com/FlareZ123/bb6/actions/runs/45590461666) at 1b698bbf5987f55331c091932514d285a815d4be. [CarryAperiodicSource.lean](CarryAperiodicSource.lean) directly connects the exact weighted-word equation from Agent9's unchanged BatchCarry to the finite-period obstruction. It treats precisely the strict interior used in Agent9's BatchCarry. If integer states satisfy

    1 <= c_j <= q+j-3, x_j in {0,1},
    2*c_(j+1) = c_j + (q+j)*x_j,

then no infinite such path can have eventually periodic x. More quantitatively, a legal finite word of length 2p+L cannot have period p>0 when 2^L > 2(q+p). The statement is for every clock q, not only a central start. It does not exclude arbitrary aperiodic infinite paths or all surviving critical indices.

Proof: for a period p put d_j=c_(j+p)-c_j. Then 2d_(j+1)=d_j+p*x_j, and e_j=d_(j+p)-d_j halves exactly. An infinite integer halving sequence is zero, so d is periodic. Cyclic inequalities for d and p-d imply 0<=d<=p. If either endpoint occurs, the corresponding bit tail is constant and the strictly positive carry c or complement q+j-2-c halves forever, a contradiction. Thus the p slopes occupy only p-1 values. Equal slopes force equal preceding slopes (the two possible predecessor branches differ by p), and cyclic periodicity propagates equality to a smaller positive period of x. Descent on p proves the claim.

For the finite version, e halves for L steps; |e_0|<=2(q+p)-8<2^L forces e_0=0. Hence d_p=d_0, and the first p slopes extend cyclically. Set C_(kp+r)=c_r+k*d_r for 0<=r<p. The cyclic inequalities 0<=d_r<=p preserve the strict interior and the exact recurrence, yielding an impossible infinite periodic continuation.

This supplies an aperiodicity constraint on hypothetical all-time modular witnesses and an explicit rejection test for repeated-word certificates. It is not an index extinction proof.

## Exact two-candidate forward block

[ForwardBlock.lean](ForwardBlock.lean) proves the ordinary map v'=(2v) mod (q+1), clock q'=q+1. For a k-step block define X=2^k*v, B0=floor(X/q), and corr(k,B)=sum of i*b_i*2^(k-i) over the wrap word's k bits (i=1..k). If 2^(k+1)<=q and 0<=v<q, the exact word B is B0 when q*B0+corr(k,B0)<=X and B0-1 otherwise. The endpoint is X-q*B-corr(k,B). The proof uses an exact word identity and an induction establishing legality of the selected word, without individual wrap searches.

For v>=3, the block is reset-free if B=0 or its endpoint R>2*lowbit(B): after a positive-time residue <=2 there can be no further wrap in a fitted block, so the trailing zero count of B bounds the possible final residue. [ForwardBlockSource.lean](ForwardBlockSource.lean) uses Agent28's original-source macro and distinguishes true macro boundaries from partial ordinary wraps. The source bridge passed [CI 45589502759](https://github.com/FlareZ123/bb6/actions/runs/45589502759) at 84ebbdd8c1618a75f45feb927361228986e90713.

This differs from Agent50's rational asymptotic renewal block: the two-candidate theorem applies to every fitted ordinary block. It is an acceleration, not an all-time decision.

[forward_block.cpp](forward_block.cpp) is a separate uint64/uint128 regression implementation, with fixed 64-bit masks for the digit-weight sum. Compile with g++ -O3 -std=c++17 forward_block.cpp -o forward_block. Both scalar and fast variants test all fitted blocks with q<200. Starting at (5,0), both give (1000000000,646533208), with identical exceptional event lists; local timings approximately 1.46 vs 0.42 seconds. The fast run to 20000000000 gives v=1449139138, 19999999400 ordinary skipped steps, 266 scalar steps, approximately 7.52 seconds. These are implementation regressions only: the corresponding critical indices are already covered by stronger existing source-certified results. The C++ executable is not itself a verified checker.
