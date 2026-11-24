# Exact band-coordinate ancestry, and nested exponent sieve

This extends the shared BMO5 reduction for roots 1, 2, 3. All three blank-start root criteria were accepted in [CI 45379836827](https://github.com/FlareZ123/bb6/actions/runs/45379836827). The exact finite-depth residue classification and its root bridge were accepted in [CI 45383459136](https://github.com/FlareZ123/bb6/actions/runs/45383459136). The all-band and stripped-unit source closure was accepted in [CI 45387850562](https://github.com/FlareZ123/bb6/actions/runs/45387850562).

## Band coordinates and exact runs

Put P_j=5*2^j, L_j=P_j-j-3, T_j=2P_j-j-6. A band is L_j<=x<L_(j+1). Define Q_j(x)=2(x-L_j)+j+6 and W_j(x)=8P_j-4x-6j-27. Then W+2Q=4P_j-3. A regular same-band step multiplies Q by 3; a regular one-band advance multiplies W by 3. A regular two-band advance sends W to 3W+16P_j-6. The regular same-band formula for W is 3W-8P_j+6. The special top x=T_j+1 goes to 2P_j.

CapBandInverse proves the complete predecessor partition for every target band j>=6: regular parents from j,j-1,j-2, or the special parent from j-1. No parent iff y=0 mod 3 or y+3=P_j or y+6=P_j. The possible regular same-band parent exists precisely when y>=P_j+3 and y=P_j mod 3; the one-band parent when y=P_(j-1) mod 3; the two-band parent when y+9<=P_j and y=P_j mod 3. The special case is y=P_j.

CapBandRun proves that an n-step same-band run is equivalent to its endpoint Q equation Q(y)=3^n Q(x) and band membership. Its inverse existence condition is 3^n|Q(y) and 3^n(j+6)<=Q(y). CapUpRun proves the all-sign version for a regular one-band run from band j>=1 to j+n: endpoint band membership and W(y)=3^n W(x) are sufficient as well as necessary. A run ending at any y in band j+n exists iff 3^n|W(y), with no other range guard. CapUpRun was compiled locally with Lean 4.36.0-rc2, standard axioms only; its dedicated full-closure CI acceptance follows separately.

CapBmo and CapBmoSource connect the published two-counter BMO5 recurrence to the graph through x=10(2^a-1)-a+b+5. Target reachability from b=3,5,6 at a=0 is equivalent to root 2,1,3 respectively. This is an independent arithmetic connection to the original problem; the pinned Turing-machine source bridge remains as above.

## Exact initial negative phase and unbounded exclusion

The terminal W at i is -(2i+3). CapNegativePhase, CapStrip and CapStripSource prove: write 2i+3=3^n w, with 3 not dividing w, j=i-n>=6. The n-step one-band inverse run exists. It ends at the unique y in band j with W=-w, explicitly y=T_j-(2j+3-w)/4. If w=1 or 11 mod 12, y has no parent and y>3; hence rootOf(T_i)>3, excluding all three roots. For w=5 or 7 mod 12, the next predecessor exists, is in the same band, and has W=(8P_j-6-w)/3>0. In particular the length of the initial one-band phase is n exactly. This removes the entire first negative phase without a finite bound on n. The complementary unit classes are the only ones needing further work.

## Nested exponent sieve (paper proof and finite computation)

Fix an odd positive unit w=5 or 7 mod 12. Consider i(n)=(3^n*w-3)/2, j(n)=i(n)-n. After the n initial inverse steps and one same-band predecessor the positive W is (8P_j-6-w)/3. At depth s>=1 after the strip write

    D=3^s, W=(A P_(j-d)+C)/D.

Start (A,D,C,d)=(8,3,-w-6,0). Same-band inverse updates (A+8D,3D,C-6D,d), and one-band descent updates (2A,3D,C,d+1). By induction 0<A<4D, 3 does not divide A, d<=s-1, and -w-3(D-1)<=C<0. The identity 2P_(k-1)=P_k makes the numerator of a descent child equal to the parent numerator.

For any maximum s=t, it suffices to have j>=4t+20 and P_(j-t)/3^t>max(w+3,6j+40). This guarantees W>0 and W<4P_k-6j-40 at every depth k=j-d; hence the realized y is safely between P_k+3 and the top of its band. This follows by bounding W below by P_k/D-w/D-3 and above by 4P_k-P_k/D. No exceptional parent can then occur. For fixed w,t, all sufficiently large j satisfy the guard. For w=5,7 and n>=6, j>=1815; the guard holds for all t<=255: the inequality 5*2^(j-t)>(6j+40)*3^t follows at j=4t+20 by induction (left grows by 8 per t, right by less than 4), then by doubling as j increases. Thus every tested symbolic prefix stays in the regular safe region. The exact rule at depth s is: W=0 mod 3 selects descent; W=P_k mod 3 selects same-band; the third residue means no parent, hence a root larger than 3.

**Exact nested class theorem (paper proof).** At fixed w and parity of j (forced by w mod 4), the set of sufficiently large j with s additional inverse steps is a union of precisely 2^(s-1) distinct classes modulo 2*3^(s-1), all in that parity. At s=1 this is one parity class. Given one parent class, increase j by M=2*3^(s-1). The elementary valuation v_3(2^M-1)=s follows by induction: if a=1+3^s u with u a unit, a^3=1+3^(s+1)(u+3^s u^2+3^(2s-1)u^3), and the new coefficient remains a unit. Each child numerator is A' P_(j-d')+C' with A' and P units mod 3. The three lifts of a parent class therefore produce three numerator residues separated by a unit times 3^s modulo 3^(s+1), so exactly one lift for each child is integral. The child lifts are distinct, since their congruences are W=0 and W=P_k mod 3. This proves the count. For residue representatives with j<d, powers use modular inverses of 2 or any sufficiently large representative.

For n>=s, j(n)=-n-3/2 mod 3^(s-1); its parity is fixed by w mod 4 since 3^n=(-1)^n mod 4. Thus the class map from n modulo 3^(s-1) to the fixed parity residues of j modulo 2*3^(s-1) is bijective. For all sufficiently large n, the surviving exponents n after s additional steps occupy exactly 2^(s-1) distinct classes modulo 3^(s-1), density (2/3)^(s-1). In particular any fixed-w small-root terminal exponent set has natural density zero. This is an exact secondary sieve: its modulus depends on additional steps rather than the possibly huge stripped n.

## Reproducible results, 2026-11-24

Run:

    g++ -O3 -std=c++17 -Wall -Wextra strip_sieve.cpp -o strip_sieve
    python strip_check.py
    ./strip_sieve 5 1000000000000
    ./strip_sieve 7 1000000000000

Both runs classified 1,000,000,000,001 exponents n=0..10^12 inclusive, with zero small-root hits and zero unresolved cases. These are terminal indices exponentially larger than the initial scan, for the two specific unit families only.

* w=5: 13.66s, 1668KB peak RSS, 79,197,049 visited nodes, 35,569,379 singleton continuations, 203,518 deep continuations, maximum additional depth 70.
* w=7: 13.74s, 1568KB peak RSS, 79,206,529 visited nodes, 35,572,244 singleton continuations, 203,003 deep continuations, maximum additional depth 77.

The fast path carries P modulo 3^39. For n>=128, its exact exponent residue is -n-3/2 modulo 3^38, with the prescribed fixed parity. At each exponent lift n->n+3^(s-1), the power is multiplied by 2^(3^38-3^(s-1)) modulo 3^39. A<4D<2^64 for D<=3^39; 8D in the child update fits uint64 since the child is computed only with D<=3^38. Modular products fit uint128; signed C and its updates fit int128. Deep cases use arbitrary precision and compute the actual j modulo 2D from 3^n mod 4D, so no assumption n>=s is made there. For 6<=n<128 the deep path is used directly. For n<6 literal exact-integer inverse is used. The independent check matched all literal depths n=6..12 and complete modular singleton histograms n=0..10000 for both units. Executed and remote blob hashes are 04ed32ca06ba718d782d466726ffbc38f4ea1bff (C++) and a77cc9f772d40325d63f58a519a0ef2b758873ef (Python).

The nested class theorem and finite C++ run are not claimed as kernel-certified. The structural run lemmas and stripped-unit exclusion are formalized. No finite run proves universal nonhalting. The remaining central problem is a root-sensitive global obstruction to long positive-coordinate ancestry (including possible low-boundary exceptions) or a halting witness. A fixed-depth sieve cannot provide this by itself.

## Additional kernel closure

The all-sign regular one-band run characterization in `CapUpRun.lean` is source-closure accepted in [CI 45388885057](https://github.com/FlareZ123/bb6/actions/runs/45388885057). The modular lifting engine of the nested theorem is now separately kernel-certified in `CapNestedLift.lean` (local Lean 4.36.0-rc2, standard axioms only; blob `80eb0ebfe03b65319761f4284441d84cf7c79d1a`). `pow_period_exact` proves the exact unit quotient for the power-of-two period, and `exp_unit_lift` proves existence and uniqueness of a divisible lift among the three exponent lifts for any unit exponential-affine numerator. The full nested cardinality statement remains a paper proof.

## Complete sign-phase partition and a minimum excursion length

`CapPhase.lean` proves that for target bands j≥6, a negative W has only a regular one-band inverse descent (preserving the sign) or a same-band inverse step into positive W. Positive W remains positive under either regular branch. A two-band inverse skip or the special inverse is necessarily a return to negative W, with magnitude bounded by 2k+7 in its new band k. Each negative one-band phase of length n ending at upper band i satisfies 3^n≤2i+7. The exact mod-12 test therefore works at every negative return, not only the initial terminal: `CapPhaseSource.negative_phase_root_exclusion` proves rootOf(y)>3 when the stripped positive unit is 1 or 11 modulo 12 and the stripped band is ≥6. Full arithmetic/source closure, including the multiplicative lift, accepted in [CI 45389703658](https://github.com/FlareZ123/bb6/actions/runs/45389703658), revision a315631c25d40ebaa769978fbe050bf23bc0ce9f.

`CapPhaseCost.lean` defines the regular history starting with the same-band inverse out of W=-w, w>0. At depth s, initial band j, current band k, and D=3^s, it proves an affine packet 3^s W=A P_k+C with 0<A<4D, A%3≠0, and C≤-6-w. The stronger band-drop invariant is 4*3^(j-k)≤4D-A: same-band inversions preserve B=4D-A, while a descent updates B to 2B+4D and the history index bound supplies D≥3^(j-k).

A low-boundary return x≤P_k+2 therefore requires

    4*3^(j-k)*P_k + 6+w ≤ 3^s*(6*k+35).

Writing d=j-k and m=s-d, this yields 4*P_k≤3^m*(6*k+35). Thus **the number of same-band inversions alone** must be at least ceil(log_3(20*2^k/(6*k+35))), regardless of how many one-band descents occur. This is an all-depth necessary condition, not a proof of nonhalting. The source-level `small_root_positive_continues` theorem uses the strict reverse inequality to force regular continuation. The packet, cost and source-wrapper theorems passed [CI 45401516931](https://github.com/FlareZ123/bb6/actions/runs/45401516931), revision d9d5a03eb873061f80b73221336650bc85879a1f, Lean 4.36.0-rc2.


## Exact exceptional-return costs

For a two-band skip RegFrom j x y with Band (j+2) y, the exact coordinate relation is

    3 W_j(x) + 2 Q_(j+2)(y) = 3.

If W_j(x) = -3^n w, then 2Q = 3^(n+1)w + 3 and the band geometry sharpens this to

    2j + 13 ≤ 3^(n+1)w ≤ 6j - 3.

Combining the skip coordinate with the band-drop packet yields the exceptional-return costs:

- Skip parent from band k-2: 4·3^(j-k)P_k + 6 + w0 ≤ 3^s(6k-9).
- Special parent at P_k: 4·3^(j-k)P_k + 6 + w0 ≤ 3^s(6k+27).

Consequently, 3^s(6k+27) is a universal upper threshold for an actual exceptional return; the skip case is strictly cheaper. Both return-cost theorems and the exact skip-coordinate lemmas passed [CI 45403951106](https://github.com/FlareZ123/bb6/actions/runs/45403951106), revision 3504354e2f2a279f04a550557be9612be7d2d4f6.
