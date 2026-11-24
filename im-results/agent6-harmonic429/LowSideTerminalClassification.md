# Exact low-side terminal words of Cryptids #429

The accelerator is the unchanged [BB429Rank.lean](../agent5-429-rank/BB429Rank.lean). The result applies to prepared states `(0,W)`, where `X=16^m`, `W=72X+d-(12m+6)`, `m>=1`, `d>=6`, `d=2 mod 4`. It does not assert that a genuine blank run reaches these states.

## Arbitrary nonsection word theorem

Use exact rank coordinates `A=2u+6, R=2u+w`. After the initial F^(4m+3) burst the coordinates are `A=48X, R=72X+d+3`. Every subsequent nonsection transition is one of the three guarded affine maps

| Move | A' | R' | Guard |
|---|---|---|---|
| F | 2A | R+3 | 2A<=R+9 |
| Oe | 2A-R+9 | R+11 | R=1 mod 4; R-2A+12<=-7; R-A+6>=3 |
| Oo | 2A-R+1 | R+7 | R=3 mod 4; R-2A+12<=-5 |

For each fixed finite word v of length n, write its symbolic final state as `A=aX+bd+c, R=72X+d+r`. These integer coefficients are calculated by composition, with initial (a,b,c,r)=(48,0,0,3). Always b<=0 and a-72b=48*2^n. Put

    M = 1-2b > 0, odd
    K = 2a-72 = 96*2^n-72M
    H = r+13-2c.

The final halting equation is exactly `M*d=K*X-H`. For every guard linear form l(x,d)=l.x*x+l.d*d+l.c, define its elimination

    E_l(X)=(M*l.x+K*l.d)*X+(M*l.c-H*l.d).

The exact scale test (theorem terminal_iff_scale) is:
1. m>=1 and the word's phase constraints hold;
2. 4M divides K*16^m-H-2M;
3. E_l(16^m)>=0 for every guard form, including d>=6.

The congruence recovers the uniquely determined integer d with d=2 mod 4. Guard elimination guarantees all source counter inequalities. There is no simulation cutoff and no dropped guard. `terminal_source` reconstructs the actual accelerator trajectory; `terminal_complete` covers every finite terminal trajectory after the initial burst that has no intervening outputs to sections 0 or 11.

Let N=M/gcd(M,abs(K/4)). This is a positive odd integer. If there is any scale witness m0, the congruence holds exactly for m=m0 mod p, where p is the multiplicative order of 16 modulo N (p=1 when N=1). Theorem `terminal_progression` proves existence and p<=N. The general affine argument gives an interval in X. The sharper guard-ray theorem below establishes that whenever the phase and congruence are compatible, it is a final ray.

Moreover set

    B=1+sum_l |M*l.c-H*l.d|.

For m>=B each eliminated linear guard has a stable truth value, because 16^m>|M*l.c-H*l.d|. Every scale witness above B+N can therefore be replaced by one in [B,B+p-1]. The theorem `finite_scale_search` proves

    (exists m, Terminal m v) iff (exists m<=B+N, Terminal m v).

This is a uniform finite algorithm for the scale quantifier, for each fixed word. The unbounded word-length quantifier is not resolved.

### Formal modules

- [BB429LowWord.lean](BB429LowWord.lean): guarded rank maps, word source soundness/completeness, coefficient identity.
- [BB429LowWordPeriod.lean](BB429LowWordPeriod.lean): exact eliminated scale criterion and guard interval.
- [BB429LowWordProgression.lean](BB429LowWordProgression.lean): gcd-reduced period, single residue class.
- [BB429LowWordFinite.lean](BB429LowWordFinite.lean): explicit finite scale-search bound.

## Guard rays and the congruence-only existence test

The earlier interval statement can be sharpened to a **final ray**. Let `v` have length n, encode F by 0 and either O by 1, and let B be the resulting binary integer. Then b=-B, M=2B+1, K=96*2^n-72M. At a prefix of length j, let q be the binary integer of the remaining suffix (length k=n-j, including the next move). The coefficient of X in each eliminated guard is exactly

    F:      96*2^j*(2^k-(2q+1))
    Oe/Oo:  96*2^j*((2q+1)-2^k)
    Oe w:   48*2^j*(2*2^k-(2q+1)).

All three are strictly positive: the leading suffix bit selects the first or second case, and 0<=q<2^k ensures the extra Oe guard. This is an exact cancellation of prefix dependence, valid for arbitrary words before any phase restriction.

Every phase-valid word alternates odd/even ranks; every second move must be F. The terminal congruence forces n even. Hence the maximal binary pattern is 1010...10, giving 3M<=4*2^n-1 and **K>=24**, so the additional d>=6 guard also has positive slope. In fact n=2 mod4: r_final=3+3n mod4, c remains even, K is divisible by 4 and the congruence forces H=2 mod4. Thus r_final=1 mod4.

Consequently, for every phase-valid word that has a congruence solution, the exact guard threshold is

    X0 = max_l ceil((H*l.d-M*l.c)/(M*l.x+K*l.d)),

where l ranges over allForms (including d>=6). Every guard is satisfied iff X>=X0. If the congruence has one exponent witness, its period p<=N from the earlier gcd-reduction theorem gives arbitrarily large exponent witnesses, and every sufficiently large one satisfies all guards. The prepared terminal scale set is therefore **empty or one arithmetic progression cut off below**, never a nonempty finite interval. Equivalently

    (exists m, Terminal m v)
    iff phases v initial and
        (exists m0<N, 4M divides K*16^m0-H-2M).

The residue witness m0 may be zero; it is lifted to a positive sufficiently large exponent along its arithmetic progression. This removes the guard-feasibility and guard-bound search from the *existence* decision for a fixed word, rather than merely bounding the search. At a prescribed scale the guards remain necessary. It does not eliminate the unrestricted word quantifier or relate a synthetically halting seed to the authentic blank root.

[BB429LowWordSlopes.lean](BB429LowWordSlopes.lean) proves the slope identities, all branch slopes positive, K>=24, n mod4=2, monotonicity, eventual guard feasibility and cofinal scale tests under the established periodicity hypothesis. Local Lean 4.36.0-rc2 compiled the exact file (Git blob f0792f5e33e5e2dfd05377a119c51a72584bab9f) against a declaration slice of the unchanged LowWord/LowWordPeriod definitions and the exact symbolic_coefficients and coefficient_identity proofs; every printed axiom profile was standard only. The original dependency closure was not locally available (direct git DNS failed). [BB429LowWordCofinal.lean](BB429LowWordCofinal.lean) composes the slope results with the already-proved congruence_period and terminal_iff_scale; full source acceptance is not yet recorded. The existing manual general-escape workflow has a selectable low-word target for this exact closure, with no per-commit trigger.

## Specialized formulas and examples

### Zero-cycle family

[BB429LowZeroCycle.lean](BB429LowZeroCycle.lean) gives an iff for all scales m and terminal F-burst lengths t, after the initial F^(4m+3) and Oe,F pair with no preceding four-step low-side cycles. Let X=16^m and start at (0,72X+d-12m-6), where d>=6, d=2 mod 4 and d+19<=24X-3. The terminal burst halts iff there exists s>=7, s=3 mod 4, such that

    t+12 = 2^s
    (4m+5) mod (2(t+2)) = t+2+s.

Here the existential d is uniquely fixed by the clock equation. Equivalently m=(t+s-3)/4 + q*(t+2)/2 for q>=0. The first family is t=116, m=30+59q; the second is t=2036, m=511+1019q. With v=24X+6-d the determining equation is (2^(t+2)+1)v=3(2^(4m+5)+t+12). Necessity uses reduction of powers modulo 2^k+1, where k=t+2; sufficiency reconstructs positive natural counters satisfying all guards and proves the actual source run of length 4m+5+t ending at the halt test. This is a complete infinite prepared-state classification, not an authentic blank-root ancestry result.




### Complete-cycle families

The modules [BB429LowGeneral.lean](BB429LowGeneral.lean), [BB429LowEvenTerminal.lean](BB429LowEvenTerminal.lean), and [BB429LowPeriod.lean](BB429LowPeriod.lean) extend the zero-cycle classification to arbitrary complete cycles and both terminal F-burst patterns. Write `X=16^m`, `W=72X+d-12m-6`, and let `j` be the number of complete Oe F Oo F cycles after the initial F burst. Let `e=1` for a final Oe F pair, or `e=0` for a direct terminal F burst (j>=1 in the latter case). Define

- L=4*2^t, K=(4^e*16^j-1)/3, C=24X+8j+6e, H=16-4e+3t, M=L*K+1.
- The exact terminal parameter equations are v+K*d=C, L*v=3C+H+d, with the natural-number and guard conditions in the respective TerminalHalt definitions. Hence M*d=(L-3)*C-H.
- A necessary test at every scale is t mod 4=2(1-e) and (L-3)*C mod M=H mod M. For C>=M*(H+28), that test is also sufficient, by reconstruction of d and v and source-level execution witnesses. The odd pattern excludes j=2 mod 3 unconditionally.
- The progression theorems prove: for fixed j,t, either there is no halting scale, or every witness lies in one residue class modulo the least positive order of 16 modulo M; above the explicit threshold, every scale in that class halts for this prepared terminal pattern. In the presence of any witness, M is coprime to 3 and 2, and L-3 is coprime to M since M-K*(L-3)=3K+1 is a power of two. This proves uniqueness, not merely eventual periodicity. The finite pigeonhole/order argument is also formalized in Lean.

Exact computational examples (separate concrete Lean certification still in progress): e=1,j=1,t=12 gives M=344065, 16^m mod M=82431, m=161 mod 17203; e=0,j=2,t=2 gives M=1361, 16^m mod M=392, m=51 mod 170. The latter contains the earlier prepared m=51 counterexample. These are prepared-state results; the source theorem does not assert that blank-root execution reaches W. 


## Reproduction and scope

Full unchanged-source local compilation with Lean 4.36.0-rc2 succeeded in this order: BB429Rank, BB429LowReturnBand, BB429LowBoundary, BB429LowZeroCycle, BB429LowGeneral, BB429LowEvenTerminal, BB429LowPeriod, BB429LowWord, BB429LowWordPeriod, BB429LowWordProgression, BB429LowWordFinite. Use LEAN_PATH=.:../agent5-429-rank and compile each to its .olean before the next. Git blob hashes for the three original dependencies were respectively 5a93ba2d833ca375478f1183f45712a34f299f19, fe8b604f3726dd44e36a0108b9215b5e872eb2a1, 55589e7de35ea90cfb9c638cc002149053aa2be3. All new files match their pushed Git blobs. Exported theorem axiom lists contain only propext, Classical.choice and/or Quot.sound. The exact original raw-TM bridge is a separate layer; the prepared-state results are expressed in the original repository accelerator.

**Remaining objective:** determine genuine rooted section ancestry and eliminate the unrestricted branch-word quantifier (or prove a direct global invariant). The prepared-state arithmetic characterizes real counter-model halts, not necessarily blank-origin halts. An exploratory inverse sieve using odd/odd residue restrictions was corrected to respect the lower-counter guard; the corrected search retains the intended prepared zero-section ancestors, so it supplies no blank-root exclusion.
