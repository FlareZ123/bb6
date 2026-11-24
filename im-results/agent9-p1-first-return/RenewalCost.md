# Superlinear critical right-five cost floor

**New source-level consequence (2026-11-24):** for every fixed integer B≥1 there is an effective N_B such that for every n≥N_B, every original OddCone history from (14·2^n−2n−16,3) to (b,5) has cost m>(B+1)n+2. In particular m/n tends to infinity along any sequence of such histories with n→∞. Explicitly, for ALL n≥8000,

    m > 4n+2.

For n=10002 this means m≥40011. No reset-count or progression restriction is imposed. The proof is an exact paper derivation using the original-source cost/return adapter accepted in [CI 45508888563](https://github.com/FlareZ123/bb6/actions/runs/45508888563). The new rational-renewal argument itself is not yet Lean-certified. It does not exclude superlinear costs and does not decide P1 or BB(6).

The renewal mechanism is adapted from Agent50's [exact reverse-unit renewal theorem](../agent50-p1-dyadic-width/reverse_unit_renewal.md), which was applied to two prepared restart progressions. Here the first return from the right-five seed itself determines a different universal initial phase; its denominator growth gives a source cost lower bound rather than a lower bound on a prepared-state local reverse prefix. The proof below supplies independent exact inequalities and an explicit 8000 threshold.

## 1. Initial phase and clock

Put P=2^n, Q=7P−n−3. By [CostSource.lean](CostSource.lean), a right-five history of cost m implies a return of length k=m+1:

    q+k=Q, r_0=1, r_j=2r_(j−1) mod(q+j), r_k=1.

Assume k≤(B+1)n+3 for fixed B. For sufficiently large n, 4P<q+1. The first n+2 steps double without a wrap, so no positive return is possible there. At step n+3,

    q_0=q+n+3=7P−k, d_0=P+k.

Indeed 8P modulo 7P−k equals P+k when 2k<6P. Thus the remaining trajectory begins with phase r=1/7, clock perturbation a=−k, state perturbation b=k in q_0=7P+a, d_0=7P r+b. Both perturbations are O_B(n).

## 2. Explicit rational-renewal lemma

Let q=7P+a and d=7P r+b be integers, 0<d<q, |a|≤A, |b|≤H_b, A+n≤P. Suppose 0<r<1 is rational with denominator dividing odd D>1. Write μ(r)=Σ_(i≥1) i ε_i 2^(−i) for its canonical binary digit moment. Let

    T=(d−a r−μ(r))/7,  ρ=T−floor(T).

Suppose ρ≠0 and its denominator divides R. Set H=A+H_b+10, let S=2^ell be the least power of two ≥2DH, set K=n−ell, and E=(A+n+2)S. Assume

    S≤P,    7P>R S(E+A+n+8).                     (1)

Then the next n unit steps are all safe: 2≤d_j≤q+j−8, including j=0. At the end,

    d_n=7P ρ+b_new,    |b_new|≤E.                (2)

In fact the exact n-bit wrap word is floor(T).

**Proof.** The wrap bits x_j are zero or one, as each previous state is smaller than its clock. Write U_j=Σ_(i=1)^j x_i 2^(j−i), V_j=Σ_(i=1)^j i x_i 2^(j−i), u_j=U_j/2^j, v_j=V_j/2^j. The exact recurrence identity, also kernel-checked in ReverseUnitMap.lean, is

    d_j=2^j d−q U_j−V_j.

At j=n, 0≤d_n<q+n, u_n<1 and v_n<2 imply |r−u_n|≤H/(7P). Since r has odd denominator dividing D and is strictly interior, its distance from any multiple of 2^(−K) is at least 1/(D·2^K)=S/(DP)≥2H/P. Hence u_n and r have the same first K bits. For every j≤K, U_j=floor(2^j r), and

    d_j=7P {2^j r}+2^j(b−a u_j−v_j).

The absolute error is at most 2^K H≤P/(2D). The ideal phase has distance ≥1/D from both endpoints. Inequality (1) implies 7P>2D(A+n+8), and consequently both safety margins exceed 8 after allowing the clock offset.

For j≥K the first K bits agree, so |r−u_j|≤2^(−K), |μ(r)−v_j|≤(K+2)2^(−K). The latter follows by summing the geometric weighted tail. Rearranging the exact identity gives

    d_j=7P (T/2^(n−j)−U_j)+E_j,
    |E_j|≤2^j (A+K+2)2^(−K)≤E.

At j=n, the nonzero fraction ρ lies in [1/R,1−1/R]. If U_n≥floor(T)+1 then d_n≤−7P/R+E<0. If U_n≤floor(T)−1 then d_n≥7P+7P/R−E>q+n. Both contradict the recurrence range. Thus U_n=floor(T). At every K≤j≤n, U_j is the leading j bits of U_n, hence floor(T/2^(n−j)). Since T is nonintegral with denominator dividing R, the fractional part of T/2^(n−j) has both margins ≥1/(R·2^(n−j))≥1/(RS). By (1), subtracting E and the clock offset still leaves margins exceeding 8. This gives safety and (2). QED.

## 3. Denominator growth never permits a zero phase

Start D_0=7 and L_0=3. For i≥0 define e_i=2i+1, L_i=ord_(D_i)(2), M_i=2^L_i−1, and

    D_(i+1)=7 D_i M_i / 7^(e_i−1).

Every D_i is odd. Inductively v_7(D_i)=e_i, v_7(L_i)=e_i−1, and every actual phase has reduced denominator dividing D_i with exact 7-valuation e_i. These hold at r_0=1/7. To prove the induction, let w=M_i r be the integer repeating binary word of length L_i (including leading zeros), W its weighted integer with weights 1,...,L_i. Summing its periodic digits gives

    μ(r)=(W+L_i r)/M_i.

Since v_7(2^3−1)=1, the elementary binomial lifting identity v_7(2^L_i−1)=1+v_7(L_i/3)=e_i applies (L_i is a multiple of 3). As v_7(L_i r)=−1 while W is integral, v_7(μ(r))=−e_i−1. The integers d,a ensure v_7(d−a r)≥−e_i. Thus

    v_7(T)=v_7((d−a r−μ(r))/7)=−e_i−2,

and subtracting floor(T) leaves the same valuation. In particular ρ≠0; its denominator divides 7 D_i M_i and has exactly e_i+2 powers of 7, hence divides D_(i+1) as defined. The common D_(i+1) has that same 7-valuation. For every other odd prime p dividing D_(i+1), p divides D_i or M_i, so ord_p(2) divides L_i. At higher powers of p, the order divides p^(h−1)ord_p(2), and therefore its 7-valuation remains at most e_i−1. Meanwhile ord_(7^(e_i+2))(2)=3·7^(e_i+1) by the same lifting identity. Taking the least common multiple yields v_7(L_(i+1))=e_i+1. This completes the induction.

The denominator and period bounds are uniform in n and k for each fixed block index. At block i the clock perturbation is a_i=−k+in=O_B(n); the renewal lemma takes a state perturbation of size O_B(n^(i+1)) to one of size O_B(n^(i+2)), since S<4D_i(A+H_b+10). For fixed B all D_i are constants, so (1) and S≤P hold for sufficiently large n simultaneously in the first B blocks. The initial wrap and these B blocks remain away from 1 up to time (B+1)n+3. This contradicts any return with k at most that time, proving the stated superlinear bound. The argument is effective: each D_i can be computed, and polynomial-vs-exponential comparisons give an explicit threshold.

## 4. Explicit 4n+2 bound at n≥8000

Take B=3 and k≤4n+3. For n≥8000, the initial wrap is valid and |a_i|≤5n for i=0,1,2, so take A=5n throughout. The first denominators and orders are

    D_0=7,              L_0=3
    D_1=343,            L_1=147
    D_2=49(2^147−1),    L_2=7203
    D_3=7 D_2(2^7203−1)/7^4.

Here L_2 follows because all non-7 prime-power factors of D_2 divide 2^147−1 and the 7-primary factor is 7^5. Thus D_1<2^9, D_2<2^153, D_3<2^7359. Use the following upper bounds on state perturbations:

| block i | H_b | H=A+H_b+10 upper bound | S upper bound | E upper bound |
|---|---:|---:|---:|---:|
| 0 | 5n | 11n | 2^9 n | 2^12 n² |
| 1 | 2^12 n² | 2^13 n² | 2^24 n² | 2^27 n³ |
| 2 | 2^27 n³ | 2^28 n³ | 2^183 n³ | 2^186 n⁴ |

In each row S<4D_i H and E=(A+n+2)S≤7n S; these imply the displayed estimates directly (for row zero, use 4·7·11=308 before rounding). Consequently the three right sides of (1) are respectively below

    2^31 n³,  2^205 n^5,  2^7729 n^7.

All are below P for n≥8000: at n=8000, 8000^7<2^91 and 7729+91<8000; the ratio 2^n/n^7 increases for n≥16 because 2·16^7>17^7. The same domination implies S≤P and A+n≤P. The hypotheses propagate by (2). After the initial n+3 steps, three full n-step blocks are safe, even if the proposed return time lies inside an earlier block. Thus k>4n+3, or m>4n+2. QED.

## 5. Reproduction and remaining obstacle

Run `python renewal_check.py` for exact integer checks of the denominators, order identities and bound constants, and independent literal recurrence regressions for (n,k)=(8000,8003),(8000,32003),(10002,40011). The code also compares each of the three n-bit wrap words and endpoints against the rational-moment renewal formula. These are tests; the universal proof is sections 1–4.

This source-level mathematical result excludes all fixed-linear costs asymptotically, substantially strengthening the checked near-2n bound. It leaves superlinear, potentially exponential, cost regimes open. The natural next target is a root-side cost upper bound or a mechanism controlling renewal when denominator sizes approach 2^n. Neither repeated finite parameter scans nor local restart suffix exclusions alone close this gap.