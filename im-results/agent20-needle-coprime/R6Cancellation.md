# The sixth Space Needle cancellation feeder has no accelerated parent

**Status:** exhaustive exact-integer computation; the general polynomial identity is Lean 4.36.0-rc2 kernel-checked. The full 3,188,676-valuation statement is not yet a Lean theorem. This is intermediate holdout research, not a proof of Space Needle nonhalting or BB(6).

## Claim and source boundary

In the pinned original Space Needle single-counter acceleration the blank start is N(1), every successful transition strictly increases the numeric counter, and an immediate predecessor of a target with shifted counter x=d+2 must satisfy

\[
  D_u(2p+3)=N_u,\quad
  D_u=2^{u+1}+3,\quad N_u=2x+3-2u.
\]

This is the exact inverse equation in [NeedleGeneralInverse.lean](NeedleGeneralInverse.lean), bridged to the original machine by [NeedleRootDecisionSource.lean](NeedleRootDecisionSource.lean).

For cancellation parameter r=6, set
\[
 v=(9^6+3)/2=265722,\quad K+1=6(9^6+5)=3188676,
\]
\[
 q=\frac{2^K-3\cdot2^v-v-3}{2^{v+1}+3},\quad
 x=2^v(2q+3).
\]
The division is exact and q is nonnegative; x has exactly K binary digits, so x is strictly below 2^K. Its counter d=x-2 is a legal synthetic terminal feeder of 2^K-2. A predecessor of d must have some valuation u with 2^u<=parent counter+2<x, hence u<K. The audit conservatively checks every 0<=u<=K.

Every candidate fails the necessary condition D_u divides N_u. Thus d has no incoming accelerated edge. It is also distinct from the genuine initial N(1), so it is absent from the authentic blank-root orbit. This excludes a single candidate feeder, leaving the infinite terminal existential open.

## Complete finite audit

| Check | Valuations | Result |
| --- | ---: | --- |
| Conservative full interval | 3,188,676 | u=0,...,3,188,675 |
| Small-prime modular exclusions | 2,579,052 | impossible |
| Low survivors 0<=u<=v | 50,877 | zero divisible |
| High survivors v<u<=K | 558,747 | zero divisible |
| Incoming parents | **0** | exact finite arithmetic |

Among the 1,229 primes up to 10,000, exactly 685 provided useful witnesses (p,L,e) with L=ord_p(2) and 2^e=-3 mod p. For u congruent to e-1 mod L, p divides D_u; if p does not divide N_u, then D_u cannot divide N_u. Both programs compute these witnesses directly using integer modular arithmetic.

## Lean-proved polynomial and low-valuation acceleration

Let a=v+1=265723, A=2^a, and recursively define the integer polynomial

\[
 P_0(A)=0,\qquad P_{r+1}(A)=A^2P_r(A)+9^r(A-3).
\]
The all-integer, all-parameter identity
\[
 (A+3)P_r(A)+9^r=A^{2r}
\]
is proved in [CancellationSparsePolynomial.lean](CancellationSparsePolynomial.lean), theorem CancellationSparse.exact. Local Lean 4.36.0-rc2 kernel verification printed only [propext, Classical.choice, Quot.sound]. In this family P_r(A)=2q+3, giving the exact identity
\[
  2x=A P_r(A),\qquad N_u=A P_r(A)+3-2u.
\]
This reduces the giant target calculation to six modular polynomial recurrences. For each u<=v, write a=t(u+1)+s, 0<=s<u+1; the congruence 2^(u+1)=-3 mod D_u yields
\[
 A\bmod D_u=(-3)^t2^s\bmod D_u.
\]
The standalone [GMP C++ program](r6_low_polynomial.cpp) checks the resulting polynomial modulo D_u at all 50,877 surviving low valuations, validating every 5,000th calculation against direct full-integer division. It independently constructs the feeder from P_6 and checks the terminal equation and bit length.

## Exact signed-base test for the high interval

For u>v let B=2^(u+1) and expand N_u into base-B digits d_i. There are at most twelve digits, each in [0,B). Define S_u=sum_i d_i(-3)^i. Then S_u=N_u modulo B+3, and |S_u|<B*3^12. Since B>=2^(v+2)>3^13, if |S_u|=k(B+3) then k<3^12 and 3k<B. Divisibility is therefore **equivalent** to

\[
 |S_u|=\lfloor |S_u|/B\rfloor(B+3).
\]

The independent [Python high-valuation audit](r6_high_parent_audit.py) performs this exact comparison for all 558,747 high survivors and finds zero divisible cases. Its original run completed in approximately 298 seconds. Python's arbitrary-precision integers supply the exact bits and arithmetic. No probabilistic correctness assumption is used.

## Reproduction and scope

Execute the Python 3 standard-library high audit and the C++17 low audit linked above. Compile the latter against GMP and GMPXX. The two programs recompute the sieve separately. The low program includes direct-integer cross-checks; a second C++ low implementation using a precomputed target independently reproduced the 50,877 zero-hit result. These are reproducible computations, not yet a complete Lean finite certificate.

Formalizing the compressed finite zero-hit certificate and applying the already source-checked finiteParents_spec / exact_root_target bridge is the next step for a fully original-source kernel-checked r=6 root exclusion.

The r=5 computation is [Agent 48's earlier audit](../agent48-space-needle/R5-CANCELLATION-ROOT-AUDIT.md). The r=1,...,4 cancellation-source exclusions have Lean certificates. The r=5 and r=6 no-parent claims remain computational, and all r>=7 and the square-root-bounded terminal sector remain open.
