# Asymmetric sparse rotations for cancellation feeder ancestry

Agent 20, 2026-11-28. Intermediate arithmetic research; no Space Needle or BB(6) verdict.

Write N=9^r, a=(N+5)/2, A=2^a, and (A+3)P=A^(2r)-N. The exact shifted initial cancellation feeder satisfies 2b=AP. The previous cutoff for an incoming valuation m=w+1 was m²<16ra for r>=8. The new bound is

    4m² < 13(r+1)a.

It also applies to the existing second-level target 55b=8AP+25, r=110j+50. The admissible interval length falls by at least 52% for r>=8. At r=13, 16,258,968 becomes 7,604,436.

## Argument

For a signed term c*2^e and D=2^m+3, shift by 2^h and reduce exponent modulo m, replacing its coefficient by c*(-3)^floor((e+h)/m). If |c|<2^H, its absolute value after rotation is <2^(m-2) when the residue plus the individual width H+8*ceil(ceil(e/m)/5)+2 is <m. This uses 3^5<2^8. A union of three forbidden cyclic intervals has size at most the SUM of their widths. Thus a good common shift exists when that sum is <m, rather than requiring three times the largest width.

The three-term necessary congruence is D | c*2^((2r+1)a)+(C-cN)*2^a+3C. Its rotated sum is smaller than D, hence zero. The two nonconstant terms are multiples of 3^floor(a/m), so this power must divide 3C. For the relevant small coefficients (|c|<64, 0<|C|<=110m+325), the old cutoff implies floor(a/m)>=8r and the improved cutoff's negation guarantees enough width. The contradiction follows from 0<|3C|<2^(4r+8)<=3^floor(a/m).

The exact local Lean modules AsymmetricShift.lean, AsymmetricRotation.lean, CancellationNarrow.lean (commit 05b26781; widened c<64 in ccafcffb) compiled against verbatim needed declarations of RotationCore and RotationValuation using Lean 4.36.0-rc2, standard axioms only. The full equation-source closure including CancellationNarrowSource.lean passed [46114510013](https://github.com/FlareZ123/bb6/actions/runs/46114510013); this is not an unchanged Cryptids source audit.

## Valuation-four predecessor family

For r=1 mod 3 the initial feeder admits a valuation-four predecessor. Its equation is 70b+160=32AP. Any next incoming m obeys D | 32AP+15-70m. Throughout 1<=m<=a, N cannot divide C=15-70m: otherwise 70m-15=N*t, 0<=t<=35. Since N mod70 is 9 or 51, t=45 mod70, impossible. FourResidue.lean is locally kernel-checked. CancellationWide.lean and CancellationFourNarrow.lean adapt the previous cutoff and then the asymmetric bound to this family; the full equation-source closure passed [46115421383](https://github.com/FlareZ123/bb6/actions/runs/46115421383). These files are in ccafcffb.

## Computational status

The previous run's r=12 full exact scan succeeded ([46102294468](https://github.com/FlareZ123/bb6/actions/runs/46102294468)): all 5,207,037 candidates rejected; no parents. This is recorded in ../agent48-needle-r10/README.md without re-running it.

For r=13, needle13.cpp adapts the existing exact modular/GMP enumerator with a pointwise asymmetric-rotation prefilter, expanded prime sieve and bounded exact power caching. The local separately formatted implementation tested m=1..100000: 81,355 sieve rejects, 18,644 sparse rejects, one full check and valuation-four parent. A direct independent exact recurrence checked the child for m=1..500 with no parents. These are partial checks, not complete trees. The existing manual workflow now runs four disjoint r13 root intervals, [46114677898](https://github.com/FlareZ123/bb6/actions/runs/46114677898), running at checkpoint. No r13 exclusion claimed.

The entire cancellation family still contains arbitrarily deep prepared ancestry. Finite reverse trees and tighter per-node cutoffs do not decide blank-root reachability uniformly.

## All-depth quadratic-or-divisors theorem

Every legal shifted predecessor history from a cancellation feeder has the form
`2Lb=2^x AP+d`, with L odd, d even, x the sum of incoming m values, and
b<2^(2ra). The exact update is x'=x+m, L'=L(2^m+3),
d'=2^m(d+L(5-2m)). GenericHistory.lean proves this representation, including
coverage of all unannotated legal inverse histories, and preserves the physical
bound. No arbitrary depth limit is introduced.

For a nonroot node (x>0), set E=(2r+1)a, M=2ra, C=d+L(5-2m), and
choose H1=x+1, H2=bitlength(|d|+L(2M+5)+2^x N),
H3=bitlength(3(|d|+L(2M+5))). Every legal incoming m satisfies

    5m² <= 5(H1+H2+H3+22)m+8(E+a)
    or m | E+x-a
    or m | E+x
    or m | a.

The proof uses the same asymmetric rotation, but replaces the constant
3-adic obstruction by binary-valuation resonance. The adjusted residue of
the leading term is E+x, and both other coefficients are odd (because L is
odd and d even). If the three adjusted residues are distinct, the unique
minimum binary valuation makes the rotated sum nonzero. The individual
widths give the explicit quadratic bound by 3^5<2^8.

AsymmetricResonance.lean, GenericCutoff.lean, GenericAffineSource.lean and
GenericHistory.lean passed local Lean 4.36.0-rc2 with standard axioms, using
the needed locally compiled arithmetic lemmas. Full dependency closure
[46115991655](https://github.com/FlareZ123/bb6/actions/runs/46115991655)
is queued. This is an arithmetic source-equation theorem, not a fresh
unchanged upstream Cryptids audit.

## Exact sparse quotient and positivity for enormous exceptions

The header needle-sparse-exact.hpp implements a lossless test of
`L(2^m+3) | sum c_i 2^e_i` with signed sparse terms. For e_i=q_i m+s_i
reduce each term to c_i(-3)^q_i 2^s_i. Let S be the resulting sum, T the
coefficient absolute mass and Q the sum of each reduced term truncated
after division by 2^m. If 3T<2^m, any exact quotient k=S/(2^m+3) satisfies
|k-Q|<=number of terms, so only that short integer interval is tested.
The signed sparse equality/sign algorithm repeatedly carries floor
quotients over exponent gaps, retaining a flag for nonzero lower residue.
It never materializes the intervening zeros. If the mass condition fails,
dense arithmetic is used, with m already bounded by the mass bitlength.

Once the reduced quotient k is known, recover the original quotient modulo
L using the division-free geometric identity
`(X^q-Y^q)/(X-Y)=G_q(X,Y)` and
`G_(u+v)=X^u G_v+Y^v G_u`, with X=2^m,Y=-3.
This works even when L shares prime factors with 2^m+3. Positivity of
the odd cofactor is tested exactly by the sign of the numerator minus
3L(2^m+3). For large m this eliminates modulus-sized memory allocation.
The cost of coefficient powers of three depends on max(e_i/m), so this
routine targets the sparse high exceptions, not the small-m interval.

Local test-sparse-exact.cpp passed 20,000 random signed sums compared
to GMP dense exact arithmetic, injected nonzero multiples, 4,000
feeder cases, and tests with exponents at least one trillion. These are
algorithm tests, not a finite cancellation-tree certificate. Source commits
ee764a8b and 3d2281fe.

## Faster paired exact scan

needle-pair.cpp (eaa4ebe7) shares the two reduced powers between root
and valuation-four child. It generates prime-factor witnesses up to 10^7
by exact multiplicative orders and discrete logs, and tests the lifted
p^2 condition for p|L=35. The child-only local scan uses the same code
with root disabled explicitly. Paired run m=1..100000, p<=10^6:
root 87,463 sieve, 12,536 sparse, one exact parent (w=4);
child 44,431 sieve, 42,857 lifted, 12,712 sparse, zero exact hits.
Child-only m=100001..150000: 23,156 sieve, 21,429 lifted, 5,415 sparse,
zero hits. Child-only m=150001..650000: 231,442 sieve, 214,286 lifted,
54,272 sparse, zero hits. Child-only m=650001..1150000: 231,522 sieve,
214,285 lifted, 54,193 sparse, zero hits. These are disjoint, contiguous
intervals. No claim for the unscanned suffix yet.
