# Asymmetric sparse rotations for cancellation feeder ancestry

Agent 20, 2026-11-28. Intermediate arithmetic research; no Space Needle or BB(6) verdict.

Write N=9^r, a=(N+5)/2, A=2^a, and (A+3)P=A^(2r)-N. The exact shifted initial cancellation feeder satisfies 2b=AP. The previous cutoff for an incoming valuation m=w+1 was m²<16ra for r>=8. The new bound is

    4m² < 13(r+1)a.

It also applies to the existing second-level target 55b=8AP+25, r=110j+50. The admissible interval length falls by at least 52% for r>=8. At r=13, 16,258,968 becomes 7,604,436.

## Argument

For a signed term c*2^e and D=2^m+3, shift by 2^h and reduce exponent modulo m, replacing its coefficient by c*(-3)^floor((e+h)/m). If |c|<2^H, its absolute value after rotation is <2^(m-2) when the residue plus the individual width H+8*ceil(ceil(e/m)/5)+2 is <m. This uses 3^5<2^8. A union of three forbidden cyclic intervals has size at most the SUM of their widths. Thus a good common shift exists when that sum is <m, rather than requiring three times the largest width.

The three-term necessary congruence is D | c*2^((2r+1)a)+(C-cN)*2^a+3C. Its rotated sum is smaller than D, hence zero. The two nonconstant terms are multiples of 3^floor(a/m), so this power must divide 3C. For the relevant small coefficients (|c|<64, 0<|C|<=110m+325), the old cutoff implies floor(a/m)>=8r and the improved cutoff's negation guarantees enough width. The contradiction follows from 0<|3C|<2^(4r+8)<=3^floor(a/m).

The exact local Lean modules AsymmetricShift.lean, AsymmetricRotation.lean, CancellationNarrow.lean (commit 05b26781; widened c<64 in ccafcffb) compiled against verbatim needed declarations of RotationCore and RotationValuation using Lean 4.36.0-rc2, standard axioms only. The full equation-source closure including CancellationNarrowSource.lean is queued in [46114510013](https://github.com/FlareZ123/bb6/actions/runs/46114510013); this is not an unchanged Cryptids source audit.

## Valuation-four predecessor family

For r=1 mod 3 the initial feeder admits a valuation-four predecessor. Its equation is 70b+160=32AP. Any next incoming m obeys D | 32AP+15-70m. Throughout 1<=m<=a, N cannot divide C=15-70m: otherwise 70m-15=N*t, 0<=t<=35. Since N mod70 is 9 or 51, t=45 mod70, impossible. FourResidue.lean is locally kernel-checked. CancellationWide.lean and CancellationFourNarrow.lean adapt the previous cutoff and then the asymmetric bound to this family; full closure not yet certified. These files are in ccafcffb.

## Computational status

The previous run's r=12 full exact scan succeeded ([46102294468](https://github.com/FlareZ123/bb6/actions/runs/46102294468)): all 5,207,037 candidates rejected; no parents. This is recorded in ../agent48-needle-r10/README.md without re-running it.

For r=13, needle13.cpp adapts the existing exact modular/GMP enumerator with a pointwise asymmetric-rotation prefilter, expanded prime sieve and bounded exact power caching. The local separately formatted implementation tested m=1..100000: 81,355 sieve rejects, 18,644 sparse rejects, one full check and valuation-four parent. A direct independent exact recurrence checked the child for m=1..500 with no parents. These are partial checks, not complete trees. The existing manual workflow now runs four disjoint r13 root intervals, [46114677898](https://github.com/FlareZ123/bb6/actions/runs/46114677898), queued at checkpoint. No r13 exclusion claimed.

The entire cancellation family still contains arbitrarily deep prepared ancestry. Finite reverse trees and tighter per-node cutoffs do not decide blank-root reachability uniformly.
