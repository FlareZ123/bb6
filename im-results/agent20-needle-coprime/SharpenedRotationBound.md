# Kernel-checked square-root cancellation predecessor bound

The cancellation family is defined by N=9^r, a=(N+5)/2, A=2^a, (A+3)P+N=A^(2r). The shifted feeder b=AP/2 is a terminal predecessor. Its second-level valuation-two/odd ancestor, when r=110j+50, is 55b=8AP+25. A legal incoming valuation w has exact parent equation b=(2^(w+1)+3)q+3*2^w+w+3 with q a natural.

## Main theorem

The fully checked arithmetic/source-equation result is

    (w+1)^2 < 16*r*a

for the original cancellation feeder at every r>=8 and the second-level target at every r=110j+50. It includes the derivation of the physical valuation range from the parent equation. It improves the earlier paper bound 64*r^2*a and decreases enumeration complexity from O(r*9^r) to O(sqrt(r)*3^r). For r<8, use the older cutoff or previously established exact inverse results. This is an unconditional bound on all integer solutions of the specified exact equations; it is not a global blank-orbit invariant or a nonhalting theorem for Space Needle.

## Proof mechanism

Put m=w+1, D=2^m+3 and use signed sparse power sums. Rotation by h reduces each c*2^e to c*(-3)^floor((e+h)/m)*2^((e+h) mod m), giving the same residue as 2^h times the original sum. A sufficiently large empty arc puts the rotated integer below D in absolute value; divisibility then forces exact zero.

A three-term form follows from (A+3)AP=A^(2r+1)-NA. In particular, for F=c AP+C, D|F implies D|c*2^((2r+1)a)+(C-cN)*2^a+3C. With raw coefficient mass <2^H and maximum exponent E, the rotated mass is <2^(H+2*ceil(E/m)). If m>=3*(H+2*ceil(E/m)), divisibility forces a collision between binary-valuation-adjusted exponent residues of the three terms, provided all coefficients are nonzero. Independently, if both nonconstant exponents are >=a, divisibility in that range forces 3^floor(a/m) to divide the constant coefficient. This generic theorem is reusable beyond cancellation families.

For m^2>=16ra, m<=a, the coefficient mass bounds at r>=8 guarantee the three-term condition with H=8r. If floor(a/m)>=8r, the divisibility by a large power of three contradicts the nonzero constant size. Otherwise ceil(a/m)<=8r, and the original 2r-term geometric sparse form has sufficiently large gap: its constant is divisible by 3^(2r+floor(a/m)-1). For the first target C=5-2m, N|C is impossible for m<a, and m=a is excluded by an exact geometric evaluation. For the second C=325-110m, N|C forces m=(N+65)/22, C=-5N and floor(a/m)>=2, contradicting divisibility by 3N. The high side m>a uses an isolated three-term rotation when m-a>=2B (B=12r+2) and an odd geometric remainder when 1<=m-a<2B.

## Reproduction

Lean 4.36.0-rc2, no Mathlib, compile in this directory with LEAN_PATH=. :

    export LEAN_PATH=.
    for f in RotationCore RotationValuation RotationFar RotationSparse RotationNear CancellationRotationBound; do
      lean -o "$f.olean" "$f.lean" || exit 1
    done

The final four theorems first_cutoff, second_cutoff, first_source_equation_cutoff and second_source_equation_cutoff in namespace NeedleRotation.Cancellation all report exactly [propext, Classical.choice, Quot.sound], no sorryAx. The earlier modules give generic rotation congruence, gap existence, mass, resonance, far-high, sparse and near-high lemmas. This is a locally kernel-checked source-equation proof; an import adapter into the original Cryptids machine development has not yet been checked.

## Modular-only complete finite inverse trees

The [resonance audit](resonance_reverse_audit.cpp) combines the [affine cutoff](AffineRotationCutoff.md) with the generic three-term collision theorem. It handles 2b=(c AP+d)/L with c a power of 2, d even and L odd coprime to 3, as obtained on any reverse branch. Necessary exceptions above its ordinary cutoff are divisors of the adjusted exponent differences, intersected with the earlier affine cutoff. It checks the exact congruence modulo L*(2^m+3) by the recurrence for P; it never materializes AP. The positive quotient >=3 and nonroot property are checked via AP>2^(2ra-1). Strict backward decrease follows from the exact legal parent equation. Build with g++ -O3 resonance_reverse_audit.cpp -lgmpxx -lgmp -o resonance_reverse_audit and run with the index r.

Exact local output:
```
r=7 bitsUpper=33480818 oldCut=32174 ordinary=14714 resonantExtras=6 sieve=11941 sparse=2776 exact=3 parents=3,4,
r=7/3 bitsUpper=33480818 oldCut=32234 ordinary=14720 resonantExtras=0 sieve=11755 sparse=2964 exact=1 parents=
r=7/4 bitsUpper=33480818 oldCut=32249 ordinary=14723 resonantExtras=1 sieve=9339 sparse=5382 exact=3 parents=
nodes=3 leaves=2 edges=2 cutoffFailure=0
r=8 bitsUpper=344373808 oldCut=108703 ordinary=46903 resonantExtras=2 sieve=37846 sparse=9058 exact=1 parents=
nodes=1 leaves=1 edges=0 cutoffFailure=0
r=9 bitsUpper=3486784446 oldCut=364802 ordinary=148658 resonantExtras=2 sieve=120174 sparse=28485 exact=1 parents=
nodes=1 leaves=1 edges=0 cutoffFailure=0
```

The r=9 tree is newly exhausted; r=7 and 8 reproduce prior exact results. These finite complete root exclusions use the paper-level affine extension and the established original-source inverse correspondence. They are not yet original-source Lean finite certificates. The universal arithmetic cutoff and finite audits do not remove the unbounded cancellation parameter or the regular sector.
