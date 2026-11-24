# Affine reverse-history rotation cutoff and complete seventh-feeder exclusion

This extends [RotationCutoff.md](RotationCutoff.md) to every fixed reverse history satisfying the explicit hypotheses below. The cutoff is presently a paper proof; the finite checks are exact GMP integer calculations, not a Lean certificate.

Let N=9^r, a=(N+5)/2, A=2^a, P=(A^(2r)-N)/(A+3), M=2ra, and write a shifted target as 2b=(c AP+d)/L, where c is a positive power of two, d even, L positive odd and coprime to 3. Suppose 3≤b≤AP/2. For m=w+1≥1 an incoming edge requires

    L(2^m+3) | c AP+C,   C=d+L(5-2m),

with quotient odd and ≥3. The new shifted state satisfies

    2b_new=(2^m c AP+2^m C)/(L(2^m+3)).

The hypotheses on c,d,L are invariant under this inverse step, and b decreases. In particular m≤M for every ancestor. This is the exact original high-level inverse equation, not a relaxed inverse relation.

Put X=|d|+L(2M+5)+cN+1, H=bitlength(X)+4, B=H+4r+4.

**Low side.** For m≤a put k=ceil(a/m). Every rotated coefficient of c AP is at most c 3^(2rk) in absolute value, and the constant is at most |C|. Their total mass is <2^(H+4rk+2r). If

    m ≥ (2r+1)(H+4rk+2r),

a cut exists avoiding the last H+4rk+2r-1 exponent positions. A multiple of D=2^m+3 then rotates to zero. Every nonconstant polynomial coefficient is divisible by N, since floor((la+h)/m)≥l for exponent la; hence N|C. Because 2L is invertible modulo N and a<N, there is at most one exception in [1,a], namely m=(d+5L)/(2L) mod N. The inequality is monotone in m, so binary search finds the final necessary cutoff.

**High side.** Assume a≥(4r+1)B and C-cN is nonzero for m>a. (In this audit C is odd, and c even except at the original target, where C-cN<0.) Multiplication by A+3 gives the three-term necessary condition

    D | c*2^((2r+1)a)+(C-cN)*2^a+3C.

For m≥a+2B, both arcs between the residues 0 and a have length ≥2B. The third term can split at most one arc. There are two gaps of size ≥B isolating a singleton term. Rotation gives mass <2^B: the leading coefficient is bounded by c 3^(2r+1)<2^(H+4r-2), the other two by 2^(H-2). Thus the rotated sum has absolute value <D and is nonzero modulo 2^B. Contradiction.

For m=a+s, 1≤s<2B, multiplying the original expression by 2^(2rs) gives the congruent integer

    R=cN sum_{l=1}^{2r}2^((2r-l)s)+C2^(2rs).

The sum is odd, so R≠0 when 2rs>v2(c). Its magnitude is <2^(B+2rs)≤2^m<D by the hypothesis on a. The only near-high exceptions to check explicitly have 2rs≤v2(c).

These bounds are conditional only on explicitly computed arithmetic parameters. The program aborts with a cutoff failure if the high-side size assumption fails. The denominator test is exact, including the factor L and quotient positivity; prime and sparse tests only eliminate necessary-condition failures.

## Reproducible complete tree at r=7

Build: g++ -O3 affine_reverse_audit.cpp -lgmpxx -lgmp -o affine_reverse_audit

Run: ./affine_reverse_audit 7

    r=7 bits=33480818 B=63 cutoff=32174 extra=2391487, sieve=26157 sparse=6015 exact=3 parents=3,4,
    r=7/3 bits=33480818 B=67 cutoff=32234 extra= sieve=25783 sparse=6450 exact=1 parents=
    r=7/4 bits=33480818 B=68 cutoff=32249 extra= sieve=20503 sparse=11743 exact=3 parents=
    nodes=3 leaves=2 edges=2 rootReached=0 cutoffFailure=0

The complete predecessor tree of the seventh cancellation feeder has exactly three vertices: the feeder and its valuation-three and valuation-four parents. Neither parent has any predecessor, and none is the authentic shifted blank-entry state 3. Therefore the feeder is not reached from the genuine blank orbit, using the established exact original-source inverse correspondence. This finite exclusion and the eighth-feeder no-parent check do not settle all r or the Space Needle machine.

The reusable local Lean module RotationCore.lean kernel-checks the rotation congruence, mass bound, vanishing under a sufficient gap, and a general existence-of-good-shift lemma using n+1 equally spaced candidate cuts. The complete affine coefficient estimates, high-side singleton exclusion, and finite GMP audit are not yet composed into a Lean original-source theorem.
