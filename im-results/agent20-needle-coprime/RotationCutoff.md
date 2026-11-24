# Rotated sparse-remainder cutoff for cancellation ancestry

**Status:** paper-level universal arithmetic proof, with reproducible exact GMP finite checks. The cutoff and source composition are not yet Lean-checked. The eighth cancellation feeder has no incoming high-level edge; the seventh has precisely two. These results use the existing exact source inverse equation and the new cutoff. The unbounded terminal exponent and authentic blank-root decision for Space Needle remain open.

## Theorem

Let r>=4, N=9^r, a=(N+5)/2, A=2^a, P_0=0, P_(i+1)=A^2 P_i+9^i(A-3), P=P_r(A). Consider either shifted target b=d+2:

- Cancellation terminal feeder b=AP/2.
- Second-level valuation-two/odd ancestor b=(8AP+25)/55, for r=110j+50, j>=0.

**Every incoming high-level predecessor valuation w satisfies (w+1)^2 < 64 r^2 a.** Thus the complete candidate search is O(r*3^r), rather than O(r*9^r). In particular, the theorem closes the large low-side middle-remainder gaps and entire high side of both earlier inverse searches.

The exact inverse equation is b=(2^(w+1)+3)q+3*2^w+w+3 for q>=0. Write m=w+1, D=2^m+3. It implies D | 2b+5-2m, hence D | F=c AP+C, where (c,C) is (1,5-2m) or (16,325-110m), respectively. The second implication multiplies by 55 and is only used as necessary. The recurrence gives

    AP=sum_{l=1}^{2r} (-3)^(2r-l) A^l,
    (A+3)AP=A^(2r+1)-N A.

Both targets satisfy b<2^(2ra), and every legal parent has b>2^m. Thus only 1<=m<=2ra need be considered.

## Rotated remainders

For a sum F=sum_i c_i 2^e_i and 0<=h<m, write q_i=floor((e_i+h)/m), s_i=(e_i+h) mod m, R_h=sum_i c_i(-3)^q_i 2^s_i. Since 2^m=-3 mod D, R_h=2^h F mod D. If D|F then D|R_h. If the sum of absolute reduced coefficients is strictly less than 2^B, and a circular gap of length at least B occurs among exponent residues, rotate the first residue after the gap to zero. All s_i<=m-B, so |R_h|<2^m<D. Divisibility then forces R_h=0.

Three-term variant: if two circular gaps have length at least B, among three monomials there is a singleton residue with both adjacent gaps at least B. If two residues coincide choose the other one; otherwise any two gaps in a three-vertex circle share a singleton vertex. Rotate it to zero. Its nonzero coefficient has absolute value <2^B; other terms are divisible by 2^B. Thus R_h!=0, a contradiction.

## Entire low side above the cutoff

Suppose m<=a and m^2>=64r^2 a. Let k=ceil(a/m), so 1<=k<=2a/m. The 2r+1 exponents of F (including zero) have a circular gap of length at least m/(2r+1); distinct residues' circular gaps sum to m. For any h<m, the absolute l-th reduced coefficient is

    c*3^(2r-l+floor((la+h)/m)) <= 16*3^(2rk) < 2^(4+4rk),

since floor((la+h)/m)<=lk. The constant has |C|<64N<2^(6+4r). Thus the sum of all absolute reduced coefficients is strictly below

    (2r+1)*2^(6+4rk) <= 2^(6+4rk+2r) <= 2^(9rk),

using 2r+1<=2^(2r) and 6+2r<=5r<=5rk for r>=2. Also

    m/(2r+1) >= m/(3r) >= (64/3)*r*a/m > 18*r*a/m >= 9rk.

The gap device with B=9rk forces R_h=0 if D|F.

But a>=m implies floor((la+h)/m)>=l, so all polynomial coefficients in R_h are divisible by N=3^(2r). Its constant contribution is C*2^h. Therefore R_h=0 implies N|C.

For the first target and m<a, 0<|5-2m|<N, impossible. At m=a, all polynomial exponents reduce to h, every signed coefficient is positive N, C=-N, and R_h=(2r-1)N*2^h!=0.

For the second target, N|C implies N|(22m-65), as N is coprime to 5. Write 22m-65=zN; since 1<=m<=a, -N<22m-65<11N, so 0<=z<=10. The progression r=110j+50 yields N=1 mod22 (9^5=1 mod22); hence z=1 mod22. Thus z=1, m=(N+65)/22, C=-5N, and 2m<=a (already true for N>=81). Now every polynomial coefficient is divisible by 3N: floor((la+h)/m)>=2l, l>=1. But -5N*2^h is not divisible by 3N. This also prevents R_h=0.

## Entire high side

Set B=6r+16. For r>=4, a>=(4r+1)B: at r=4, 3283>=680, and a_(r+1)=9a_r-20>=8a_r while (4r+5)(6r+22)<2(4r+1)(6r+16).

### Far high side m>=a+2B

Multiplying F by A+3 gives the necessary divisibility

    D | G = c*2^((2r+1)a) + (C-cN)*2^a + 3C.

All three coefficients are nonzero (C<0). On the physical range m<=2ra, |C|<128*2^r N<2^(7+5r), using 2r+1<=2^r, a<=N, and 110m+325<128*2^r N. Also |C-cN|<2^(8+5r). For h<m the middle quotient is at most 1, leading quotient at most 2r+1, constant quotient zero. Thus the absolute reduced coefficients are bounded by 2^(4r+6), 2^(10+5r), 2^(9+5r), with sum <2^(12+5r)<2^B.

The residues 0 and a are separated by arcs of lengths a and m-a, each at least 2B. The third residue can subdivide at most one arc, which then has a gap of length at least B; the other arc remains unsplit. There are therefore two gaps of length at least B. The three-term singleton device prevents D|G.

### Near high side m=a+s, 1<=s<2B

Since 2^s A=-3 mod D, multiply the original F by 2^(2rs) and reduce:

    2^(2rs) F = R mod D,
    R = cN sum_{l=1}^{2r} 2^((2r-l)s) + C*2^(2rs).

The geometric sum is odd and strictly less than 2^(2rs). The first term has exact binary valuation 0 or 4, respectively; the second is divisible by 2^(2rs), with 2rs>=8. Hence R!=0. The previous coefficient bounds give cN+|C|<2^B, so |R|<2^(B+2rs)<=2^m, since s<2B and a>=(4r+1)B. Therefore D cannot divide R. The low-side proof includes m=a whenever it satisfies the cutoff.

Combining both sides proves the claimed inequality. QED (paper proof).

## Exact finite checks: first cancellation target

[cancellation_rotate_audit.cpp](cancellation_rotate_audit.cpp) checks all 1<=m<=floor(sqrt(64r^2a-1)), intersected with m<a (the cutoff is strictly below a for every reported r). It uses necessary small-prime divisibility, the three-term identity, then the original polynomial recurrence modulo D for every three-term survivor, avoiding false parents from the factor A+3. The odd quotient is positive and at least 3 since b is far larger than every checked denominator and AP+5-2m is odd. Compile with g++ -O3 cancellation_rotate_audit.cpp -lgmpxx -lgmp -o cancellation_rotate_audit and pass r.

| r | max m | prime rejections | sparse rejections | full checks | legal valuations w |
|---:|---:|---:|---:|---:|---|
| 4 | 1833 | 1504 | 328 | 1 | 4 |
| 5 | 6873 | 5554 | 1319 | 0 | none |
| 6 | 24743 | 19976 | 4767 | 0 | none |
| 7 | 86600 | 70463 | 16135 | 2 | 3,4 |
| 8 | 296916 | 239949 | 56967 | 0 | none |

The r=4,5,6 rows are regressions, not new research claims. The r=7,8 complete finite inverse rows are new within the inspected repository. The r=8 target exceeds 3, the authentic shifted blank start, so its empty incoming list implies its nonreachability under the exact original inverse correspondence. Both r=7 branches require analysis. No new Lean-accepted original-source certificate is asserted.

## Next mathematical step

The remaining range is exponentially smaller but still unbounded in r. The same sparse method can extend to fixed reverse histories: if 2b=(c AP+d)/L, an incoming valuation m-1 gives

    2b_new = (2^m c AP+2^m(d+L(5-2m)))/(L(2^m+3)).

Here L remains odd and coprime to 3. The low-side rotated nonvanishing argument fails only at the unique solution of N|(d+L(5-2m)) modulo N, since 2L is invertible modulo N. The high-side three-term method can use coefficient bounds depending on the fixed history. Formalizing this generalization and using it to close both seventh-feeder branches is the next useful action. No whole-machine halt/nonhalt result or BB(6) value follows.
