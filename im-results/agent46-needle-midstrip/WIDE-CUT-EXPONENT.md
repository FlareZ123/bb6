# Wider cut-exponent exclusion for the Space Needle cancellation feeder

**Status:** the all-r arithmetic and original-source Lean drafts are committed in CancellationMidBandResidue.lean and CancellationMidBandSource.lean. They are not yet locally preflighted or re-run through pinned-source CI. This is an intermediate research result, not a BB(6) decision.

## Theorem

Write
\[
a_r=\frac{9^r+5}{2},\qquad
d_r=1+\lfloor\log_2(3^{2r-1})\rfloor,
\]
and, for \(s\ge1\),
\[
c_r(s)=a_r+s-s\left\lfloor\frac{a_r+s-1}{s}\right\rfloor
      =((a_r+s-1)\bmod s)+1.
\]
Define the cut exponent
\[
E_r(s)=2a_r-(2r-2)s-c_r(s).
\]
Let \(P_0(A)=0\) and \(P_{r+1}(A)=A^2P_r(A)+9^r(A-3)\).

**Theorem (wide cut-exponent exclusion).** For every \(r\ge2\), if
\[
\boxed{
d_r\le s,\qquad
a_r\le(2r-1)s,\qquad
c_r(s)\ge d_r,\qquad
E_r(s)\ge d_r+1,
}
\tag{W}
\]
then
\[
\boxed{
2^{a_r+s}+3\nmid
\left(2^{a_r}P_r(2^{a_r})+3-2(a_r-1+s)\right).
}
\tag{1}
\]
Thus no cancellation-form immediate predecessor of the synthetic feeder can have valuation \(u=a_r-1+s\) in this range. The source-linked Lean draft lifts the arithmetic statement through the exact inverse-parent characterization of the original Space Needle transition.

The earlier residue-cut theorem used the stronger condition \(rs\le a_r\) in place of \(E_r(s)\ge d_r+1\). The new condition strictly enlarges the checked finite ranges and retains the old condition as a corollary. Indeed, \(c_r(s)\le s\), so \(rs\le a_r\) implies
\[
E_r(s)\ge 2a_r-(2r-1)s\ge s.
\]
Also \((2r-1)d_r<a_r\), hence the case condition \(a_r\le(2r-1)s\) forces \(s\ge d_r+1\). Therefore \(E_r(s)\ge d_r+1\).

## The new coefficient estimate

Put \(n=3^{2r-1}\) and \(d=d_r\). The already established logarithmic gap is
\[
2^d\ge n+5.
\tag{2}
\]
Suppose \(c=c_r(s)\ge d\) and \(E=2a_r-(2r-2)s-c\ge d+1\). Since
\[
2a_r=9^r+5=3n+5,
\]
we obtain
\[
d+1+(2r-2)s+c\le3n+5.
\]
As \(c\ge d\ge1\) and \(2r-2\ge2\),
\[
2s\le(2r-2)s\le3n+2.
\]
Consequently
\[
9^r+2s=3n+2s\le6n+2
<8n+40
\le8\cdot2^d
=4\cdot2^{d+1}
\le4\cdot2^E.
\tag{3}
\]
This is the only new estimate needed in the earlier residue-cut proof. It replaces the old estimate \(9^r+2s<4\cdot2^s\), which had required \(rs\le a_r\).

## Proof of the divisibility exclusion

Fix \(r,s\) satisfying (W). Abbreviate
\[
a=a_r,\quad A=2^a,\quad t=2^s,\quad
T=t^{2r},\quad S=\sum_{j=0}^{2r-1}t^j,\quad
n=3^{2r-1},\quad u=a-1+s.
\]
Set
\[
B=At=2^{a+s},\quad D=B+3,\quad M=B,\quad
N=AP_r(A)+3-2u.
\]
The recurrence for \(P_r\) supplies the exact certificate identity
\[
TAP_r(A)=3^{2r}S+D\,C
\tag{4}
\]
for a natural number \(C\). This is the existing cert_identity lemma.

Assume for contradiction that \(D\mid N\). Let
\[
Y=3^{2r}S,\qquad U=(2u-3)T,\qquad Q=U-Y.
\]
Since \(2u-3=9^r+2s=3^{2r}+2s\) and \(S<T\), \(Q>0\). Equation (4) gives
\[
TN+U=Y+DC,
\]
so \(TN+Q=DC\). The assumption \(D\mid N\) therefore implies \(D\mid Q\). Write \(Q=Dz\), with \(z>0\); then
\[
U=Dz+Y.
\tag{5}
\]

The case condition \((2r-1)s\ge a\) gives \(2rs\ge a+s\), so \(M=2^{a+s}\mid T\). Reducing (5) modulo \(M\), using \(D=M+3\), yields
\[
M\mid 3z+Y=3(z+nS).
\]
Since \(M\) is a power of two, it is coprime to \(3\), hence
\[
M\mid z+nS.
\tag{6}
\]

Now set
\[
L=\left\lfloor\frac{a+s-1}{s}\right\rfloor,\qquad c=c_r(s).
\]
The division algorithm gives \(1\le c\le s\) and \(Ls+c=a+s\). Also \(L+1\le2r\), because \(a\le(2r-1)s\). Split
\[
S=\operatorname{geomSum}(t,L+1)
+t^{L+1}\operatorname{geomSum}(t,2r-(L+1)).
\]
Since \((L+1)s\ge a+s\), the tail term is divisible by \(M\). Thus (6) implies
\[
M\mid z+R_{\rm low},\qquad
R_{\rm low}=n\,\operatorname{geomSum}(t,L+1).
\tag{7}
\]

The finite geometric-sum inequality
\[
n\,\operatorname{geomSum}(t,L+1)<(n+1)t^L
\]
holds because \(n+2\le t\), which follows from \(s\ge d\) and (2). Since \(c\ge d\), (2) also gives \(n+1\le2^c-4\). Therefore
\[
R_{\rm low}<(2^c-4)t^L=M-4t^L.
\tag{8}
\]

It remains to bound \(z\). From \(Q=Dz<U\) and \(D>M\),
\[
z<\frac{U}{M}=(2u-3)\frac{2^{2rs}}{2^{a+s}}.
\]
By (3), \(2u-3=9^r+2s<4\cdot2^E\). The definitions of \(E,L,c\) give
\[
E+2rs
=2a-(2r-2)s-c+2rs
=a+s+Ls.
\]
Hence
\[
z<\frac{4\cdot2^E2^{2rs}}{2^{a+s}}
=4\cdot2^{Ls}=4t^L.
\tag{9}
\]
Combining (8) and (9),
\[
0<z+R_{\rm low}
<4t^L+(2^c-4)t^L
=2^ct^L
=2^{Ls+c}
=2^{a+s}
=M.
\]
This contradicts (7), proving (1).

## Original-source composition

CancellationMidBandSource.lean contains the source-linked theorem no_original_source_parent_in_remainder_band_wide. It uses NeedleGeneralInverse.original_source_inverse_iff to convert an original high-level transition into exact inverse-parent list membership, then uses injectivity of oddTower to identify the source parameters. The arithmetic divisibility contradiction therefore excludes a genuine original-source one-step predecessor, not merely a relaxed divisibility candidate.

This is still only a one-step parent exclusion for one synthetic feeder family. It does not show that the feeder is unreachable from the blank tape, exclude valuations outside (W), prove Space Needle nonhalting, or determine BB(6).

## Finite range audit

The updated residue_band_scan.js uses BigInt arithmetic to count the old and wide residue-cut conditions. For \(r=2,\ldots,8\):

| \(r\) | Old residue-cut count | Wide count | Additional values |
|---:|---:|---:|---:|
| 2 | 5 | 21 | 16 |
| 3 | 44 | 101 | 57 |
| 4 | 345 | 615 | 270 |
| 5 | 2,616 | 4,088 | 1,472 |
| 6 | 20,119 | 28,972 | 8,853 |
| 7 | 157,670 | 214,606 | 56,936 |
| 8 | 1,255,514 | 1,639,856 | 384,342 |

These counts are a reproducible finite range audit, not part of the all-\(r\) proof.

## Formalization status and limitations

The Lean drafts are committed in:
- CancellationMidBandResidue.lean: midband_no_parent_remainder_general and its exact source-equation adapter;
- CancellationMidBandSource.lean: no_original_source_parent_in_remainder_band_wide and the parent-list bridge.

The prior, narrower residue-cut source theorem is retained as a corollary. The wider declarations have not yet passed local Lean preflight or a fresh pinned-source CI run. Do not move this result to results/ or describe it as verified until both checks succeed. The existing manual-only workflow agent46-needle-three.yml already compiles the dependency chain; no new workflow is required.
