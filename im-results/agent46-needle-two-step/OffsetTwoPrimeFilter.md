# Offset-two elimination for the wide-band exceptions

**Status:** exact finite exclusions of the \(t=w+2\) second-parent offset for the \(r=50\) and \(r=160\) cancellation-family exception sets. The \(r=50\) exclusions use small prime witnesses; the \(r=160\) exclusions combine prime witnesses with an exact quotient obstruction. This is not a uniform theorem for all \(r\), all offsets, or blank-root reachability.

## Necessary condition

For a first parent at valuation \(w\) and a second parent at \(t=w+k\), the quotient-free two-step congruence implies
\[
D_{w+k}\mid
y+(2^k-2)w+3-k+(2k-3)2^{k-1}.
\]
At \(k=2\), this specializes to
\[
D_{w+2}\mid y+2w+3. \tag{P2}
\]
Therefore, for any prime \(p\), if
\[
2^{w+3}+3\equiv0\pmod p
\quad\text{but}\quad
y+2w+3\not\equiv0\pmod p,
\]
then the candidate has no second parent at valuation \(w+2\).

## Candidate sets and combined results

The candidate set is the wide-band exception parametrization
\[
a-5=ks+e,\qquad r-1\le k\le2r-2,\qquad 0\le e\le d-2,
\]
with the two band inequalities, followed by the existing eleven-prime first-parent filter and the short odd-entry exclusion. The remaining candidates are exactly the forced-even exception set in Agent 20's audit.

| Family member | Forced-even exceptions | Prime bound | Prime witnesses | Quotient obstructions | Remaining |
|---|---:|---:|---:|---:|---:|
| \(r=50\) (\(j=0\)) | 28 | \(p\le1{,}000{,}000\) | 28 | 0 | **0** |
| \(r=160\) (\(j=1\)) | 105 | \(p\le1{,}000{,}000\) | 94 | 11 | **0** |
| \(r=270\) (\(j=2\)) | 195 | \(p\le1{,}000{,}000\) | 172 | 23 | **0** |
| \(r=380\) (\(j=3\)) | 272 | \(p\le1{,}000{,}000\) | 240 | 32 | **0** |
| \(r=490\) (\(j=4\)) | 341 | \(p\le1{,}000{,}000\) | 303 | 38 | **0** |
| \(r=600\) (\(j=5\)) | 355 | \(p\le1{,}000{,}000\) | 322 | 33 | **0** |
| \(r=710\) (\(j=6\)) | 545 | \(p\le1{,}000{,}000\) | 480 | 65 | **0** |
| \(r=820\) (\(j=7\)) | 572 | \(p\le1{,}000{,}000\) | 508 | 64 | **0** |

For \(r=50\), every one of the 28 candidates has an explicit prime witness. The table gives the parametrizing pair \((k,e)\), the prime \(p\mid D_{w+2}\), and the nonzero residue of \(y+2w+3\pmod p\).

| \(k\) | \(e\) | \(p\) | \((y+2w+3)\bmod p\) |
|---:|---:|---:|---:|
| 50 | 148 | 7 | 1 |
| 53 | 42 | 5 | 1 |
| 57 | 53 | 13 | 7 |
| 57 | 110 | 1009 | 11 |
| 59 | 10 | 5 | 1 |
| 59 | 69 | 405991 | 227526 |
| 60 | 98 | 7 | 2 |
| 65 | 38 | 1523 | 1303 |
| 65 | 103 | 7 | 2 |
| 66 | 86 | 5 | 1 |
| 67 | 63 | 7 | 2 |
| 70 | 38 | 5 | 3 |
| 70 | 108 | 7 | 4 |
| 71 | 91 | 7 | 3 |
| 74 | 70 | 5 | 1 |
| 77 | 31 | 7 | 6 |
| 79 | 102 | 7 | 3 |
| 80 | 38 | 5 | 1 |
| 80 | 118 | 7 | 2 |
| 85 | 38 | 5 | 4 |
| 85 | 123 | 7 | 2 |
| 86 | 52 | 7 | 4 |
| 89 | 142 | 7 | 3 |
| 90 | 38 | 5623 | 2641 |
| 90 | 128 | 7 | 2 |
| 92 | 22 | 5 | 3 |
| 93 | 41 | 7 | 1 |
| 96 | 134 | 7 | 2 |

## Quotient obstruction for the 11 remaining \(r=160\) candidates

After the prime search through \(10^6\), eleven \(r=160\) candidates remain. They can all be excluded without increasing the prime bound.

For \(t=w+2\), put
\[
C=110w+190,\qquad u=2^{s+2},\qquad
S_u=\sum_{i=0}^{2r-1}u^i,\qquad D=D_{w+2}=2^{a+s+2}+3.
\]
The necessary condition (P2) gives \(D\mid 8AP_r(A)+C\). Since \(Au\equiv-3\pmod D\),
\[
u^{2r}AP_r(A)\equiv3nS_u\pmod D.
\]
As \(u^{2r}\) is divisible by \(8\) and \(D\) is odd, this implies
\[
D\mid Z,\qquad
Z:=3nS_u+\frac C8u^{2r}.
\]
Write \(Z=Dz\).

Set \(T=s+2\), \(m_0=a+s+2\), and let \(c_0\in\{1,\ldots,T\}\) be the positive remainder of \(m_0\) modulo \(T\) (use \(c_0=T\) when \(T\mid m_0\)). Choose
\[
\ell=\begin{cases}0,&c_0\ge d+1,\\c_0,&c_0\le d,\end{cases}
\qquad m=m_0-\ell.
\]
If \(\ell=0\), take \(c=c_0\); otherwise take \(c=T\). Then
\[
m=LT+c,\qquad c\ge d+1,\qquad m_0-d\le m\le m_0.
\]
With \(M=2^m=u^L2^c\), the lower band inequality gives \(M\mid u^{2r}/8\), while \(D\equiv3\pmod M\). Reducing \(Dz=Z\) modulo \(M\) and splitting \(S_u=R+u^{L+1}(\cdots)\), where \(R=\sum_{i=0}^L u^i\), gives
\[
M\mid z-nR.
\]
Also \(R<2u^L\), so \(nR<M\) because \(2^c>2n\).

Write \(z=nR+kM\), with \(k\ge0\). Reducing \(Dz=Z\) modulo \(n\) determines \(k\) modulo \(n\):
\[
k\equiv\kappa:=
C u^{2r}(8DM)^{-1}\pmod n,\qquad 0\le\kappa<n. \tag{Q}
\]
The size bound is also explicit. Since \(C<256(n+5)\le2^{d+8}\), \(S_u<2u^{2r-1}\), \(D>2^{a+s+2}\), and \(m\ge a+s+2-\ell\),
\[
\frac zM
<
6n\,2^{(2r-2)(s+2)-a-m}
+\frac C8\,2^{(2r-1)(s+2)-a-m}
<
2^{r-3+\ell}
\]
for the eleven candidates. Here the last inequality uses \(s\ge4r\), \(3r-1\le d\), \((2r-2)s\le2a-2d-6\), and the observed candidate-wide bound \(\ell\le117\). Thus
\[
0\le k<2^{r-3+\ell}<n
\]
(\(r=160\), \(d=506\), and the largest exponent is \(274\)). Consequently \(k=\kappa\).

The exact modular computation of (Q) gives the following certificate. Ten candidates have \(\ell=0\); the one exception has \(c_0=\ell=117\). Every \(\kappa\) has at least 504 bits, whereas the largest bound is \(2^{274}\).

| \(k\) | \(e\) | \(\ell\) | Bound exponent \(r-3+\ell\) | Bits in \(\kappa\) |
|---:|---:|---:|---:|---:|
| 190 | 218 | 0 | 157 | 506 |
| 194 | 500 | 117 | 274 | 505 |
| 215 | 263 | 0 | 157 | 505 |
| 228 | 218 | 0 | 157 | 505 |
| 238 | 100 | 0 | 157 | 504 |
| 261 | 281 | 0 | 157 | 505 |
| 270 | 308 | 0 | 157 | 505 |
| 292 | 66 | 0 | 157 | 506 |
| 299 | 275 | 0 | 157 | 506 |
| 313 | 461 | 0 | 157 | 505 |
| 314 | 452 | 0 | 157 | 504 |

Every row has \(\kappa>2^{r-3+\ell}\), contradicting the forced bound on \(k\). Thus all eleven remaining \(r=160\) candidates are excluded at offset \(t=w+2\).

This is an exact finite proof for the enumerated exception sets. It is not a theorem for all \(r\), does not eliminate other second-parent offsets, and does not establish blank-root nonreachability.

### Further members of the cancellation progression

The same exact script was also run at \(r=270,380,490,600,710,820\), always with prime bound \(10^6\). Every prime-filter survivor was eliminated by the quotient obstruction. The following summary records the maximum cut loss \(\ell\), the maximum exponent in the bound \(2^{r-3+\ell}\), and the minimum bit length of the computed least residue \(\kappa\) among quotient-obstructed candidates.

| \(r\) | \(d\) | Quotient rows | Maximum \(\ell\) | Maximum bound exponent | Minimum bits in \(\kappa\) |
|---:|---:|---:|---:|---:|---:|
| 160 | 506 | 11 | 117 | 274 | 504 |
| 270 | 855 | 23 | 313 | 580 | 841 |
| 380 | 1203 | 32 | 211 | 588 | 1199 |
| 490 | 1552 | 38 | 205 | 692 | 1545 |
| 600 | 1901 | 33 | 377 | 974 | 1892 |
| 710 | 2250 | 65 | 218 | 925 | 2244 |
| 820 | 2598 | 64 | 495 | 1312 | 2591 |

In each row the maximum bound exponent is strictly below \(d-1\), while the minimum \(\kappa\)-bit length is far above that exponent. Thus every computed \(\kappa\) exceeds its candidate's bound. These are exact finite computations for the listed family members; the pattern is not a proof for all later \(j\).

## Reproduction

The self-contained Node.js script is offset_two_prime_filter.js. It uses exact BigInt modular arithmetic, a prime sieve, and the recurrence for \(y\bmod p\); it never materializes \(2^a\) or \(D_{w+2}\) as giant integers. It also computes the quotient obstruction (Q) for every prime-filter survivor.

Run:
\`\`\`sh
node offset_two_prime_filter.js 50 1000000
node offset_two_prime_filter.js 160 1000000
\`\`\`

The filter is one-way and exact: every prime witness or quotient obstruction rules out that candidate by (P2). No Lean compilation is claimed.
