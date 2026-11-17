# Residue-cut extension of the cancellation-feeder parent exclusion

**Status:** exact paper-level arithmetic proof, derived 17 November 2026; Lean formalization and original-source composition pending. This is an extension of the verified all-r middle band, not a BB(6) decision.

## Theorem

Let
[
a_r=\frac{9^r+5}{2},\qquad
d_r=1+\lfloor\log_2(3^{2r-1})\rfloor,
\qquad
P_0(A)=0,\quad P_{r+1}(A)=A^2P_r(A)+9^r(A-3).
]
For (s\ge1), define the positive cut remainder
[
c_r(s):=a_r+s-s\left\lfloor\frac{a_r+s-1}{s}\right\rfloor
       =((a_r+s-1)\bmod s)+1.
]

For every (r\ge2) and (s\in\mathbb N), if
[
d_r\le s,\qquad
(2r-1)s\ge a_r,\qquad
rs\le a_r,\qquad
c_r(s)\ge d_r,
	ag{R}
]
then
[
\boxed{
2^{a_r+s}+3\nmid
\left(2^{a_r}P_r(2^{a_r})+3-2(a_r-1+s)\right).
}
	ag{1}
]
Equivalently, no inverse-parent valuation (u=a_r-1+s) in this residue-cut range can satisfy the exact cancellation-feeder parent divisibility condition.

This is complementary to the already formalized middle band
[
d_r\le s,\qquad (2r-2)s\le a_r-d_r.
	ag{2}
]
The union of (1) and (2) is the stronger exclusion; (1) is especially useful above the old upper endpoint.

## Proof

Fix (r,s) satisfying (R). Abbreviate
[
a=a_r,quad A=2^a,quad u=a-1+s,quad t=2^s,quad
n=3^{2r-1},quad S=\sum_{j=0}^{2r-1}t^j,
]
and put
[
D=2^{a+s}+3,qquad M=2^{a+s},qquad
T=t^{2r},qquad R_0=nS.
]
The exact polynomial identity already used in the formalized middle-band proof is
[
TAP_r(A)=3^{2r}S+D C
	ag{3}
]
for a natural number (C). This is the existing `cert_identity` with (t=2^s).

Assume, for contradiction, that (D) divides
[
N=AP_r(A)+3-2u.
]
Set
[
Y=3^{2r}S=3R_0,quad U=(2u-3)T,quad Q=U-Y.
]
Multiplying (N) by (T) and using (3) gives
[
TN+Q=DC.
]
Thus (D\mid Q). Also (Q>0): (S<T), while (2u-3=3^{2r}+2s>3^{2r}). Write (Q=Dz) with (z\in\mathbb N), (z>0). Then
[
U=Dz+Y.
	ag{4}
]

Because ((2r-1)s\ge a), we have (2rs\ge a+s), so (M\mid T). Since (D=M+3), reducing (4) modulo (M) yields
[
M\mid 3z+Y=3(z+R_0).
]
As (M) is a power of two, it is coprime to (3), hence
[
M\mid z+R_0.
	ag{5}
]

Now let
[
L=\left\lfloor\frac{a+s-1}{s}\right\rfloor,
\qquad c=a+s-Ls=c_r(s).
]
The division algorithm gives (1\le c\le s) and
[
Ls+c=a+s.
	ag{6}
]
Also (L+1\le2r), since ((2r-1)s\ge a). Split the geometric sum at (L):
[
S=\sum_{j=0}^{L}t^j+t^{L+1}\sum_{j=0}^{2r-L-2}t^j.
]
By the definition of (L), ((L+1)s\ge a+s), so (M\mid t^{L+1}). Therefore
[
R_0\equiv R_1:=n\sum_{j=0}^{L}t^j
=n\,\operatorname{geomSum}(t,L+1)\pmod M.
]
Together with (5),
[
M\mid z+R_1.
	ag{7}
]

We show (0<z+R_1<M), contradicting (7).

First, the finite geometric-sum identity gives
[
\operatorname{geomSum}(t,L)(t-1)+1=t^L.
]
Since (n+2\le t), it follows that
[
n\operatorname{geomSum}(t,L)<t^L.
]
Splitting off the last term,
[
n\operatorname{geomSum}(t,L+1)
=n\operatorname{geomSum}(t,L)+nt^L
<(n+1)t^L.
]
The standard logarithmic gap (2^{d_r}\ge n+5), together with (c\ge d_r), gives (n+1\le2^c-4). Consequently,
[
R_1<(2^c-4)t^L=M-4t^L,
	ag{8}
]
where (6) was used in the last equality.

It remains to bound (z). From (Q<U), (D>M), and (Q=Dz),
[
z<\frac{(2u-3)2^{2rs}}{2^{a+s}}.
	ag{9}
]
Put
[
E=2a-(2r-2)s-c.
]
Since (c\le s) and (rs\le a),
[
E\ge2a-(2r-1)s\ge s.
	ag{10}
]
We claim (2u-3=9^r+2s<4\cdot2^s). For (r=2), (a_2=43), so (s\le21), while (s\ge d_2=5); hence (9^2+2s\le123<128\le4\cdot2^s). For (r\ge3), the bound (rs\le a) gives
[
6s\le2rs\le2a=9^r+5=3n+5,
]
so (2s\le n+2). Since (2^s\ge n+5),
[
9^r+2s=3n+2s\le4n+2<4(n+5)\le4\cdot2^s.
]
Combining this with (10),
[
2u-3<4\cdot2^E.
]
Using (Ls+c=a+s), this is exactly the exponent comparison
[
(2u-3)2^{2rs}
<4\cdot2^{E+2rs}
=4\cdot2^{a+s}2^{Ls}
=4M t^L.
]
Equation (9) therefore gives
[
z<4t^L.
	ag{11}
]
Finally, (8) and (11) imply
[
0<z+R_1<4t^L+(2^c-4)t^L=2^ct^L=M,
]
contradicting (7). This proves (1).

## Concrete range growth

The attached `residue_band_scan.js` enumerates the integers (s) satisfying (R) using exact BigInt arithmetic. For illustration:

| (r) | (a_r) | (d_r) | Old upper endpoint (lfloor(a_r-d_r)/(2r-2)\rfloor) | New residue-cut (s) beyond old endpoint |
|---:|---:|---:|---:|---:|
| 3 | 367 | 8 | 89 | 28 |
| 4 | 3,283 | 12 | 545 | 268 |
| 5 | 29,527 | 15 | 3,689 | 2,207 |
| 6 | 265,723 | 18 | 26,570 | 17,705 |
| 7 | 2,391,487 | 21 | 199,288 | 142,342 |
| 8 | 21,523,363 | 24 | 1,537,381 | 1,153,023 |

The residue condition produces short gaps rather than one uninterrupted interval. The theorem is uniform in (r); the table is only an illustration of its range.

## Status and limitations

- The argument is an exact paper proof; it has **not yet been Lean-formalized**.
- It is an arithmetic exclusion for the cancellation-form immediate-parent divisibility condition. Composing it with `NeedleGeneralInverseSource.original_source_inverse_iff` should give the corresponding authentic one-step source-parent exclusion, but that composition is also pending.
- It does not exclude the complementary valuation classes, establish blank-root unreachability of the feeder, prove Space Needle nonhalting, or determine BB(6).
- Keep this in `im-results/` until the Lean theorem and pinned-source composition pass.
