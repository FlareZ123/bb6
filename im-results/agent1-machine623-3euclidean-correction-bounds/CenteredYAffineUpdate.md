# Centered residual one-step affine update

This is an algebraic simplification of the compact gap/scale cocycle. It isolates the next smaller counter as the only large additive term in the centered residual update.

## Definitions and conventions

For sector \(s\in\{LO,LE,RO,RE\}\), set
\[
c_s=(18,10,2,4),\qquad z=Y-c_s,\qquad Y=2g.
\]
The exact gap cocycle is
\[
Y'=|Y-2T|-6q',\qquad T=3D+2r+t_s,
\]
where \(q'\) is the next smaller counter, \(D\) is the signed first-counter drop, and \(r\) is the split outer-drain count. The sector constants are
\[
t_{LO}=19,\quad t_{LE}=10,\quad t_{RO}=-4,\quad t_{RE}=4.
\]
The split convention is important: in RE, \(r=R_{\rm full}-1\); in LO/LE/RO, \(r=R_{\rm full}\).

Let \(s'\) be the target sector, with centered constant \(c_{s'}\). Since \(Y=z+c_s\),
\[
z'=|z+c_s-2T|-6q'-c_{s'}.
\]

## Exact two-branch formula

The output-side decision is the sign of \(g-T\), equivalently of \(Y-2T\).

If \(g>T\), the absolute value is positive and
\[
\boxed{z'=z-6q'+\kappa_+,\qquad
\kappa_+=c_s-c_{s'}-2T
=c_s-c_{s'}-6D-4r-2t_s.}
\]

If \(g<T\), the absolute value is negative and
\[
\boxed{z'=-z-6q'+\kappa_-,\qquad
\kappa_-=-c_s-c_{s'}+2T
=-c_s-c_{s'}+6D+4r+2t_s.}
\]

Thus in both cases the centered residual has the same scale term:
\[
\boxed{z'=\sigma z-6q'+\kappa,\qquad \sigma\in\{+1,-1\}.}
\]
The coefficient of \(q'\) is always \(-6=-2\cdot3\): it is exactly a one-place ternary shift followed by multiplication by 2. No \(\beta,\delta\), \(H\), or orientation-dependent scale coefficient remains in this formula.

## Sector constants and a conditional correction bound

The sector constants are:
| Sector | \(c_s\) | \(t_s\) |
|---|---:|---:|
| LO | 18 | 19 |
| LE | 10 | 10 |
| RO | 2 | -4 |
| RE | 4 | 4 |

The constant parts of \(\kappa_+\) and \(\kappa_-\), before the \(\mp6D\mp4r\) terms, have maximum absolute values 38 and 28 respectively over all 16 source/target sector pairs:
\[
\max_{s,s'}|c_s-c_{s'}-2t_s|=38,
\]
\[
\max_{s,s'}|-c_s-c_{s'}+2t_s|=28.
\]

If the source depth bounds \(|D|\le\ell+1\) and \(r\le\ell\) are available, then
\[
|\kappa_+|\le6(\ell+1)+4\ell+38=10\ell+44,
\]
\[
|\kappa_-|\le6(\ell+1)+4\ell+28=10\ell+34.
\]
Consequently \(|\kappa|\le10\ell+44\). For the centered-Y width \(W_Y=4(9\ell+22)=36\ell+88\), this gives
\[
|\kappa|<W_Y<3^k
\]
when \(3^k>W_Y\). The algebraic update is exact independently of these bounds; the displayed uniform bound remains conditional until the combined \(D,r\) depth wrapper is source-CI certified.

## Computational cross-check

A deterministic BigInt replay of 9,967 root transitions \(D_{33}\to D_{10000}\), using the source-shaped drain summary and the split RE count, found **zero** failures of the two-branch identity. The largest observed \(|\kappa|\) was 9,604. This is a consistency check, not a substitute for the exact algebraic derivation or a source-compiled proof.

## Why this may help the buffered residue argument

The centered middle-block test trims two low ternary positions. The new update separates:
- a signed copy of the old residual \(z\);
- the next scale \(q'\), shifted by exactly one ternary place and multiplied by 2;
- a correction \(\kappa\) whose conditional source bound is below \(3^k\).

This is a cleaner carry interface than the absolute-value formula alone. A prospective induction can now study the joint buffered digit blocks of \((z,q)\) under \(z'=\pm z-6q'+\kappa\), rather than the four separate \(h'\) formulas or the full pair \((H,q)\). The remaining difficulty is to show that the joint digit language excludes both all-zero and all-two middle blocks after the one-place shift and bounded correction; nonmonochromaticity of \(z\) and \(q\) separately is not by itself sufficient.

This is an intermediate algebraic result, not a proof that the root avoids the terminal strip.
