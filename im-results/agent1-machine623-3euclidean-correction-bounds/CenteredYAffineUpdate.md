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

The source depth package RootRayDrainDepthSource.lean supplies, for each of the four root-ray boundary drains under its sector budget and power hypotheses, a full evaluator count R_full≤ell and signed first-counter drop -ell≤D≤ell+1. In RE the split count is r=R_full-1; in LO/LE/RO it is r=R_full. These bounds give |kappa_+|≤10ell+44 and |kappa_-|≤10ell+34, hence |kappa|≤10ell+44<W_Y=36ell+88<3^k. The D/r depth bounds are therefore available from the source package. The remaining formalization gap is that the compact root gap cocycle Y'=|Y-2T|-6q' and its sector/sign normalization are documented in RootRayGapCocycle.md but are not yet a Lean theorem. The displayed z' identity is an exact algebraic consequence of that documented cocycle, but is not yet source-formalized.

## Computational cross-check

A deterministic BigInt replay of 9,967 root transitions \(D_{33}\to D_{10000}\), using the source-shaped drain summary and the split RE count, found **zero** failures of the two-branch identity. The largest observed \(|\kappa|\) was 9,604. This is a consistency check, not a substitute for the exact algebraic derivation or a source-compiled proof.

## Scalar digit transducer (finite diagnostic)

The affine update induces a digit transducer on pair symbols (z_i,q'_{i-1}). For sign sigma, its output digit and carry are
\[
d_i=(\sigma z_i-2q'_{i-1}+c_i)\bmod3,\qquad
c_{i+1}=\left\lfloor\frac{\sigma z_i-2q'_{i-1}+c_i}{3}\right\rfloor.
\]
A conservative carry envelope [-4,2] covers the low-boundary carry; the actual carry range in the 9,967-transition replay was [-3,0]. For initial carries in [-4,2], there are 513 universal length-three words for each sign; every observed pair window contains a sign-specific universal triple. There are 361 length-three words universal for both signs, and 9,963 of the 9,967 observed pair windows contain one. A common universal length-four word occurs in all 9,967 windows, but the set is broad (5,329 of 6,561 words). The transducer output digits matched the actual target z' digits throughout the replay. These are finite computational observations; proving that every future root pair window contains a universal word remains open.

## Why this may help the buffered residue argument

The centered middle-block test trims two low ternary positions. The new update separates:
- a signed copy of the old residual \(z\);
- the next scale \(q'\), shifted by exactly one ternary place and multiplied by 2;
- a correction \(\kappa\) whose conditional source bound is below \(3^k\).

This is a cleaner carry interface than the absolute-value formula alone. A prospective induction can now study the joint buffered digit blocks of \((z,q)\) under \(z'=\pm z-6q'+\kappa\), rather than the four separate \(h'\) formulas or the full pair \((H,q)\). The remaining difficulty is to show that the joint digit language excludes both all-zero and all-two middle blocks after the one-place shift and bounded correction; nonmonochromaticity of \(z\) and \(q\) separately is not by itself sufficient.

This is an intermediate algebraic result, not a proof that the root avoids the terminal strip.
