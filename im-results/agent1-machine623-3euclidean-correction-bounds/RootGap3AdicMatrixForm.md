# 3-adic matrix form of the centered root cocycle

**Status:** exact algebraic reformulation of the existing root cocycle. It exposes the linear 3-adic structure of the two branches; it is not a root-history invariant or a BB(6) proof.

## Coordinates and convention

Use the split drain convention of RootRayGapCocycle.md and CenteredYAffineUpdate.md: D is the signed first-counter drop and r is the split outer-drain count (in RE, r=R_full-1). For sector s in {LO, LE, RO, RE}, let
\[
c_s=(18,10,2,4),\qquad t_s=(19,10,-4,4),
\]
and set
\[
Y=2g,\qquad z=Y-c_s,\qquad w=z/2=g-c_s/2,\qquad q=m.
\]
All c_s are even, so w is an integer.

The exact centered update is
\[
z'=\sigma z-6q'+\kappa_\sigma,
\]
where sigma=+1 for left output and sigma=-1 for right output, with
\[
\kappa_+=c_s-c_{s'}-6D-4r-2t_s,
\]
\[
\kappa_-=-c_s-c_{s'}+6D+4r+2t_s.
\]

From the exact two-statistic table in RootRayGapCocycle.md,
\[
q'=
\begin{cases}
3q+2D+2r+c_{\delta,s},&\text{left},\\
3q+g-D+c_{\beta,s},&\text{right},
\end{cases}
\]
where
\[
(c_{\delta,s})=(14,8,0,5),\qquad
(c_{\beta,s})=(-5,-2,4,1).
\]
Since g=w+c_s/2, the right formula becomes
\[
q'=w+3q-D+\rho_s,\qquad
\rho_s=c_s/2+c_{\beta,s}=(4,3,5,3).
\]

## Exact affine matrix form

Dividing the centered update by two and substituting the corresponding q'
gives one of two fixed integer matrices.

For left output:
\[
\boxed{
\begin{pmatrix}w'\\q'\end{pmatrix}
=
\underbrace{\begin{pmatrix}1&-9\\0&3\end{pmatrix}}_{M_L}
\begin{pmatrix}w\\q\end{pmatrix}
+
\begin{pmatrix}-9D-8r+C_{L,s}\\2D+2r+c_{\delta,s}\end{pmatrix}.
}
\]

For right output:
\[
\boxed{
\begin{pmatrix}w'\\q'\end{pmatrix}
=
\underbrace{\begin{pmatrix}-4&-9\\1&3\end{pmatrix}}_{M_R}
\begin{pmatrix}w\\q\end{pmatrix}
+
\begin{pmatrix}6D+2r+C_{R,s}\\-D+\rho_s\end{pmatrix}.
}
\]

The target sector and the constants are completely determined by the input
sector and output orientation:

| Input sector | Left target | \(C_{L,s}\) | \(c_{\delta,s}\) | Right target | \(C_{R,s}\) | \(\rho_s\) |
|---|---|---:|---:|---|---:|---:|
| LO | LO | -61 | 14 | RO | -3 | 4 |
| LE | LE | -34 | 8 | RE | -6 | 3 |
| RO | LE | 0 | 0 | RE | -22 | 5 |
| RE | LO | -26 | 5 | RO | -8 | 3 |

These are exact identities, not asymptotic linearizations. The only
nonlinear control is the exact source-side branch decision
g >= 3D+2r+t_s versus its complement.

## 3-adic linear structure

The two matrices have
\[
\det M_L=3,\qquad \det M_R=-3.
\]
Each therefore has exactly one eigenvalue divisible by 3, of 3-adic
valuation one, and one 3-adic unit eigenvalue.

For M_L, the eigenvalues are 1 and 3. A unimodular-over-Z_3 eigenbasis is
given by columns (1,0)^T and (-9,2)^T; its determinant is 2, a 3-adic unit.

For M_R, the characteristic polynomial is
\[
f(\lambda)=\lambda^2+\lambda-3.
\]
Modulo 3, its roots are 0 and 2. Since f'(2)=5 is nonzero modulo 3,
Hensel's lemma gives a unique 3-adic root lambda_u congruent to 2 mod 3;
it satisfies lambda_u congruent to 5 mod 9. The other root
lambda_c=-1-lambda_u is congruent to 3 mod 9, hence v_3(lambda_c)=1.
For either eigenvalue lambda, an eigenvector is (lambda-3,1)^T. The
determinant of the two eigenvectors is lambda_u-lambda_c, congruent to 2
mod 3, so M_R is diagonalizable over Z_3.

Thus each branch has a one-dimensional 3-adic unit direction and a
one-digit contracting direction. The left branch has unit multiplier 1;
the right branch has a nontrivial unit multiplier congruent to 2 mod 3.

## Bounded translation at the moving-window scale

The source depth bounds used by the centered-Y analysis are
\[
-\ell\le D\le\ell+1,\qquad 0\le r\le\ell,\qquad
W_Y=36\ell+88<3^k.
\]
The table above gives, uniformly in the sector,
\[
|-9D-8r+C_{L,s}|\le17\ell+70<W_Y,
\]
\[
|2D+2r+c_{\delta,s}|\le4\ell+16<W_Y,
\]
\[
|6D+2r+C_{R,s}|\le8\ell+28<W_Y,
\]
\[
|-D+\rho_s|\le\ell+5<W_Y.
\]
Consequently each coordinate translation is smaller in ordinary absolute
value than 3^k. When the low k digits are stripped, its contribution to the
next high-digit stream is a bounded carry/borrow (at most one unit from the
translation itself). This is the scale reason a finite carry description
of the joint (w,q) buffer is plausible.

This magnitude statement does not mean the translations are 3-adically
small, nor does it determine the exact carry from the low k digits.
The exact D,r dependence and the source-side branch/sector transition
must still be accounted for.

## Connection to the moving S-window

The determinant-±3 structure is consistent with the observed one-place
3-adic scale shift. In the S-window source indexing, the transducer emits
one or two low digit-pairs before the target window begins; the shifted
reset-carry product in ShiftedResetCarryDFA.js tracks precisely offsets
0,1,2 of that output stream. The matrix form gives the complementary
coordinate-side description: the target (w',q') pair is obtained by one
of two fixed 3-adic linear maps plus a bounded translation.

This is a structural connection, not yet a conjugacy theorem between the
matrix cocycle and the reset automaton.

## Research consequence and remaining gap

A promising finite-state target is the joint high-digit buffer of (w,q),
with control state containing sector and output orientation, and carry state
accounting for the four bounded translations. The three-state drain
transducer supplies D,r; the shifted reset-carry machine supplies the
post-reset carry label after the correct one/two low-output symbols are
consumed.

The remaining hard step is to prove that the authentic D(0,7) orbit
selects only transitions in a finite invariant subset of this joint
machine, and that every resulting target window contains a reset. The
matrices alone do not prove that the branch is determined by the sign of g,
that the phase set is closed, or that the centered middle block is
nonmonochromatic. No all-time root claim is made.
