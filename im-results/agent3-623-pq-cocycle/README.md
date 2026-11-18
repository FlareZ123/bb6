# Exact \((p,q)\) cocycle for the #623 canonical-ray transition

**Status:** exact algebraic reduction of the source-derived canonical-ray formulas; not yet a root invariant and not a halting/nonhalting proof.

## Coordinates and source corrections

For a state \(D(a,d)\), put
\[
p=|a-d|,\qquad q=\min(a,d).
\]
In each canonical sector, the next unsorted counters are
\[
A=p+\beta,\qquad E=3q+\delta,
\]
where \(D,r\) are the signed-drop and drain-count statistics from the canonical drain. The correction table is:

| Sector | \(\beta\) | \(\delta\) | \(T=\delta-\beta\) | \(S=\delta+2\beta\) |
|---|---:|---:|---:|---:|
| LO | \(-D-5\) | \(2D+2r+14\) | \(3D+2r+19\) | \(2r+4\) |
| LE | \(-D-2\) | \(2D+2r+8\) | \(3D+2r+10\) | \(2r+4\) |
| RO | \(4-D\) | \(2D+2r\) | \(3D+2r-4\) | \(2r+8\) |
| RE | \(1-D\) | \(2D+2r+5\) | \(3D+2r+4\) | \(2r+7\) |

The RE convention is the one in RootRayGapCocycle.md: the initial evaluator's signed drop is included in \(D\), while \(r\) counts the subsequent drain iterations. If the initial evaluator is bundled into drainB, its full iteration count is \(r+1\).

## Single piecewise-affine transition

The output state is obtained by sorting \(A,E\). Thus, with \(p'=|A-E|\) and \(q'=\min(A,E)\),
\[
\boxed{
p'=|p-3q-T|,\qquad q'=\min(p+\beta,\,3q+\delta).
}
\]
The branch is determined exactly by the sign of \(p-3q-T\):
\[
\begin{array}{c|cc}
& p' & q'\\ \hline
p-3q\ge T & p-3q-T & 3q+\delta\\
p-3q<T & 3q+T-p & p+\beta.
\end{array}
\]
This is a corrected 3-Euclidean step. It packages the eight source cases (four input sectors times two output orientations) into two affine branches with four sector-dependent correction pairs.

The corresponding affine matrices are
\[
M_L=\begin{pmatrix}1&-3\\0&3\end{pmatrix},
\qquad
M_R=\begin{pmatrix}-1&3\\1&0\end{pmatrix},
\]
with \(\det M_L=3\) and \(\det M_R=-3\). Modulo \(3\), both matrices have rank one:
\[
M_L\equiv\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
M_R\equiv\begin{pmatrix}2&0\\1&0\end{pmatrix}\pmod3.
\]
So each successful canonical step removes exactly one independent 3-adic digit from the linear part; the drain statistics inject the new low-order information.

## Useful derived coordinates

Let \(g=p-3q\), \(Y=2g\), and \(K=2p+3q\). Then
\[
Y'=|Y-2T|-6q',
\]
and
\[
K'=
\begin{cases}
K+S,&p-3q\ge T,\\[2mm]
(K+9q+3\delta+S)/2,&p-3q<T.
\end{cases}
\]
The division by \(2\) is exact on the right branch because the expression is \(2K'\). The left branch updates \(K\) by \(S\) alone, independent of \(q\) and \(D\); on the right branch the old scale enters through \(9q\), and the signed drop enters through \(3\delta\).

The old-ray distance \(h\) is related to \(Y\) by
\[
Y=2h+18\quad(\mathrm{LO}),\qquad
Y=2h+10\quad(\mathrm{LE}),
\]
\[
Y=4h+2\quad(\mathrm{RO}),\qquad
Y=4h+4\quad(\mathrm{RE}).
\]
Consequently the terminal-window condition \(|h|\le W\) becomes a short interval for \(Y\), with width \(2W\) in LO/LE and \(4W\) in RO/RE.

## Why this reduction may matter

The matrices have determinant exactly \(\pm3\), not merely a determinant divisible by \(3\). The 3-adic evolution is therefore a one-digit rank drop at every canonical step, while the non-linear information is confined to the explicit drain statistics \(D,r\). The coordinate \(K\) further shows that the left branch has a particularly simple update. These facts suggest a finite-state or stack-based 3-adic analysis driven by the ternary drain word.

This does **not** by itself exclude the terminal window: the allowed \(D,r\) are correlated digit statistics, not arbitrary small errors. The next mathematical task is to combine this \((p,q)\) map with the exact DrainDigitStack.md representation and prove that the root's admissible correction sequence cannot produce a terminal-window residue. No bounded scan is used as a substitute for that proof.

## Derivation source

The sector correction table and terminal-distance normalizations are the algebraic content of im-results/agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md; the valuation/digit interpretation is in im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitStack.md and im-results/agent41-623-3euclidean/DrainValuationNormalForm.md. The equations above are obtained by substituting \(A=p+\beta\), \(E=3q+\delta\) and sorting the two outputs. This note does not claim an independent Lean compilation.
