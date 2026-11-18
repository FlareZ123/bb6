# Signed-coordinate normal form for the #623 root cocycle

This note records an exact algebraic simplification of the four-sector affine root cocycle. It is an intermediate result, not a proof that the canonical root orbit avoids the terminal strips.

## 1. Common branch factorization

In the integer carry coordinates used by the integer carry transducer,
\[
x=2g-\gamma_s,\qquad y=6q,
\]
the linear parts are
\[
M_L=\begin{pmatrix}1&-3\\0&3\end{pmatrix},\qquad
M_R=\begin{pmatrix}-4&-3\\3&3\end{pmatrix}.
\]
They satisfy
\[
M_R=UM_L,\qquad
U=\begin{pmatrix}-4&-5\\3&4\end{pmatrix},\qquad
U^2=I,\quad \det U=-1.
\]
Thus both branches share the same index-three linear map; the right branch applies a unimodular involution afterward.

A basis matrix
\[
P=\begin{pmatrix}1&5\\-1&-3\end{pmatrix},\qquad \det P=2
\]
diagonalizes the involution over \(\mathbb Z_3\), since 2 is a 3-adic unit:
\[
P^{-1}M_LP=\frac12\begin{pmatrix}3&3\\1&5\end{pmatrix},\qquad
P^{-1}M_RP=\frac12\begin{pmatrix}3&3\\-1&-5\end{pmatrix}.
\]
The first row is branch-independent; only the sign of the second row changes.

## 2. Integral coordinates and exact affine update

Because \(x\) and \(y=6q\) are even, define
\[
w=-x/2-5q,\qquad v=x/2+3q.
\]
Then
\[
w+v=-2q,\qquad x=3w+5v,\qquad y=-3(w+v).
\]

Write the branch updates as
\[
x'=\begin{cases}x-18q+C_L,&L,\\-4x-18q+C_R,&R,\end{cases}
\]
and
\[
y'=\begin{cases}18q+F_L,&L,\\3x+18q+F_R,&R.\end{cases}
\]
Set
\[
A=\frac{-3C-5F}{6},\qquad B=\frac{C+F}{2}.
\]
The exact transformed updates are
\[
\boxed{w'=w-q+A}
\]
and
\[
\boxed{v'=\begin{cases}x/2+B,&L,\\-x/2+B,&R.\end{cases}}
\]
The linear part of the \(w\)-update is independent of branch. The new centered distance coordinate \(v'\) is the signed old terminal residual \(x/2\), plus the drain correction.

## 3. Full-drain correction table

Here \(D\) is the signed first-counter drop and \(R\) is the *full* number of evaluator calls. In the right-even sector, this includes the initial evaluator as well as the subsequent drain calls. This convention is important: it removes the special extra evaluator from the right-even formulas.

| Sector / output | \(A\) | \(B\) |
|---|---:|---:|
| LO / L | \(-D-2R-9\) | \(-3D-2R-19\) |
| LE / L | \(-D-2R-6\) | \(-3D-2R-10\) |
| RO / L | \(-D-2R\) | \(-3D-2R\) |
| RE / L | \(-D-2R+3\) | \(-3D-2R-9\) |
| LO / R | \(-D-2R-17\) | \(3D+2R+9\) |
| LE / R | \(-D-2R-9\) | \(3D+2R+3\) |
| RO / R | \(-D-2R-3\) | \(3D+2R-7\) |
| RE / R | \(-D-2R-5\) | \(3D+2R-1\) |

The underlying \((C,F)\) correction table and the identities
\[
6A=-3C-5F,\qquad 2B=C+F
\]
are formalized in the Lean source.

## 4. Formal verification

SignedCoordinateNormalForm.lean is self-contained and uses only Std.Tactic. It proves:
- the common factorization \(M_R=UM_L\);
- the involution identity \(U^2=I\) and determinant data;
- both conjugacy identities after clearing denominators;
- the coordinate reconstruction identities;
- all eight full-drain correction-table identities;
- the exact left- and right-branch affine updates in \((w,v)\).

The file was compiled locally with Lean 4.36.0-rc2. The matrix identities are proved by kernel reduction (decide); the affine identities use omega. No sorry or sorryAx is used.

## 5. Research significance and remaining gap

This basis reduces the branch difference to a sign flip in one coordinate. It may permit a smaller 3-adic carry abstraction or a more effective invariant for the root's middle ternary digit blocks.

It does not by itself establish an all-time root-orbit invariant or exclude any terminal state. The next mathematical task is to exploit the branch-independent w update and the signed-residual v update to obtain a genuinely inductive digit-language or quantitative gap bound.

Related source work:
- im-results/agent41-623-integer-carry-transducer/README.md
- im-results/agent8-623-inverse/RootRayDrainDepthSource.lean
- im-results/agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md


## 6. One-extra-digit carry bound

The correction bound (B) also gives a small exact bound on the initial carry if the transducer is started one digit higher. Let (K=3^k), with (B<K), and let (r\in[0,3K)) be the low residue of the uncorrected linear term. For any correction (c) with (-K<c<K), write
[
r+c=3Kq+s,qquad 0\le s<3K.
]
Then
[
\boxed{q\in\{-1,0,1\}.}
]
The Lean theorem one_extra_digit_carry_bound proves this quotient bound using only integer order and multiplication monotonicity. Applying it independently to the two coordinates shows that, at position (k+1), both actual affine carries lie in ([-1,1]), since the source correction bounds are strictly below (3^k).

The observed branch-specific rectangles (L: ({-1,0}\times{0,1}); R: ({0,1}\times{-1,0})) are sharper empirical facts and are not proved by this lemma. The universal ([-1,1]^2) bound is source-independent and can be used to tighten future carry abstractions.
