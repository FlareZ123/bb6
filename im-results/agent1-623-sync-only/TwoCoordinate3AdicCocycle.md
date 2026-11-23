# Unimodular two-coordinate form of the #623 synchronization cocycle

**Status:** exact algebraic reduction; not yet an all-time synchronization proof.

This note refactors the existing (A,B) cocycle in SynchronizationResidueCocycle.md. The change of coordinates is unimodular, so it loses no information. Its benefit is that the four synchronization forms become two primitive linear forms and two exact ternary rescalings.

## 1. Coordinates

Keep the signed S-window coordinates X,Y, and define
\[
U:=Y,\qquad V:=X+Y.
\]
The map (X,Y) -> (U,V) has determinant -1, hence is an invertible integer change of coordinates. No additional identification with the (p,q) coordinates is needed for this change of basis.

Recall
\[
A=X-3Y,\qquad B=3Y.
\]
Then the four scalar forms in the exact synchronization criterion are
\[
\boxed{
A=V-4U,\quad B=3U,\quad
4A+5B=4V-U,\quad 3A+4B=3V.
}
\]
Thus the four tests are the two forms V-4U, 4V-U, together with 3U, 3V.

## 2. Exact residue criterion in the new coordinates

Put M=3^n and N=3^(n-1). The full-rectangle criterion from ExactSynchronizationCriterion.md is equivalent to
\[
4\le [V-4U]_M\le M-3,
\]
\[
2\le [4V-U]_M\le M-8,
\]
\[
1\le [U]_N\le N-2,
\]
\[
1\le [V]_N\le N-3.
\]

The last two equivalences are exact, not estimates. For every integer z,
\[
[3z]_{3^n}=3[z]_{3^{n-1}},
\]
because the representative on the right lies in [0,3^n). Thus 2 <= [3U]_M <= M-5 is precisely 1 <= [U]_N <= N-2, and 2 <= [3V]_M <= M-7 is precisely 1 <= [V]_N <= N-3.

This removes one ternary digit from each of the two scale tests. The remaining full-depth exclusions are the two primitive forms V-4U and 4V-U.

## 3. Exact branch cocycle

Write the exact signed-coordinate corrections as kappa,phi (the existing source file calls them C,F). The maintained updates are

Left:
\[
X'=X-3Y+\kappa,\qquad Y'=3Y+\phi.
\]

Right:
\[
X'=-4X-3Y+\kappa,\qquad Y'=3X+3Y+\phi.
\]

Substituting U=Y, V=X+Y gives

**Left**
\[
\boxed{U'=3U+\phi,\qquad V'=V-U+\kappa+\phi.}
\]

**Right**
\[
\boxed{U'=3V+\phi,\qquad V'=U-V+\kappa+\phi.}
\]

The corresponding linear matrices are
\[
L_{UV}=\begin{pmatrix}3&0\\-1&1\end{pmatrix},
\qquad
R_{UV}=\begin{pmatrix}0&3\\1&-1\end{pmatrix},
\]
with determinants 3 and -3, respectively. These are conjugate to the previously recorded (A,B) matrices by an integer unimodular transformation.

The inverse recurrences are:

- after a left step, U=(U'-phi)/3 and V=V'+U-kappa-phi;
- after a right step, V=(U'-phi)/3 and U=V'+V-kappa-phi.

So backward reconstruction divides exactly one of the two coordinates by three at each step.

## 4. Exact corrections from the Lean-checked signed normal form

The existing SignedCoordinateNormalForm.lean defines the exact corrections corrC and corrF in terms of the full-drain statistics D and R. In this note kappa=corrC and phi=corrF. R is the full evaluator-call count; in the RE sector it includes the initial evaluator.

| Sector | Branch | kappa | phi |
|---|---|---|---|
| LO | Left | -18D - 16R - 122 | 12D + 12R + 84 |
| LE | Left | -18D - 16R - 68 | 12D + 12R + 48 |
| RO | Left | -18D - 16R | 12D + 12R |
| RE | Left | -18D - 16R - 36 | 12D + 12R + 18 |
| LO | Right | 12D + 4R - 6 | -6D + 24 |
| LE | Right | 12D + 4R - 12 | -6D + 18 |
| RO | Right | 12D + 4R - 44 | -6D + 30 |
| RE | Right | 12D + 4R - 20 | -6D + 18 |

Every phi is a multiple of 6. The source Lean file proves the correction identities, signed updates, and correction bounds; this note only changes coordinates on those already-defined updates.

## 5. One-digit quotient and low-digit reduction

Since phi is divisible by 6, the active register can be divided by 3 exactly:

**Left**
\[
U'/3=U+\phi/3,\qquad V'=V-U+\kappa+\phi.
\]

**Right**
\[
U'/3=V+\phi/3,\qquad V'=U-V+\kappa+\phi.
\]

The correction sums kappa+phi simplify as follows:

| Sector | Left: kappa+phi | Right: kappa+phi |
|---|---|---|
| LO | -6D - 4R - 38 | 6D + 4R + 18 |
| LE | -6D - 4R - 20 | 6D + 4R + 6 |
| RO | -6D - 4R | 6D + 4R - 14 |
| RE | -6D - 4R - 18 | 6D + 4R - 2 |

Because U is divisible by 3, the passive-register low digit is therefore

\[
V'\equiv
\begin{cases}
V-R+1 & \text{left, LO or LE},\\
V-R & \text{left, RO or RE},\\
-V+R & \text{right, LO or LE},\\
-V+R+1 & \text{right, RO or RE}
\end{cases}
\pmod3.
\]

The signed drop D disappears modulo 3. The remaining low-digit input is the sector, branch, current V digit, and full-drain count R modulo 3. This is an exact low-digit rule; it is not yet a finite invariant because the source drain state and moving-window boundary carry must still be retained.

## 6. Why this is useful

The all-time problem can now be stated as avoidance, along the exact two-coordinate cocycle, of the four allowed residue intervals displayed in Section 2. The inverse recurrences expose a ternary digit at every backward step. A prospective proof can track (U,V) as a two-register 3-adic process, with the exact correction pair supplied by the verified drain-statistic table.

The natural next object is a carry automaton retaining the sector, branch, R mod 3, and the moving-window low-boundary carry. The global (U,V) coordinates alone cannot be substituted naively for every shifted S-window quotient; the caveat in WindowQuotientInterface.md still applies.

This is an exact reparameterization and a more explicit low-digit reduction, **not** a proof that the authentic orbit avoids the synchronization bands or a solution of BB(6).


## 7. Boundary carries in the same (U,V) coordinates

The WindowQuotientInterface.md caveat can also be written naturally in this basis. For a window starting at position s, put P=3^s and decompose
\[
U=PQ_U+r_U,\qquad V=PQ_V+r_V,
\]
with
\[
0\le r_U<P,\qquad r_U\le r_V<r_U+P.
\]
Indeed U=Y, V=X+Y, so r_U=r_Y and r_V=r_X+r_Y. The window coordinates are exactly
\[
U_w=[Q_U]_{3^n},\qquad V_w=[Q_V]_{3^n}.
\]

The four low remainders that create the synchronization carries become
\[
r_V-4r_U,\qquad 3r_U,\qquad 4r_V-r_U,\qquad 3r_V.
\]
Consequently their quotient carries are
\[
c_A=\left\lfloor\frac{r_V-4r_U}{P}\right\rfloor,\quad
c_B=\left\lfloor\frac{3r_U}{P}\right\rfloor,\quad
c_C=\left\lfloor\frac{4r_V-r_U}{P}\right\rfloor,\quad
c_D=\left\lfloor\frac{3r_V}{P}\right\rfloor.
\]
The wedge constraint on (r_U,r_V) gives exactly
\[
c_A\in\{-3,-2,-1,0\},\quad c_B\in\{0,1,2\},
\]
\[
c_C\in\{0,1,2,3,4,5,6\},\quad c_D\in\{0,1,2,3,4,5\}.
\]
These are the same finite carry ranges as the original X,Y formulation, but now both the global cocycle and the window boundary state use the same two-register basis.

This does not eliminate the carries; it packages them as a constrained remainder pair
\[
0\le r_U<P,\qquad r_U\le r_V<r_U+P.
\]
A finite-state proof still has to track the induced carry transitions as s changes. The advantage is that the affine branch update and the boundary quotient interface can now be composed without changing coordinate systems.
