# Unimodular two-coordinate form of the #623 synchronization cocycle

**Status:** exact algebraic reduction; not yet an all-time synchronization proof.

This note refactors the existing (A,B) cocycle in SynchronizationResidueCocycle.md. The change of coordinates is unimodular, so it loses no information. Its benefit is that the four synchronization forms become two primitive linear forms and two exact ternary rescalings.

## 1. Coordinates

Keep the signed S-window coordinates X,Y, and define
\[
U:=Y,\qquad V:=X+Y.
\]
The map (X,Y) -> (U,V) has determinant -1, hence is an invertible integer change of coordinates. In the canonical root coordinates X=2g-gamma_s, Y=6q, this is
\[
U=6q,\qquad V=2p-\gamma_s,
\]
using g=p-3q.

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
In particular, the four tests are not four unrelated residues: they are the two forms V-4U, 4V-U, together with 3U, 3V.

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

Write the existing source/drain corrections as kappa,phi, to avoid confusing them with the four synchronization forms. The maintained updates are

Left:
\[
X'=X-3Y+\kappa,\qquad Y'=3Y+\phi.
\]

Right:
\[
X'=-4X-3Y+\kappa,\qquad Y'=3X+3Y+\phi.
\]

Substituting U=Y, V=X+Y gives the simpler exact cocycle.

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
with determinants 3 and -3, respectively. These are conjugate to the previously recorded (A,B) matrices by an integer unimodular transformation; the determinant-±3 fact is unchanged.

The inverse recurrences are particularly useful:

- after a left step,
  \[
  U=(U'-\phi)/3,\qquad V=V'+U-\kappa-\phi;
  \]
- after a right step,
  \[
  V=(U'-\phi)/3,\qquad U=V'+V-\kappa-\phi.
  \]

So backward reconstruction divides exactly one of the two coordinates by three at each step.

## 4. Corrections from the exact (p,q) source map

The correction pair is not arbitrary. Let beta,delta be the sector-dependent source/drain corrections from the exact (p,q) cocycle, let T=delta-beta, and let gamma_s,gamma_s' be the current and next sector phases. The phase values are
\[
\gamma_{LO}=18,\quad \gamma_{LE}=10,\quad
\gamma_{RO}=2,\quad \gamma_{RE}=4.
\]
The (p,q) map is
\[
p'=p-3q-T,\quad q'=3q+\delta
\]
on the left-output branch, and
\[
p'=3q+T-p,\quad q'=p+\beta
\]
on the right-output branch.

Substitution into U=6q and V=2p-gamma_s gives the exact corrections:

**Left-output branch**
\[
\phi_L=6\delta,\qquad
\kappa_L=\gamma_s-\gamma_{s'}+2\beta-8\delta.
\]
Equivalently, kappa_L+phi_L = gamma_s-gamma_s'-2T.

**Right-output branch**
\[
\phi_R=3\gamma_s+6\beta,\qquad
\kappa_R=2\delta-8\beta-4\gamma_s-\gamma_{s'}.
\]
Equivalently, kappa_R+phi_R = 2T-gamma_s-gamma_s'.

Thus phi is a multiple of 6 on both branches: this is immediate for phi_L, and for phi_R it follows because every gamma_s is even. Equivalently, U'=6q' and V=2p-gamma_s is even, so phi_R=U'-3V is divisible by 6. These formulas connect the two-register cocycle directly to the source drain statistics; the remaining phase input is the exact sector transition s -> s'.

The corresponding correction table for beta,delta,T is in im-results/agent3-623-pq-cocycle/README.md, and the phase values and transition table are in im-results/agent32-623-phase-automaton/RootPhaseInvariant.md. The latter also warns that its observed finite phase set is not yet proved invariant.

## 5. Why this is useful

The all-time problem can now be stated as avoidance, along the exact two-coordinate cocycle, of the four allowed residue intervals displayed in Section 2. More importantly, the inverse recurrences expose a ternary digit at every backward step. A prospective proof can therefore track the pair (U,V) as a two-register 3-adic process: the left branch shifts the U-register, while the right branch shifts the V-register. The correction phi supplies the low ternary digit, and kappa+phi supplies the affine carry in the other register.

This is an exact reparameterization and an actionable reduction, **not** a proof that the authentic orbit avoids the bands. The next mathematical task is to combine the explicit beta,delta,gamma correction formulas with a proved boundary-carry invariant for the authentic S-window quotients. The low-boundary carry warning in WindowQuotientInterface.md still applies: global (U,V) alone cannot be substituted naively for every shifted S-window quotient.
