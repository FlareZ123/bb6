# Phase-corrected equivalence of the #623 global signed and canonical \((p,q)\) cocycles

**Status:** exact algebraic conjugacy between two already-established source-derived recurrence tables. This note repairs an overbroad withdrawal of their global-coordinate relationship. It is **not** a conjugacy of arbitrary truncated S-window words without boundary carries, and it is not an all-time root decision. The combined source-imported Lean theorem has not been compiled.

## Coordinate statement

For each canonical #623 section state, write
\[
p=|a-d|,\quad q=\min(a,d),\quad g=p-3q.
\]
Let the input sector \(s\) be LO, LE, RO, or RE, and define its integer phase
\[
\gamma_{\rm LO}=18,\quad
\gamma_{\rm LE}=10,\quad
\gamma_{\rm RO}=2,\quad
\gamma_{\rm RE}=4.
\]
The signed-coordinate normal form uses the **global integer** pair
\[
X=2g-\gamma_s,\qquad Y=6q.
\]
In the unimodular basis \(U=Y,\ V=X+Y\), therefore
\[
\boxed{U=6q,\qquad V=2p-\gamma_s.}
\tag{1}
\]
In particular \(P:=V+\gamma_s=2p,\ Q:=U=6q\). The unshifted equation \(P=V\) is **false**; the phase \(\gamma_s\) is essential. On RO/RE, the signed \(X/2\) is *not* the old-ray distance \(h=(g-1)/2\) or \((g-2)/2\): the factor of two is another reason not to substitute old-ray coordinates naïvely.

The correct output-sector table is
\[
\begin{array}{c|cc}
s&\text{left output}&\text{right output}\\\hline
\mathrm{LO}&\mathrm{LO}&\mathrm{RO}\\
\mathrm{LE}&\mathrm{LE}&\mathrm{RE}\\
\mathrm{RO}&\mathrm{LE}&\mathrm{RE}\\
\mathrm{RE}&\mathrm{LO}&\mathrm{RO}
\end{array}
\tag{2}
\]

## Exact correction transport

The canonical unsorted output counters are \(p+\beta_s\) and \(3q+\delta_s\); put \(T_s=\delta_s-\beta_s\).
Using the **full** evaluator count \(R\) (so the right-even old split count is \(r=R-1\)) gives
\[
\begin{array}{c|cc}
s&\beta_s&\delta_s\\\hline
\mathrm{LO}&-D-5&2D+2R+14\\
\mathrm{LE}&-D-2&2D+2R+8\\
\mathrm{RO}&4-D&2D+2R\\
\mathrm{RE}&1-D&2D+2R+3
\end{array}
\tag{3}
\]
with the signed first-counter drop \(D\) in the established canonical convention. No change of drain interpretation is hidden in the RE row.

The two canonical branch maps are exactly
\[
L:\quad p'=p-3q-T_s,\quad q'=3q+\delta_s,
\]
\[
R:\quad p'=3q+T_s-p,\quad q'=p+\beta_s.
\tag{4}
\]
Let \(t\) denote the actual output sector from (2). Substituting (4) into
\(X'=2(p'-3q')-\gamma_t,\;Y'=6q'\)
gives the signed-coordinate updates
\[
L:\quad X'=X-3Y+\kappa,\quad Y'=3Y+\phi,
\]
\[
R:\quad X'=-4X-3Y+\kappa,\quad Y'=3X+3Y+\phi,
\tag{5}
\]
where, **exactly**,
\[
\boxed{
\begin{array}{c|cc}
&\kappa&\phi\\\hline
L&\gamma_s-\gamma_t+2\beta_s-8\delta_s&6\delta_s\\
R&2\delta_s-8\beta_s-4\gamma_s-\gamma_t&3\gamma_s+6\beta_s
\end{array}}
\tag{6}
\]
These are genuine global-coordinate conjugacy equations, not estimates. Substitution of the four rows (3) and actual successor phases (2) agrees **coefficient by coefficient** in both \(D,R\) with every one of the eight definitions of \(\mathrm{corrC},\mathrm{corrF}\) in [SignedCoordinateNormalForm.lean](../agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.lean). The separate existing Lean source already verifies that correction table; the conjugacy here has not been compiled as one original-source imported theorem.

Adding the corrections gives the particularly economical identities
\[
L:\quad \kappa+\phi=\gamma_s-\gamma_t-2T_s,
\]
\[
R:\quad \kappa+\phi=2T_s-\gamma_s-\gamma_t.
\tag{7}
\]
In the \((U,V)\) basis of [TwoCoordinate3AdicCocycle.md](TwoCoordinate3AdicCocycle.md), equations (5)–(7) recover the source-derived scaled canonical recurrence with its phase correctly restored:
\[
\boxed{\begin{array}{c|cc}
 &Q'&P'\\\hline
L&3Q+6\delta_s&P-Q-2T_s\\
R&3P+6\beta_s&Q-P+2T_s
\end{array}}
\tag{8}
\]
where always \(Q=U\) and \(P=V+\gamma_s\), and after the transition \(P'=V'+\gamma_t\).

The proof of (8) is one substitution: for L,
\(V'+\gamma_t=(V-U+\kappa+\phi)+\gamma_t=P-Q-2T_s\);
for R,
\(U'=3V+\phi=3(P-\gamma_s)+(3\gamma_s+6\beta_s)=3P+6\beta_s\), and
\(V'+\gamma_t=U-V+\kappa+\phi+\gamma_t=Q-P+2T_s\).

## Why the previous withdrawal must be narrowed

The earlier rejected claim was *not* safe as a **window-transducer closure**: truncating global signed coordinates to the moving ternary S-window introduces a low-boundary carry. In particular, if \(P_0=3^s\) is the window start scale and \(U=P_0Q_U+r_U,\ V=P_0Q_V+r_V\), then the actual word is
\[
U_w=[Q_U]_{3^n},\qquad
V_w=[Q_V-c_V]_{3^n},\quad
c_V=\mathbf1_{r_V<r_U}.
\]
This is the exact [WindowQuotientInterface.md](WindowQuotientInterface.md) correction; the successor sector phase, dynamic shift index, and transducer start carry must also be preserved. Therefore (8) does **not** imply a carry-free one-step S-window synchronization invariant or a Markov phase/drain product. The explicit counterexample in [SynchronizationPropagationObstruction.md](SynchronizationPropagationObstruction.md) remains valid.

However, at the **global integer** level, the stronger withdrawal “there is no established relation between canonical \(p,q\) and the signed \(U,V\)” is unnecessarily restrictive: equation (1) and the exact eight-row equality (6) provide that relation. They allow the source-derived \((D,R)\) 27-state drain digit lift to be used for the global cocycle **with the phase adjustment**. The remaining challenge is precisely its composition with the finite low-window carry and the moving S-window cut, not a mismatch of global root coordinates.

## Check and research boundary

[verify_global_signed_pq_bridge.js](verify_global_signed_pq_bridge.js) compares the two algebraic correction descriptions as affine integer coefficient triples for all eight sector/branch cases. This reproducer is finite arithmetic over constant coefficients, while the derivation (1)–(8) is a universal symbolic identity valid for all integers obeying the canonical recurrence and specified phase map.

Neither (8) nor this consistency check proves that authentic blank-orbit windows synchronize. A universally quantified authentic-root carry/quotient compatibility invariant is still missing. The bridge is retained in \`im-results/\`; no BB(6) upper bound, lower-bound improvement or halting decision is claimed.
