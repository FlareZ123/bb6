# Root source-carry inclusion in the full reset rectangles

**Status:** exact arithmetic implication from the source-carry formulas and the mass-indexed correction bound. The Lean consumer still needs to connect the formulas/hypotheses to the authentic root transition.

Let \(K=3^k\), so the source-carry denominator is \(3K=3^{k+1}\). The digit residues satisfy
\[
0\le x_{K1}<3K,\qquad 0\le x_K<K,\qquad 0\le y_K<K,
\]
where \(x_{K1}=x\bmod 3K\), \(x_K=x\bmod K\), \(y_K=y\bmod K\). The correction bound gives \(|C|,|F|\le B\), and the window choice has \(B<3^k=K\). Thus \(-K\le C,F\le K\).

The sourceCarry formulas in s_window_boundary_phases.js are:

**Branch L**
\[
c_0=\left\lfloor\frac{x_{K1}-3y_K+C}{3K}\right\rfloor,\qquad
c_1=\left\lfloor\frac{3y_K+F}{3K}\right\rfloor.
\]
The numerator bounds are
\[
-4K+3\le x_{K1}-3y_K+C\le4K-1,
\]
\[
-K\le3y_K+F\le4K-3.
\]
Consequently
\[
-2\le c_0\le1,\qquad -1\le c_1\le1,
\]
which is contained in the full L start rectangle \([-2,2]\times[-2,2]\).

**Branch R**
\[
c_0=\left\lfloor\frac{-x_{K1}-3x_K-3y_K+C}{3K}\right\rfloor,\qquad
c_1=\left\lfloor\frac{3x_K+3y_K+F}{3K}\right\rfloor.
\]
The numerator bounds are
\[
-10K+7\le -x_{K1}-3x_K-3y_K+C\le K,
\]
\[
-K\le3x_K+3y_K+F\le7K-6.
\]
Consequently
\[
-4\le c_0\le0,\qquad -1\le c_1\le2,
\]
which is contained in the full R start rectangle \([-4,1]\times[-2,2]\).

The previous digit pair is always in \(\{0,1,2\}^2\), exactly the nine previous-pair choices included by reset_poststate_dfa.js. Hence the actual source start state is inside the full L/R rectangle whenever the correction bound and sourceCarry formula hold.

## How the mass-indexed Lean bounds supply B

For root mass \(S=a+d\), let \(\ell=\mathrm{massIndex}(S)\), so \(S+3\le\tau(\ell)\). With \(q=\min(a,d)\) and sector offset in \(\{3,2,-1,1\}\), the drain input satisfies
\[
b=q+\mathrm{offset}\le q+3\le S+3\le\tau(\ell).
\]
Agent 49's drainB_digit_source_correction_interface_mass then gives
\[
|C|,|F|\le34\ell+122=B.
\]
The S-window uses the least \(k\) with \(3^k>B\), so the inequalities above apply with \(K=3^k\).

This is a direct proof of the *rectangle inclusion*; it does not use the one_extra_digit_carry_bound_closed lemma (which bounds only an isolated correction quotient, not the total carry). The remaining formal integration is to establish the exact sourceCarry formulas and mass hypotheses for every authentic root transition, then connect the resulting start state to the reset automaton's finite common-reset validation over all 225 L and 270 R starts.
