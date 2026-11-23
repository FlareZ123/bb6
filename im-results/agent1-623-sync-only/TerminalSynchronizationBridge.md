# Terminal-event bridge through full-rectangle synchronization for machine #623

**Status:** exact arithmetic reduction conditional on the maintained terminal-predecessor strip theorem. It is not yet an all-time root exclusion because full-rectangle synchronization still needs an all-time proof on the authentic orbit.

This note combines the exact four-residue synchronization criterion with the existing terminal-predecessor strips.

## 1. A scale-local synchronization barrier

Let \(X,Y\in\mathbb Z\), let \(s\ge0\), and put \(P=3^s\). Take any length-\(n\) digit-pair word, \(n\ge2\), cut from positions \(s,\ldots,s+n-1\) of the standard floor-division ternary expansions of \(X,Y\). Let \(M=3^n\) and let \(X_w,Y_w\in[0,M)\) be the corresponding word values.

Write \(X=P Q_X+r_X\), \(Y=P Q_Y+r_Y\), with \(0\le r_X,r_Y<P\). Then \(X_w\equiv Q_X\pmod M\) and \(Y_w\equiv Q_Y\pmod M\).

### Left dangerous residual

Put \(Z_L=X-3Y\). Then

\[Z_L=P(Q_X-3Q_Y)+(r_X-3r_Y),\]

with \(-3P<r_X-3r_Y<P\). If \(|Z_L|<P\), the integer \(Q_X-3Q_Y\) must lie in \(\{-1,0,1,2,3\}\). Therefore

\[[X_w-3Y_w]_M\in\{M-1,0,1,2,3\}.\]

But the exact left synchronization criterion requires

\[4\le[X_w-3Y_w]_M\le M-3.\]

Hence

\[\boxed{|X-3Y|<3^s\Longrightarrow\text{the full L rectangle does not synchronize on the word beginning at }s.}\]

### Right dangerous residual

Put \(Z_R=4X+3Y\). Then

\[Z_R=P(4Q_X+3Q_Y)+(4r_X+3r_Y),\]

with \(0\le4r_X+3r_Y<7P\). If \(|Z_R|<P\), the integer \(4Q_X+3Q_Y\) lies in \(\{-7,-6,-5,-4,-3,-2,-1,0\}\). Consequently

\[[4X_w+3Y_w]_M\in\{M-7,M-6,\ldots,M-1,0\}.\]

The exact right synchronization criterion requires

\[2\le[4X_w+3Y_w]_M\le M-8.\]

Hence

\[\boxed{|4X+3Y|<3^s\Longrightarrow\text{the full R rectangle does not synchronize on the word beginning at }s.}\]

These implications are exact and do not mention the minimized DFA.

## 2. Apply to the #623 S-window

For a canonical #623 state use

\[X=2g-\gamma_s,\qquad Y=6q,\]

so

\[X-3Y=2(g-9q)-\gamma_s,\]

\[4X+3Y=2(4g+9q)-4\gamma_s.\]

Let \(\ell_S\) be the S-window scale exponent and \(B=34\ell_S+122\). Let \(k\) be least with \(3^k>B\). The correction-only S-window begins at \(s=k+2\), therefore

\[3^s=3^{k+2}>9B=306\ell_S+1098.\]

The maintained sharpened terminal-predecessor theorem says that for canonical depth \(n\ge10\), a terminal successor has a predecessor satisfying one of

\[|g-9q|\le23n+140,\]

or

\[|4g+9q|\le23n+140.\]

The same depth comparison used in the S-window construction gives \(n\le\ell_S\).

In the left case, using \(\gamma_s\le18\),

\[|X-3Y|\le2(23n+140)+18\le46\ell_S+298<306\ell_S+1098<3^{k+2}.\]

In the right case,

\[|4X+3Y|\le2(23n+140)+4\cdot18\le46\ell_S+352<306\ell_S+1098<3^{k+2}.\]

The scale-local barrier therefore gives the exact implication

\[\boxed{\text{terminal successor at depth }n\ge10\Longrightarrow\text{the predecessor correction-only S-window fails full-rectangle synchronization.}}\]

The failing branch is L for the far strip \(g-9q\), and R for the near strip \(4g+9q\).

## 3. Research consequence

This converts the nonhalting goal into a particularly clean invariant target: after the separately handled small-depth prefix, every authentic correction-only S-window synchronizes both full carry rectangles. If that invariant is proved, the terminal-predecessor strip theorem immediately excludes every later terminal event.

The current 9,968-transition authentic replay satisfies the synchronization invariant everywhere, with first synchronization by symbol 12. That remains finite evidence; the point of this bridge is that **no nonmonochromatic-output flag is needed for the terminal contradiction**. The old common-reset language was stronger than necessary.

The remaining all-time problem is now precisely to prove the four modular inequalities in ExactSynchronizationCriterion.md along the authentic root orbit. This is the same 3-adic separation problem exposed by the dangerous residuals, but with the proof target reduced to explicit scalar inequalities.
