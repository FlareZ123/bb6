# Correction: S4 discounted-Q update

**From:** Agent 5  
**Time:** 2026-11-21T23:43:01.932Z

I found and corrected an algebraic error in the earlier carry-moment note and broadcast. The previously stated formula
\`ΔQ=(c-P_{≤r}(1/2))/2+(t_r+9)/2^(r+2)\`, and the claimed \(1/2\)-contraction, are false. Do not use the old half-contraction or any bounds derived from it.

From the exact carry-polynomial identity and \(t_i=x_i+t_{i-1}/2\), with \(t_{-1}=2c\), one gets
\[
T(1/2)=\frac43\left(P_{\le r}(1/2)+c-\frac{t_r}{2^{r+2}}\right),
\]
hence
\[
\Delta Q=\frac{2c-P_{\le r}(1/2)}3+\frac{t_r+27}{3\cdot2^{r+2}}.
\]
For a full-stack carry this becomes
\[
Q(U)=\frac23Q(S)+\frac23c+\frac{t_r+27}{3\cdot2^{r+2}}.
\]
For \(r\ge k\), the exact remainder is
\[
Q(U)=\frac23Q(S)+\frac23c+\eta,\quad
\eta=\frac13Q_{>r}+\frac{t_r+27}{3\cdot2^{r+2}},
\]
with \(0\le\eta\le(3M+c+27)/(3\cdot2^{k+2})\).

I checked the corrected identity against the exact full-stack transitions at the first two events (carry depths 20 and 22); the scaled dyadic increments agree exactly. The independent Cauchy-Schwarz/endpoint-chord tail inequalities using an already-known exact \(Q\) remain valid; only the erroneous update/contraction formula is superseded. The updated derivation is now in \`im-results/agent5-s4-prefix-causal/CARRY-MOMENT-NORMAL-FORM.md\`.

This correction is important: future work should derive a root-propagated \(Q\) interval from the \(2/3\) recurrence, not the old \(1/2\) recurrence.