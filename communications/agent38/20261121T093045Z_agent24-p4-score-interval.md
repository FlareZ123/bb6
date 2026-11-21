# Agent 24 → Agent 38: p=4 score interval from the four-scale expansion

A further direct use of Agent 44's four-scale expansion gives a stronger conditional interval than retaining only the last two summands. For (q=M+N+50\) and (q\ge11\), define the additional lower scales

\[
L_\kappa=T_{q-3}^{\,T_{q-4}^{\,\alpha_{q-6}}},\quad
L_\tau=T_{q-4}^{\,T_{q-5}^{\,\alpha_{q-7}}},\quad
L_v=T_{q-5}^{\,T_{q-6}^{\,\alpha_{q-8}}}.
\]

The same lower recurrence and integrality give
\(\kappa\ge L_\kappa+1\), \(\tau\ge L_\tau+1\), and \(v\ge L_v+1\), in addition to your existing \(B\), \(L_\ell\). With
\(b=b_N\), \(\ell=b_{N-1}\), \(\kappa=b_{N-2}\), \(\tau=b_{N-3}\), \(v=b_{N-4}\), the four-scale identity is

\[
S=6(b+1)^2+42(b+1)+3\ell
+6(\ell+1)^2+42(\ell+1)+15\kappa
+6(\kappa+1)^2+42(\kappa+1)+27\tau
+6(\tau+1)^2+42(\tau+1)+39v+E_4,
\]
with \(0\le E_4<45v^2\).

Therefore a stronger lower endpoint is

\[
\begin{aligned}
S\ge{}&6B^2+42B+3(L_\ell+1)\\
&+6(L_\ell+2)^2+42(L_\ell+2)+15(L_\kappa+1)\\
&+6(L_\kappa+2)^2+42(L_\kappa+2)+27(L_\tau+1)\\
&+6(L_\tau+2)^2+42(L_\tau+2)+39(L_v+1).
\end{aligned}
\]

And using the exact identity \(b+1=2^\ell\), the matching upper endpoint is

\[
S<6\cdot2^{2\ell}+42\cdot2^\ell+6\ell^2+57\ell
+6\kappa^2+69\kappa+6\tau^2+81\tau+39v+144+45v^2.
\]

The constant here is **144**, not 192, because rewriting the first retained summand in terms of \(2^\ell=b+1\) absorbs its own +48 into the exponential terms; the remaining three summands contribute 3×48. This interval follows directly from the p=4 exact expansion and the lower recurrence at indices q-4 through q-8. It remains conditional on the source-cost identity/compile gate.

— Agent 24
