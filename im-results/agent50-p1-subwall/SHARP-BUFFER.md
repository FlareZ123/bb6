# Sharper dyadic buffer for the P1 right-five wall (19 November 2026)

## Result

The existing source energy induction uses
\[
T_{\rm old}(m)=16(M+n+6)(M-m+1)2^{M-m}.
\]
Its only role in the depth-two case is to satisfy
\[
8T(m+3)+16(m+n+6)\le T(m).
\]
The factor \(M-m+1\) is unnecessary. Set
\[
A=M+n+6,\qquad
T_{\rm sharp}(m)=3A\bigl(2^{M-m}-1\bigr)+1.
\]
For \(n\ge14\), \(m+3\le M\), and \(M\le n\),
\[
\begin{aligned}
T_{\rm sharp}(m)-8T_{\rm sharp}(m+3)
&=21A-7\\
&\ge16A\\
&\ge16(m+n+6).
\end{aligned}
\]
The positive \(+1\) is important: it ensures \(T_{\rm sharp}(M)=1\), so an exact wall is still excluded at the budget endpoint.

For every \(m\le M\),
\[
T_{\rm sharp}(m)\le3(M+n+6)2^M+1.
\]
Thus the old sufficient condition
\[
64(n+2)^2 2^M\le2^n
\]
can be replaced by the substantially weaker condition
\[
\boxed{3(M+n+6)2^M+1\le2^n.}
\]
Since \(M\le n\), the simpler sufficient condition
\[
6(n+3)2^M+1\le2^n
\]
also works.

## Consequence for the original-source induction

The existing proof of source_energy_budget_gap_param uses the threshold only in three places:

1. A shallow \(t\le1\) step establishes \(W_{\rm child}+2^n\le12\cdot2^n\); the new bound \(T_{\rm sharp}\le2^n\) initializes the low-side buffer.
2. A depth-two step uses the exact cocycle
   \[
   8W'=W+84\cdot2^n+16(m+n+6).
   \]
   The inequality above propagates the buffer.
3. A depth-\(t\ge3\) step moves strictly above the wall, exactly as before.

The root is already strictly above the wall. Therefore the same induction proves, for every original-source CountCone and every \(m\le M\),
\[
W>12\cdot2^n
\quad\text{or}\quad
W+T_{\rm sharp}(m)\le12\cdot2^n.
\]
The exceptional-last-reset argument is unchanged. In particular, the existing source_right_five_parametric_cost_gap proof should lift verbatim after replacing its old buffer and witness lemmas:
\[
\boxed{m>n+2+M}
\]
whenever \(M\le n\) and \(3(M+n+6)2^M+1\le2^n\).

For \(M\) near its largest admissible value, this reaches
\[
M=n-\log_2 n-O(1),
\]
rather than the previous \(M=n-2\log_2 n-O(1)\). The improvement is about one full \(\log_2 n\) in the certified prefix-cost window.

## Scope and next step

This is an exact arithmetic super-solution for the existing source invariant, not a new P1 verdict. It improves the low-cost energy window but does not control prefixes whose cost exceeds the new \(M\), and it does not establish blank-root reachability.

The next implementation step is to add a separate Lean leaf defining thresholdSharp, proving its decay and witness bounds, then copy the source induction with this threshold. The current local shell/Lean runtime was unavailable in this invocation, so this note is a paper-level derivation pending kernel verification.