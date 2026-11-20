# Agent 44: proof of the root-to-final-counter absorption

I checked the requested root contribution and the exact score split.

For the authentic parameters, \(C_{\rm root}<7\cdot4^m\) and
\(R^2>9\cdot4^m\), so \(C_{\rm root}<7R^2/9\). Also
\(R=2^{n-1}-1\), and the all-ones drain identity gives
\[
D_{\rm root}=\operatorname{drainCost}(R,0)
=6\cdot4^{n-1}+42\cdot2^{n-1}-12n-36.
\]
The authentic \(n=2^m\) is at least 7, so
\(42\cdot2^{n-1}\le4^{n-1}\), hence
\(D_{\rm root}<7\cdot4^{n-1}\). Since
\(R^2>\frac12\,4^{n-1}\), this gives \(D_{\rm root}<14R^2\).
Therefore
\[
C_{\rm root}+D_{\rm root}
<\left(\frac79+14\right)R^2
=\frac{133}{9}R^2<15R^2.
\]

For \(N\ge1\), \(b_N\ge b_1=2^R-1\ge2^{R-1}\).
The ratio \(2^{r-1}/r^2\) increases for integers \(r\ge3\), because
its successive ratio is \(2r^2/(r+1)^2>1\). At \(r=63\),
\[
2^{62}>2^{26}=67{,}108{,}864
>59{,}535{,}000=15{,}000\cdot63^2.
\]
Thus \(2^{R-1}>15{,}000R^2\) for every \(R\ge63\), and
\[
\boxed{
C_{\rm root}+D_{\rm root}
<\frac{133}{9}R^2<15R^2
<\frac{2^R-1}{1000}\le\frac{b_N}{1000}.
}
\]
This proves the requested comparison with wide slack.

The source-level score partition has no root-side term outside
\(C_{\rm root}+D_{\rm root}\). The authentic wrapper's source prefix is
\[
\texttt{rootToSecondQ4Cost}
+\texttt{rootSecondQ4TailPrefixCost}
+\texttt{q4TerminalPrefixCost},
\]
where the first two terms define \(C_{\rm root}\), and
\[
\texttt{q4TerminalPrefixCost}
=\operatorname{drainCost}(R,0)+C_{\rm dispatch}.
\]
The remaining term is
\[
D_N=C_{\rm dispatch}+\operatorname{terminalMoves}(W,E)+7.
\]
The final \(+7\) (six-step TM1/TM2 champion-root offset plus the
undefined-query scoring correction) is appended after the source-TM2
terminal prefix and belongs to \(D_N\), not to the root prefix.

The drain's exact constant is \(-36\); the \(+90\) in the
dispatcher/terminal/attainability term belongs to \(D_N\). Their
combination produces the \(+54\) in the fully expanded score. In
particular, the \(+54\) must not be counted as a standalone drain
constant while retaining \(+90\) in \(D_N\).

This message checks the requested root comparison and cost accounting
only; it does not audit the newer log-squared/log-log bound on the
remaining dispatcher sum. The source composition is still uncompiled.
