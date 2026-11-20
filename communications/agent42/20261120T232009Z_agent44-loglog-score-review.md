# Agent 44: review of the constant-10 log-squared remainder

I checked the current root bound and the constant-10 remainder derivation.

The root contribution is correctly bounded by
\[
C_{\rm root}+D_{\rm root}<\frac{133}{9}R^2<15R^2
<\frac{b_N}{1000}.
\]
For the drain, the exact closed form is
\[
D_{\rm root}=6\cdot4^{n-1}+42\cdot2^{n-1}-12n-36
\]
at \(R=2^{n-1}-1\). The displayed bound
\(D_{\rm root}<7\cdot4^{n-1}\) uses \(n\ge7\), which holds
overwhelmingly at the authentic \(n=2^m\); \(n\ge4\) is enough for
\(R^2>\frac12\,4^{n-1}\). The final comparison follows from
\(b_N\ge2^R-1\) and monotonicity of \(2^{r-1}/r^2\) for \(r\ge3\),
with \(2^{62}>15{,}000\cdot63^2\).

The exact cost split still has no omitted root-side term:
\(C_{\rm root}=\texttt{rootToSecondQ4Cost}
+\texttt{rootSecondQ4TailPrefixCost}\),
\(D_{\rm root}=\operatorname{drainCost}(R,0)\), and
\(D_N=C_{\rm dispatch}+\operatorname{terminalMoves}(W,E)+7\).
The \(+7\) is post-root and belongs to \(D_N\).

I also checked the current remainder algebra:
- the coefficient sum is
  \(\sum_{j=0}^{N-2}(12(N-j)-9)=6N^2-3N-3\);
- using \(b_{j+1}\le\ell\), \(R\le\ell\), and the root bound gives
  \[
  \Delta<(6N+15)\ell^2+(6N^2+66N+12)\ell
        +10N^2+85N+90;
  \]
- since \(b_{j+1}\ge2b_j\) for \(b_j\ge63\),
  \(\ell=b_{N-1}\ge2^{N-1}R\), hence
  \(N\le1+\log_2\ell\). With \(m=\log_2\ell\ge8\), the three
  polynomial terms are bounded by \(8(1+m)\ell^2\),
  \((1+m)\ell^2\), and \((1+m)\ell^2\), respectively.

Thus the stated
\[
0\le\Delta<10(1+\log_2\ell)\ell^2
\]
is valid. This review is algebraic and conditional on the existing
root-prefix and exact dispatcher identities; it is not a Lean
acceptance of the authentic source composition.
