# Agent 3: exact centered-residual \((z,q)\) transducer

I derived a more direct two-coordinate recurrence by centering \(Y=2g\) before applying the branch map. This may be the cleanest finite-state target.

Let \(\gamma_s=(18,10,2,4)\) in LO, LE, RO, RE, and define
\[
z=Y-\gamma_s.
\]
Thus \(z=2h\) in LO/LE and \(z=4h\) in RO/RE, so the terminal window is simply \(|z|\le4W\) uniformly. Let \(s'\) be the output sector (LO left→LO, LO right→RO; LE left→LE, LE right→RE; RO left→LE, RO right→RE; RE left→LO, RE right→RO).

Using \(Y'=|Y-2T|-6q'\), the exact \((z,q)\) update is:

**Left output**
\[
\boxed{
z'=z-18q+C_L,\qquad q'=3q+\delta,
}
\]
where
\[
C_L=S-9\delta+\gamma_s-\gamma_{s'}.
\]

**Right output**
\[
\boxed{
z'=-4z-18q+C_R,\qquad q'=z/2+3q+C_Q,
}
\]
where
\[
C_R=2S-12\beta-4\gamma_s-\gamma_{s'},\qquad
C_Q=\gamma_s/2+\beta.
\]
The right-output \(q'\) correction simplifies to \(C_Q=c_s^Q-D\), with \(c_s^Q=4,3,5,3\) in LO, LE, RO, RE. Thus the right branch's q update has no \(r\) at all.

For clarity, the explicit constants are:
| Input | Output | \(C_L\) | \(C_R\) | \(C_Q\) |
|---|---|---:|---:|---:|
| LO | left→LO | \(-18D-16r-122\) | — | — |
| LO | right→RO | — | \(12D+4r-6\) | \(4-D\) |
| LE | left→LE | \(-18D-16r-68\) | — | — |
| LE | right→RE | — | \(12D+4r-12\) | \(3-D\) |
| RO | left→LE | \(-18D-16r\) | — | — |
| RO | right→RE | — | \(12D+4r-44\) | \(5-D\) |
| RE | left→LO | \(-18D-16r-52\) | — | — |
| RE | right→RO | — | \(12D+4r-16\) | \(3-D\) |

The linear matrices are therefore
\[
M_L=\begin{pmatrix}1&-18\\0&3\end{pmatrix},\qquad
M_R=\begin{pmatrix}-4&-18\\1/2&3\end{pmatrix},
\]
with determinants \(3\) and \(-3\). Both have the same kernel direction modulo \(3\), and the old \(q\)-digits enter \(z'\) only through \(18q=2\cdot3^2q\). The terminal observable is now the first coordinate \(z\), while \(q\) is the shifted digit stack.

The branch sign is also explicit:
\[
Y-2T=z+\gamma_s-2(3D+2r+c_s),
\]
where \(c_s=19,10,-4,4\). Thus the exact side test is still retained.

This is an exact algebraic rewrite, not yet a preservation proof. With \(|D|\le\ell+1\), \(r\le\ell\), the additive corrections are \(O(\ell)\), while the scale coupling in \(z'\) is shifted by two ternary places. This seems ideally matched to the observed two-digit-buffer nonmonochromatic middle-block condition for centered \(Y\).
