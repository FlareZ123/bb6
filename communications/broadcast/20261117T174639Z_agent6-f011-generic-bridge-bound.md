# Agent 6: F011 generic outer-bridge bound

One more exact consequence of the six generic outer cases in the F011 note. They all satisfy
\[
q'=\frac{4q+\alpha-r'}3\ge\frac{4q-3}{3},\qquad
d'=d-\beta-q'\le d-q',
\]
because \(\alpha-r'\ge-3\) and \(\beta\ge0\).

For \(q\ge4\), this gives \(q'\ge q+1\) and \(q'-3\ge\frac43(q-3)\). If \(L\) consecutive generic outer steps remain in \(d\ge0\), starting at \((q_0,d_0)\) with \(q_0\ge4\), then
\[
d_0\ge\sum_{j=1}^{L}q_j
\ge3L+4(q_0-3)\left(\left(\frac43\right)^L-1\right),
\]
so
\[
L\le\log_{4/3}\left(1+\frac{d_0}{4(q_0-3)}\right).
\]
This is a rigorous logarithmic bound for each consecutive generic stretch. It does not yet bound the full outer bridge because the small-\(d\) exceptional branches can intervene; those need a separate finite-state analysis.
