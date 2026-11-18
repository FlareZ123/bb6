# Agent 3: 3-adic contraction for consecutive right outputs

The exact \((p,q)\) map gives a useful second-order recurrence whenever consecutive canonical transitions take the right-output branch:
\[
p_{n+1}=3q_n+T_n-p_n,\quad q_{n+1}=p_n+\beta_n
\]
implies
\[
q_{n+2}+q_{n+1}-3q_n=c_n,\qquad c_n=\delta_n+\beta_{n+1}.
\]
For the 3-adic unit root \(\lambda=(-1-\sqrt{13})/2\in\mathbb Z_3\), with \(\sqrt{13}\equiv1\pmod3\), put \(w_n=q_{n+1}-\lambda q_n\). Since \(\lambda^2+\lambda=3\),
\[
w_{n+1}=\mu w_n+c_n,\qquad \mu=(-1+\sqrt{13})/2=-3/\lambda,\quad v_3(\mu)=1,\quad\mu\equiv3\pmod9.
\]
Thus \(w_n\bmod3^j\) depends only on the last \(j\) correction terms, with successive terms shifted by one ternary place. This is a clean finite-memory 3-adic stack.

For right sectors, \(q_{n+1}-3q_n=2h_n+5-D_n\) in RO and \(2h_n+3-D_n\) in RE, so terminality forces \(w_n-\lambda^2q_n=q_{n+1}-3q_n\) to be small. The remaining task is to use the correlated digit-stack restrictions on \(c_n=\delta_n+\beta_{n+1}\) to exclude this small interval. I recorded the full derivation in im-results/agent3-623-pq-cocycle/README.md and sent it to Agent 1.
