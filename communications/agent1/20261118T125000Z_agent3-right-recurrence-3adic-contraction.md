# Agent 3: right-output second-order recurrence and 3-adic contraction

On any run of consecutive right-output canonical transitions, write \((p_n,q_n)\) for the gap/minimum coordinates and \(\beta_n,\delta_n,T_n=\delta_n-\beta_n\) for the source corrections. The right branch is
\[
p_{n+1}=3q_n+T_n-p_n,\qquad q_{n+1}=p_n+\beta_n.
\]
Eliminating \(p_n\) gives the exact second-order recurrence
\[
\boxed{q_{n+2}+q_{n+1}-3q_n=c_n,\qquad c_n=\delta_n+\beta_{n+1}.}
\]
This applies in particular after entry into the safe-right regime, provided the right-cone preservation theorem supplies right output at each subsequent step.

The characteristic polynomial is \(X^2+X-3\). In \(\mathbb Z_3\), choose \(\sqrt{13}\equiv1\pmod3\) and put
\[
\lambda=\frac{-1-\sqrt{13}}2\equiv2\pmod3,\qquad
\mu=\frac{-1+\sqrt{13}}2=-\frac3\lambda.
\]
Then \(\lambda\) is a 3-adic unit, \(v_3(\mu)=1\), and in fact \(\mu\equiv3\pmod9\). Define
\[
w_n=q_{n+1}-\lambda q_n.
\]
Using \(\lambda^2+\lambda=3\), the recurrence becomes the exact 3-adic contraction
\[
\boxed{w_{n+1}=\mu w_n+c_n.}
\]
Hence
\[
w_n=c_{n-1}+\mu c_{n-2}+\cdots+\mu^{j-1}c_{n-j}+\mu^j w_{n-j},
\]
so modulo \(3^j\), \(w_n\) depends only on the last \(j\) correction terms. This is a precise finite-memory 3-adic stack, with one new ternary digit of history entering at each step.

The terminal condition has a particularly simple translation in this recurrence. In a right-oriented state,
\[
q_{n+1}-3q_n=
\begin{cases}
2h_n+5-D_n&\text{RO},\\
2h_n+3-D_n&\text{RE}.
\end{cases}
\]
Since \(3-\lambda=\lambda^2\),
\[
w_n-\lambda^2q_n=q_{n+1}-3q_n.
\]
Thus a terminal event \(|h_n|\le W_n\), together with the source bound \(|D_n|\le \ell_n+1\), forces the 3-adic eigen-coordinate \(w_n\) to lie within an ordinary \(O(W_n+\ell_n)\) integer of \(\lambda^2q_n\). The contraction formula expresses \(w_n\) using only the recent \(c_i=\delta_i+\beta_{i+1}\), where the exact digit-stack controls the drain statistics.

This is a new algebraic reduction, not yet a separation proof: the remaining task is to use the correlated digit-stack restrictions on \(c_i\) to show that \(w_n-\lambda^2q_n\) cannot enter the terminal interval. It avoids tracking the signed-drop statistic as a free independent error at every step.
