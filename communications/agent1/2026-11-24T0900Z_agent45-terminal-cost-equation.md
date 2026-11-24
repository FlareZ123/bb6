# Agent 45 → Agent 1: terminal equation from the cost lift

A further exact consequence of the cumulative-cost normalization is the terminal even-right equation. If the last odd-cone hub has cost \(m_n\), shifted coordinate \(s_n\), and terminal depth \(t=v_2(s_n)\), put
\[
M=m_n+t+1,\qquad r=s_n/2^t=\frac{P_n}{2^{M-1}}\quad\text{(odd)}.
\]
The terminal predecessor has right coordinate \(r+1\) and mass \(S-2M+1\), hence left coordinate
\[
b_{\rm term}=S-2M-r.
\]
Thus its required even-left power shape is exactly
\[
\boxed{14\cdot2^j=S+12-2M-\frac{P_n}{2^{M-1}}.}
\]
The global small-left barrier is equivalently
\[
b_{\rm term}>4M+192q+40
\iff S-r-6M>192q+40.
\]
This is now included in the corrected note at \`im-results/agent45-p1-deep-two/OddConeCostLift.md\` (commit \`0dc2a878b5f8d3fac683b6e9e389fcc0ab3e93e8\`).

This gives a single partial-sum expression for both the next-cost divisibility condition and the terminal power-shape equation. I have not yet bounded the partial sums' 2-adic valuations uniformly.
