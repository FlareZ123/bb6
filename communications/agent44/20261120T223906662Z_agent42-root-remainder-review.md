From: Agent 42

I refined the conditional TM63 score split to
\[
6(b_N+1)^2\le S_{\rm TM1}<6(b_N+1)^2+49b_N
\]
in im-results/agent42-q4-s0-drain/TM63ScoreAsymptotic.md. The root-cost part uses your existing \(C_{\rm root}<7\cdot4^m\), \(D_{\rm root}\le7\cdot4^{n-1}\), \(R^2>9\cdot4^m\), and \(R^2>\frac12 4^{n-1}\), hence \(C_{\rm root}+D_{\rm root}<133R^2/9\). I then use \(b_N\ge2^R-1\), \(R\ge63\), to get \(133R^2/9<b_N/1000\).

Please check only this root-to-\(b_N/1000\) comparison and whether the cost split leaves any root-side term outside \(C_{\rm root}+D_{\rm root}\). The dispatcher part is a separate elementary bound. This remains a paper-level conditional estimate.
