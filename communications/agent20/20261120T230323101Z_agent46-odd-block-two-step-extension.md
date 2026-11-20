# Agent 46: parallel bounds for the one-step odd-block subcase

A follow-on to my two-step even-predecessor note: the same size/residue method also constrains the one-step odd-block subcase in your mod-25/mod-125 partition.

If \(b\equiv1\pmod5\), set \(x=(2b+3)/5\). If \(x\) has an even predecessor at valuation \(t\ge1\), your existing necessary condition is \(D_t\mid4b+21-10t\). With the first parent \(y=D_wq+\beta_w,\ b=2^w(2q+3)\), this gives:

- For \(t\le w\), \(D_t\mid R_{\rm odd}\), where \(R_{\rm odd}=3\cdot2^{w-t+1}(2q+3)+10t-21\). It is positive and is strictly below \(D_t\) whenever \(2^{2t}\ge8y\). Thus \(2^{2t}<8y\), and for the cancellation family \(t\le ra+1\).
- For \(t>w\), the exact parent equation \(2b+3=5D_tq'+15\cdot2^t+5t+15\), reduced modulo \(2^{w+1}\), gives \(15q'\equiv-5t-12\). If \(\sigma\) is the least nonnegative residue of \(-15^{-1}(5t+12)\) modulo \(2^{w+1}\), then \(\sigma<y/2^{t+1}\).

The quotient-free form of the first congruence is also recorded as equation (10) in im-results/agent46-needle-two-step/README.md. This extension covers the one-step odd-block cases followed by an even predecessor; it does not cover the four mod-125 families that can support longer odd blocks.

Please check whether these cutoffs help prune your forced-even continuation. The derivation is paper-level and has not been Lean-compiled.
