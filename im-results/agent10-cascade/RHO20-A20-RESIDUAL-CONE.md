# Exact reverse-parent cone for the first rho-20 residual example

**Status:** exact arbitrary-precision integer computation for one fixed candidate only. This is intermediate evidence, not a family theorem and not a Lean-certified result.

For \(a=20\), the selected rho-20 candidate has
\[
\gamma=103,\quad K=97\cdot2^{13}+48=794672,\quad r=K+4-a=794656.
\]
The target \(E\) is the corresponding \(t=0,q=0\) fatal-source height.

The standalone reproducer rho20_residual_a20_reverse_cone.py enumerates the complete inverse-parent graph using both source-exact ResetParent arms:
- the unique possible even dyadic level is determined by the child's bit length and checked against \([6\cdot2^k-1,8\cdot2^k-3]\);
- every odd exponent \(0\le t<v_3(2u+5)\) is enumerated, with quotient parity and the exact odd-source band \([6\cdot2^k+1,8\cdot2^k-1]\) checked;
- no maximal-exponent-only shortcut and no \(3\nmid d\) restriction is used.

The exact graph has **35 states, 34 edges, 8 leaves, maximum depth 14, and 5 branching nodes**. It is a tree with no merges, and no state or parent is the blank root \(2\). The branching nodes occur at depths \(2,4,6,8,10\); odd side branches use \(t=1\) and \(t=3\).

This candidate belongs to the still-open class \(a\equiv2\pmod{18}\), where \(v_3(X)=2\) but \(v_3(X_1)\ge2\). The unique-chain theorem does not apply: the higher-valuation parent fan must be closed branch by branch. The fixed \(a=20\) census is a useful lead for that symbolic problem, but it does not prove the corresponding family or any general rho-20 exclusion.
