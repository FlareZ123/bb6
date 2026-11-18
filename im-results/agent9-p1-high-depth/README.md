# High-depth restart arithmetic (Agent 9)

**Current conditional result.** The exact restart-energy identity
\[
I_0=14k-42c-50=2(7(k-3c)-25)
\]
gives \(I_0\equiv6\pmod7\). If \(s\) depth-two edges follow and \(I_0=8^sI_s\), the six-bit scaling slack \(\delta=3s-n>0\) reduces to the finite \(I_s\) list in [SIX-BIT-SLACK-MOD7.md](./SIX-BIT-SLACK-MOD7.md). This uses the positive restart-energy bound \(0<I_0<98P\).

The exact first-shallow profiles and the Lean-checked low-suffix argument remove:
- all odd \(I_s\) candidates, since neither shallow depth can start;
- \(I_s=6,34\), since the only possible first shallow step produces odd energy;
- \(I_s=20\) whenever \(T_1\) is even, since at most one further depth-zero step can follow and it produces odd energy.

The scalar proof is in [Mod7SlackLeaf.lean](./Mod7SlackLeaf.lean). It models arbitrary finite suffixes of depths \(0,1,2\), uses the exact affine wall energy, and relies on the sign-dynamics lemma to ensure a shallow edge must eventually occur after the last high-depth reset. It has no original-source imports and is not itself a CountCone theorem.

The source-parent depth bounds for both terminal shallow costs are in [RestartDepthBounds.lean](./RestartDepthBounds.lean). They formalize the parent mass equation, the restart defect identity, the inverse-depth equation, and the terminal cost bounds. With \(P\ge2^{83}\), the cost-one bounds give \(t=5\) or \(6\) for \((\delta,I_s)=(2,20)\), and \(t\ge8\) for \((1,48)\). The cost-two bounds give \(t=5\) for \((2,20)\), and \(t\ge8\) for \((1,48)\).

Combining these with \(T_1\equiv t+s\pmod2\) leaves the same two families for either terminal cost. The Offset namespace in RestartDepthBounds.lean additionally proves the first-shallow offset congruences modulo 14: 5 for Is=20, and 10 (even T1) or 3 (odd T1) for Is=48:
1. \((\delta,I_s,t)=(2,20,5)\), with odd \(T_1\) and first shallow depth \(0\);
2. \((\delta,I_s)=(1,48)\), with \(t\ge8\); the first shallow depth is \(0\) for even \(T_1\), \(1\) for odd \(T_1\).

Both formal files are arithmetic certificates under the displayed source-coordinate hypotheses, not original-source CountCone proofs. Neither residual family has been excluded; BB(6) remains unresolved. See the detailed derivation, hypotheses, and next target in [SIX-BIT-SLACK-MOD7.md](./SIX-BIT-SLACK-MOD7.md).


## Arbitrary-restart telescoping (recurrence-level Lean proof)

RestartWallTelescoping.lean formalizes the arbitrary-start weighted telescoping identity for a low-depth suffix. A restart walk records each edge cost \(e_j\), relative accumulated cost \(s_j\), and the scalar source recurrence
\[
x_j+14P=2^{e_j}x_{j+1}+2(c+3+s_j),\qquad x_j=d_j-1.
\]
The Lean theorems also prove a one-edge aggregate update: from an invariant at cost L, appending a step of cost e updates (S,T,L) to (S+2^L,T+L*2^L,L+e) while preserving the invariant. A second theorem derives the additive wall identity directly from that aggregate invariant, so a future source induction need not construct an explicit edge list. The Lean theorem proves
\[
x_0+14P S=2^Lx_{\rm wall}+2((c+3)S+T),
\]
where \(S=\sum_j2^{s_j}\), \(T=\sum_js_j2^{s_j}\), and \(L=\sum_je_j\). Substituting the wall value and an even initial defect gives the additive wall identity; if \(x_0/2<P\), it also proves \(2^L\le7S\), i.e. the nonnegative restart product \(N=7S-2^L\).

This is a formal proof of the recurrence-level arithmetic, not yet a source-history extraction theorem: proving that the suffix after the last high-depth edge instantiates RestartWalk remains a separate source-level task. It is intended to close the formalization gap identified in Section 6 of SourceWallToCarryDP.md, without claiming that the original CountCone lift is complete.


### Exact source recurrence needed for the lift

The source-edge calculation in WallTelescopingSource.lean has the form
\[
d_{\rm parent}-1+14P
=2^{t+1}(d_{\rm child}-1)+2(m_{\rm parent}+n+3).
\]
For a restart child at absolute cost \(m_0\), set \(c=m_0+n\), and for a later parent set \(s=m_{\rm parent}-m_0\). Then this is exactly the RestartWalk step
\[
x+14P=2^e x'+2(c+3+s),\qquad e=t+1.
\]
Thus the source lift should maintain \(m_{\rm current}=m_0+L\), reset \(L=S=T=0\) after every edge with \(t\ge3\), and apply restart_aggregate_step to each subsequent edge with \(t\le2\). At the final wall, source mass plus the wall equation supplies \(x_{\rm wall}=2P+2L+2c+6\). The high-depth defect positivity in HighDepthRestartSource.lean should supply \(x_0=2x_{\rm half}\) with \(x_{\rm half}<P\). The remaining work is to formalize this state extraction/induction over OddCone; the arithmetic interface is now in place.


The same file now isolates the two source-coordinate reductions needed by that induction: source mass plus the doubled inverse-power equation gives the one-edge recurrence, and source mass plus the wall equation gives the terminal value \(d_{\rm wall}=2P+2m+2n+7\). These lemmas are elementary and kernel-checked; the remaining nontrivial step is carrying the restart aggregate through the actual OddCone path and resetting it at each high-depth edge.


Finally, restart_half_defect_lt formalizes the half-defect bound used by the wall identity: if the high-depth child satisfies source mass and its wall defect \(F=b_0+2m_0+2n+8-12P\) is positive, then odd \(d_0\) gives \(d_0-1=2x_{\rm half}\) with \(x_{\rm half}<P\). This is the arithmetic consequence of the deep-reset defect positivity already established in HighDepthRestartSource.lean.
