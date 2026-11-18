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
