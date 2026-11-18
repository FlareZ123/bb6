# High-depth restart arithmetic (Agent 9)

**Current result.** The exact restart-energy identity
\[
I_0=14k-42c-50=2(7(k-3c)-25)
\]
gives \(I_0\equiv6\pmod7\). If \(s\) depth-two edges follow and \(I_0=8^sI_s\), the six-bit scaling slack \(\delta=3s-n>0\) reduces to the finite \(I_s\) list in [SIX-BIT-SLACK-MOD7.md](./SIX-BIT-SLACK-MOD7.md). This is conditional on the existing positive restart-energy bound \(0<I_0<98P\).

The exact first-shallow profiles and a Lean-checked low-suffix argument further remove:
- all odd \(I_s\) candidates, since neither shallow depth can start;
- \(I_s=6,34\), since the only possible first shallow step produces odd energy;
- \(I_s=20\) whenever \(T_1\) is even, since at most one further depth-zero step can follow and it produces odd energy.

The scalar proof is in [Mod7SlackLeaf.lean](./Mod7SlackLeaf.lean). It models arbitrary finite suffixes of depths \(0,1,2\), uses the exact affine wall energy, and compiles with Lean 4.36.0-rc2. Its axiom lists are [propext, Quot.sound]; it has no original-source imports and is not itself a CountCone theorem.

For the **cost-one terminal suffix** and \(P\ge2^{83}\), the remaining cases are:
1. \((\delta,I_s,t)=(2,20,5)\), with odd \(T_1\) and first shallow depth \(0\);
2. \((\delta,I_s)=(1,48)\), with \(t\ge8\); the first shallow depth is \(0\) for even \(T_1\), \(1\) for odd \(T_1\).

The cost-two terminal branch still needs its own \(t\)-interval. Both residual families remain conditional on the restart/source hypotheses; neither is excluded, and BB(6) remains unresolved. See the detailed derivation, exact hypotheses, and next source-model target in [SIX-BIT-SLACK-MOD7.md](./SIX-BIT-SLACK-MOD7.md).
