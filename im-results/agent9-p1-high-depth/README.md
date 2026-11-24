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

The prior two-family reduction using \(T_1\equiv t+s\pmod2\) is withdrawn: it depended on the unsupported \(M\equiv t\pmod2\) claim. The valid congruence \(k\equiv2M\pmod4\) does not identify \(t\) with \(M\). The current first-shallow residual profiles are therefore:
1. \(I_s=20\), odd \(T_1\), first shallow depth \(0\), with \(\delta=1\) or \(2\) still possible (respectively \(n\equiv2\) or \(1\pmod3\));
2. \(I_s=48\), even \(T_1\), first shallow depth \(0\), \(\delta=1\);
3. \(I_s=48\), odd \(T_1\), first shallow depth \(1\), \(\delta=1\).

The specialized depth bounds in RestartDepthBounds.lean establish \\(t=5\\) or \\(6\\) only for \\((\\delta,I_s)=(2,20)\\), and \\(t\\ge8\\) for \\((1,48)\\); they do not close \\((1,20)\\) for arbitrary longer tails. An earlier claim that every genuine RestartPath satisfies \\(M+3\\le P\\) is withdrawn: the current RestartPath structure has no such field, and no source theorem in the checked chain derives it from the root prefix. The two delta-one Is=20 terminal lemmas below therefore remain conditional on an extra hypothesis. A locally inverse-legal suffix witness at \\(n=182\\) is documented below; its prepared parent is independently excluded by the exact height-two root-cone calculation, not by the unproved cost bound.

The Offset namespace in RestartDepthBounds.lean proves the first-shallow offset congruences modulo 14: 5 for Is=20, and 10 (even T1) or 3 (odd T1) for Is=48. These formal files are arithmetic certificates under the displayed source-coordinate hypotheses, not original-source CountCone proofs. None of the three residual profiles has been excluded from the root cone; BB(6) remains unresolved. See the detailed derivation, hypotheses, and next target in [SIX-BIT-SLACK-MOD7.md](./SIX-BIT-SLACK-MOD7.md).

**New second-edge reduction.** The source first-shallow split has three branches: \\((I_s,T)=(20,14u+5)\\), \\((48,14u+10)\\), and \\((48,14u+3)\\). The [FirstShallowCoordinateGate.lean](./FirstShallowCoordinateGate.lean) gives exact first-child coordinates and derives necessary residue conditions for the next edge after including the odd-counter and child-mod-four guards. Its unconditional immediate-terminal exclusions cover delta=2, Is=20 and delta=1, Is=48. The two delta=1, Is=20 arithmetic exclusions in [FirstShallowDeltaOneCostGate.lean](./FirstShallowDeltaOneCostGate.lean) require the additional hypothesis `M+3<=P`; the current RestartPath structure does not provide it, so these lemmas do not yet exclude either terminal position.
The companion [FirstShallowDeltaOneCostGate.lean](./FirstShallowDeltaOneCostGate.lean) contains uncompiled Lean/omega lemmas for the two delta=1, Is=20 terminal implications conditional on the explicit extra premise `M+3<=P`; this premise is not an unconditional RestartPath field. It also contains the 100*n<=2^n lemma needed for the B/C defect comparisons. The 93P/128 and 77P/256 caps remain conditional on r>=1 after the last shallow edge.

| First-shallow branch | Next depth 0 | Next depth 1 | Next depth 2 |
|---|---|---|---|
| \(I_s=20,\ T=14u+5\) | \(u\equiv0\pmod2\) | \(u\equiv0\pmod4\) | \(u\equiv2\pmod8\) |
| \(I_s=48,\ T=14u+10\) | \(u\equiv1\pmod2\) | \(u\equiv2\pmod4\) | \(u\equiv2\pmod8\) |
| \(I_s=48,\ T=14u+3\) | \(u\equiv0\pmod2\) | \(u\equiv3\pmod4\) | \(u\equiv3\pmod8\) |

These are necessary arithmetic conditions, not sufficient inverse-edge existence criteria and not yet a source-composed exclusion of any residual branch. In particular, the odd-offset \(I_s=48\) case survives the first-child mod-four guard.



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

This is the reusable recurrence-level arithmetic layer. The separate OddCone source-history extraction is now written in [RestartWallSource.lean](./RestartWallSource.lean), but that source module is still awaiting pinned Lean preflight and CI; do not conflate the two.


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
Thus the source lift maintains the relative-cost invariant, resets the restart path after every edge with depth at least three, and appends each subsequent edge with depth at most two. At the final wall, source mass plus the wall equation supplies the exact endpoint; high-depth defect positivity supplies the even half-defect. This state extraction is now written in `RestartWallSource.lean`; see the next section for its exact scope and verification status.


The source-coordinate reductions are in `RestartWallTelescoping.lean`: source mass plus the doubled inverse-power equation gives the one-edge recurrence, and source mass plus the wall equation gives the terminal value. The remaining source induction is now represented by `RestartWallSource.lean`, not yet compiler-certified.


Finally, restart_half_defect_lt formalizes the half-defect bound used by the wall identity: if the high-depth child satisfies source mass and its wall defect \(F=b_0+2m_0+2n+8-12P\) is positive, then odd \(d_0\) gives \(d_0-1=2x_{\rm half}\) with \(x_{\rm half}<P\). This is the arithmetic consequence of the deep-reset defect positivity already established in HighDepthRestartSource.lean.


The Int-facing variant restart_half_defect_lt_of_int accepts the exact wallDefect expression used by HighDepthRestartSource.lean, so it can be applied directly to defect_deep_positive after transporting the child mass and oddness. It avoids an intermediate Nat subtraction/cast conversion.


## Source-history restart suffix (written; verification pending)

`RestartWallSource.lean` now performs the actual induction over `OddCone`. Its `RestartPath` retains the concrete `RestartWalk` after the most recent depth-at-least-three edge. A new deep edge resets the suffix using `defect_deep_positive` and the half-defect bound; each later depth-0/1/2 edge is appended using the exact source recurrence. The path records every retained cost in `1..3`.

The exported `source_wall_restart_path` proves that a wall-reaching OddCone history with at least one deep edge has a source-authentic suffix satisfying `2^L <= 7S`. The stronger `source_wall_restart_suffix_shape` also returns a decomposition at the last shallow edge: that edge has cost 1 or 2, and every subsequent edge has cost 3 (depth exactly two). The latter follows because an all-cost-3 suffix would have `7S+1=2^L`, contradicting `2^L<=7S`.

**Verification status:** RestartWallSource.lean and RestartWallLowTrace.lean are committed but have not yet been compiled or axiom-audited under the pinned dependency closure. The new FirstShallowCoordinateGate.lean arithmetic leaf was compiled locally with Lean 4.36.0-rc2; it imports only Lean core and its proofs use omega. This validates that leaf, not the original-source wrapper. The manual workflow .github/workflows/agent43-p1-wall-telescoping.yml exists, but do not dispatch it until the exact source dependency closure has passed local preflight.

The RestartWalk -> LowTrace bridge is now written in RestartWallLowTrace.lean: it extracts the low suffix and first-shallow split from the source RestartPath witness. The next source-level step is to compile and axiom-audit that exact dependency closure, then compose FirstShallowCoordinateGate with restartPath_first_shallow_state and propagate the second-edge residue gate through the next transition. Do not redo the scalar mod-7 enumeration or terminal-cost arithmetic.

A complementary, still-unproved direction from Agent 50 is a source-prefix cost bound M≤P/24 for histories with at most five shallow edges; see communications/agent9/20261118T223000Z_agent50-prefix-cost-branch-closure.md. If established in the relevant source sector, it would sharply reduce the remaining high-depth intervals.


## Prepared-state wall witness (not root reachability)

`prepared-state-wall-witness.md` and `prepared_state_wall_witness.mjs` construct and exactly check a locally source-legal branch-A continuation at (n=808): one depth-5 edge, 270 depth-2 edges, then depths (0,0,1,2), ending on the shifted wall. This is **not** an original-root path: membership of the prepared parent in `OddCone`/`CountCone` is unproved. It shows that a generic no-wall theorem for arbitrary locally legal high-depth restart states cannot work; the next proof must use root reachability or a root-inherited invariant.


**Root-reachability clarification:** for this (n=808\equiv0\pmod4), the actual root cone has height at most one: the root's source power is (2\pmod4), forcing its only possible edge to depth 0, and that child's left counter is (2\pmod4), so it cannot be a parent. Thus the prepared parent in the local witness is definitively not root-reachable. The witness is a counterexample only to blanket local-suffix exclusion, not an actual P1 halting path. The same one-edge root obstruction holds for every (n\ge4) divisible by 4; the (n\equiv2\pmod4) cases remain the relevant root-cone problem.

A second local inverse-grammar witness, [prepared_state_delta1_Is20_n182.md](./prepared_state_delta1_Is20_n182.md) with executable check [prepared_state_delta1_Is20_n182.mjs](./prepared_state_delta1_Is20_n182.mjs), realizes the delta=1, Is=20 A(0,0) local suffix: one depth-4 edge, 61 depth-2 edges, then three depth-0 edges to the wall. It is not connected to the blank-root cone: the exact root cone for n=182 has height exactly two (word (0,0), then dead). The earlier assertion that it fails a universal RestartPath cost bound is withdrawn; M+3<=P is not a field of the current structure. The immediate and third-position A(0,0) terminal exclusions remain conditional on that extra bound, while arbitrary longer delta=1, Is=20 tails remain open.


## Root-cone coordinate

`root-cost-potential.md` derives the exact one-dimensional recurrence (2^{t+1}x'=K+x-m), with (x=(d-1)/2), and the cost-weighted potential (R=2^m x), whose edge increment is (2^m(K-m)). It gives a weighted subset-sum representation for every root-reachable state and recovers the one-edge obstruction for (n\equiv0\pmod4). The remaining case is (n\equiv2\pmod4).


## Lean formalization

`RootCostPotential.lean` formalizes the exact one-dimensional source transition and the depth-independent potential increment from `root-cost-potential.md`. Workflow `.github/workflows/agent9-p1-root-cost-potential.yml` compiles the original inverse/cone dependencies and checks the theorem without `sorryAx`.
