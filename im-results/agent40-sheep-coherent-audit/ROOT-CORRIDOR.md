# Authentic Sheep blank-orbit conditional: exact forced corridor and halting-free return delay

**Agent 40, 6 November 2026. Intermediate conditional statement; Sheep remains undecided.** The fixed blank-origin Sheep even-section trajectory starts at \(t_0=10\) and follows actual legal first-even returns whenever it remains nonterminal. The earlier original-machine Lean bridge (Agent 16, CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547)) establishes this reduction and monotone increase of even return states. Thus every reached even-section state satisfies \(t\ge10\).

The structural quotient results in [MIXED-EXACT-DIAMETER.md](MIXED-EXACT-DIAMETER.md) are freely witnessed synthetic statements. This note records a **genuinely fixed-blank-orbit-applicable conditional law** extracted from their proof.

## Exact law

Let \(t\ge10\) be any **genuinely reached, nonterminal** even section integer on the authentic Sheep blank orbit. If
\[
b=v_2(t+2)\ge3,
\]
then, putting \(k=\lfloor b/2\rfloor\), the next \(\lfloor(b-1)/2\rfloor\) even-section first-return blocks are **forced to take the exact normal branch \(a=1,h=0\)**. For each index
\[
0\le i\le \lfloor(b-1)/2\rfloor
\]
the literal consecutive integer orbit satisfies
\[
\boxed{\quad t_i+2=\frac{5^i}{4^i}(t+2),\qquad
v_2(t_i+2)=b-2i.\quad}
\tag{1}
\]
Here \(t_0=t\). All divisions are exact in the integers. This is a statement about the **actual single trajectory**, and its preconditions do not assert that the blank orbit ever visits a particular chosen \(t\) or value of \(b\).

**Proof.** When \(8\mid t_i+2\), write \(t_i=8w+6\). Because the actual even orbit starts at \(10\) and increases strictly, \(t_i\ge10\), which forces \(w\ge1\); the exceptional odd-part-three source \(t_i=6\) is impossible. Consequently \(t_i=2(4w+3)\) lies in the generic branch, and its first section return is
\[
F(t_i)=10w+8=\frac{5t_i+2}{4},
\]
which is already even. Hence \(E(t_i)=F(t_i)\) and
\[
4(t_{i+1}+2)=5(t_i+2).
\]
The factor \(5\) is odd; thus this equality reduces the exact 2-adic valuation of \(t_i+2\) by precisely two. Iterate while the current valuation is at least three. The stated stopping count and formula (1) follow by induction. The source-compatible arbitrary-precision one-step identity is separately Lean-checked in [SheepCorridor.lean](SheepCorridor.lean), theorems \`forced_unbounded_drop\` and \`forced_from_residue_eight\`; the all-time machine-source induction (including the genuine \(10\) seed) is a **written mathematical composition**, not yet a single imported source-level Lean theorem.

## Conditional halting delay

A Sheep halting section target in the even graph is a power \(t_i=2^j\) with \(j\ge2\). For every such power,
\[
v_2(2^j+2)=1.
\]
The forced corridor has \(v_2(t_i+2)=b-2i\), which remains greater than one for all \(i<\lfloor b/2\rfloor\). Therefore, **conditionally upon reaching any even state \(t\) with \(b=v_2(t+2)\ge3\), the genuine machine cannot encounter a halting power in fewer than \(\lfloor b/2\rfloor\) subsequent first-even returns**.

When \(b\) is even, the last known state at \(i=b/2-1\) has valuation two and cannot be a power \(2^j\) with \(j\ge2\); when \(b\) is odd, the first index whose valuation may become one is \(i=(b-1)/2\). The delay bound refers to **macro even-section returns**, not primitive Turing-machine steps, and does not give an upper bound on whether a halt ever occurs.

**Literal blank-prefix checks:** The independently computed genuine even orbit has \(334\to418\) with \(v_2(334+2)=4\) and \(v_2(418+2)=2\); likewise \(20414\to25518\to31898\) with valuations \(6\to4\to2\). Exact identities (1) hold in both examples. They are illustrative checks, not a proof of unbounded reachability.

## Research significance and limitations

This is a local, **blank-orbit valid**, history-compatible rule for valuation bursts; it differs in scope from synthetic quotient mixing results, because it follows actual successive returns from the authentic machine's current state. It may help design history-sensitive invariants and lower bounds on distances between potential halting gates. It does **not** establish that any required valuation burst occurs, preclude all future halting powers, settle the Sheep machine, or determine BB(6). Prior external novelty is unassessed, and the all-time source-importing Lean composition remains open.
