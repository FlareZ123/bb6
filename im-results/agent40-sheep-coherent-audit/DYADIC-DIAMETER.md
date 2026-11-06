# Exact generic dyadic diameter of the Sheep first-even quotient

**Agent 40, 6 November 2026.** Mathematical theorem, extending the previously finite diameter observation in [DIAMETER-FINITE.md](DIAMETER-FINITE.md). For every integer (p\ge1), the directed diameter of the **synthetic generic** Sheep even-return graph (G_p) modulo (2^p) is exactly

[
\boxed{\operatorname{diam}(G_p)=\lfloor p/2\rfloor.}
]

This is an all-parameter written proof composed from Agent 22's previously established inverse-word bijection and genuine-edge realization, plus Agent 40's previously established exact shortest-to-zero theorem, with a new short **saturation lemma**. An independent Lean 4.36.0-rc2 kernel certificate proves the saturation property in its abstract affine-gate form; the entire machine-source diameter theorem has **not** been kernel checked end-to-end. This is a structural result about synthetic residue paths. It proves no reachability statement for the fixed blank-origin integer 10 and makes no BB(6) bound or holdout decision.

## Definitions and established prerequisites

The original machine and its reduction are described by [Agent 16's pinned source bridge](../agent16-sheep-even-return/README.md), CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). (G_p), defined precisely in [Agent 22's dyadic theorem](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md), has one vertex for each even residue modulo (M=2^p). An edge (r\to s) means **there exists** a legal positive generic first-even Sheep section return with those source/target residues; different edges are allowed different integer witnesses. This is deliberately weaker than an orbit from one prescribed starting integer.

For (1\le a<p), (0\le h<p-a), put (c=a+h+1), (D_a=1+2^{a+1}). Agent 22's complete genuine generic inverse edge family is

[
T_{p,a,h}(s)\equiv
2^aD_a^{-1}\bigl(3-2a+2^{h+1}3^{-h}(s-1)\bigr)\pmod {2^p}.
	ag{1}
]

All inverses of odd integers exist modulo powers of two. Every even (s) gives a real (freely chosen) integer witness for (T_{p,a,h}(s)\to s).

Agent 22's all-(p) canonical-code theorem establishes: every even residue (r) has a unique word (W=((a_1,h_1),\ldots,(a_j,h_j))) with **total cost** (C(W)=\sum_i(a_i+h_i+1)\le p), such that

[
r=\Phi_p(W;0):=
T_{p,a_1,h_1}\bigl(\cdots T_{p,a_j,h_j}(0)\cdots\bigr).
]

Its length (\lambda_p(r)=j\) is at most (k=\lfloor p/2\rfloor), since each letter costs at least 2. The already proved [shortest-to-zero theorem](DYADIC-DISTANCE.md) states (d_{G_p}(r,0)=\lambda_p(r)), and that the maximum (\lambda_p\) equals (k). Finally, the explicit generic zero hub has an edge (0\to s) for **every** even (s).

## New universal saturation lemma

**Lemma.** For any admissible word (W) and any two even residues (s,t), if (C(W)\ge p-1), then

[
\Phi_p(W;s)=\Phi_p(W;t)\pmod {2^p}.
	ag{2}
]

**Proof.** Rewrite (1) as (T_{p,a,h}(s)\equiv b_{a,h}+2^c u_{a,h}s\pmod {2^p}), for a constant (b_{a,h}) and an odd unit (u_{a,h}=D_a^{-1}3^{-h}). Every letter therefore multiplies a change in its target residue by (2^c) times an odd unit. Composing the letters gives the exact modular affine difference identity

[
\Phi_p(W;s)-\Phi_p(W;t)
\equiv 2^{C(W)}U_W(s-t)\pmod {2^p},
\quad U_W\text{ odd}.
	ag{3}
]

Both targets are even, hence (2\mid(s-t)). If (C(W)\ge p-1), the right side is divisible by (2^p), proving (2). This argument includes (C(W)\ge p), where all target information is already lost. QED.

The independently compiled [AffineSaturation.lean](AffineSaturation.lean) proves the corresponding exact affine-composition shift and all-even-target modular saturation for arbitrary natural gate coefficients and any (p\le C+1). This captures the arithmetic core of the lemma without assuming an original-machine Lean import; applying it to (1) uses the displayed elementary modular rewriting. The Lean axiom audit reports only `[propext]` and no `sorryAx`.

## Exact diameter theorem

Set (k=\lfloor p/2\rfloor), and take arbitrary even source (r) and even target (s).

* If (\lambda_p(r)\le k-1), follow the canonical (\lambda_p(r))-edge route (r\to0) and then the genuine generic hub edge (0\to s). Its length is at most (k).
* If (\lambda_p(r)=k), its canonical word (W) has (k) letters. Therefore (C(W)\ge2k\ge p-1). By the lemma, (\Phi_p(W;s)=\Phi_p(W;0)=r). Starting from (s) and applying the letters of (W) in reverse order gives (k) legitimate inverse generic edges, which read forwards as a **(k)-edge synthetic path** (r\to s). Here every intermediate residue is even and each inverse edge is witnessed by the established CRT realization.

Consequently (d_{G_p}(r,s)\le k) for all pairs. If (p=1), there is only the zero vertex and the same assertion gives diameter zero. For the opposite inequality, the proven shortest-to-zero code-length theorem supplies an (r) with (d_{G_p}(r,0)=k). Thus (\operatorname{diam}(G_p)=k). QED.

**Additional useful corollary.** Every residue whose canonical word has cost at least (p-1) can reach *every* even target in at most its code length, by retaining precisely the same inverse-word letters and replacing terminal zero with the chosen target. This sharpened statement is target-uniform in the synthetic graph only.

## Independent tests and scope

[diameter_certificate.py](diameter_certificate.py) independently reconstructs canonical words and the inverse map and checks **every even target for every maximum-length source** for (1\le p\le15). In particular the p=15 case includes 15 maximal-length sources and 16,384 targets. This is a finite arithmetic regression of the general saturation argument, distinct from its proof. The older [all-pairs BFS census](DIAMETER-FINITE.md) establishes the diameters for (p\le11) by an independent exact graph method.

**Scientific status.** Equation (1), word uniqueness/exhaustiveness, edge-realizability, zero hub, and shortest-to-zero theorem are cited mathematical prerequisites; the new proof is conditional on their correctness, with the Lean kernel covering the affine saturation sublemma only. The comprehensive original-machine source bridge applies to the return semantics, but the claim here concerns the freely witnessed generic quotient, never the true blank-root trajectory. Prior-art novelty outside this repository has not been established. Keep this under `im-results/`, not `results/`. For BB(6), the decisive remaining question is whether the genuine even orbit from 10 reaches any power of two.
