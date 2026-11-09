# P1: 78 additional infinite parameter cylinders at modulus 4096

**Intermediate research, original-source certification under audit (9 November 2026).** This note presents a finite, exact affine-graph calculation and a source-importing Lean proof candidate. It addresses the **necessary critical gateway** of the six-state P1 machine, not its full blank-tape nonhalting decision or BB(6). Proof status must be read from the original-source CI report before treating the universal implication as kernel certified.

## Mathematical claim and scope

Define the critical P1 counter
`H(n)=14·2^n−2n−10`. For each `q` in the displayed 78-element list and every `r≥0`, the proposed original-source theorem is

```lean
¬ BB6.Agent1.Reach 2
    (14*2^(16*(q+4096*r)+2)-2*(16*(q+4096*r)+2)-10)
```

where `Reach` is the repository's authentic accelerated blank-root source relation. The 78 residues are

```text
109, 165, 225, 253, 397, 409, 413, 433, 533, 629, 681, 737, 793, 821, 865, 877, 993, 1013, 1017, 1021, 1065, 1073, 1109, 1137, 1181, 1201, 1233, 1285, 1401, 1505, 1517, 1633, 1661, 1689, 1765, 1777, 1821, 1841, 1857, 1905, 1985, 2057, 2073, 2101, 2193, 2285, 2293, 2297, 2317, 2353, 2373, 2429, 2441, 2453, 2465, 2485, 2545, 2577, 2589, 2613, 2681, 2769, 2917, 3029, 3085, 3137, 3221, 3337, 3381, 3429, 3493, 3497, 3521, 3541, 3633, 3721, 3725, 3881
```

They are pairwise distinct modulo 4096 and also distinct modulo 1024. All 78 lie outside the earlier **701/1024** necessary-gateway census certified by Agent 13. If the source-connected certificate succeeds, the resulting disjoint extension would increase the covered gateway residue count from `2804/4096` to **`2882/4096`**, i.e. approximately **70.36%** of critical exponents in this arithmetic progression, apart from the previously documented finitely many low-index exceptions. This is a gateway density, not a percentage of six-state machines decided, a P1 halting probability, or any BB(6) upper bound.

## Exact construction

Reuses the original all-parameter graph checker `BB6.Agent13AdaptiveParam.check` and source theorem `critical_unreachable_of_affine_check` from [Agent13's adaptive-parametric dossier](../agent13-p1-adaptive-param/README.md), without new axioms or machine-model substitutions.

For each q and each feeder side `s∈{8,9}`, begin with `(m,a,b)=(0,cq+4,4096c)`, where `c=12` for s=8 and `c=10` for s=9. For every graph vertex `(m,a,b)`, set `k=v₂(a)+1` and enumerate each `0≤t<k` for which `2^t|a` and `16q+s+m+t+a/2^t` is odd. Add the exact successor

```text
(m+t+1,
 (16q+s+m+t+a/2^t−1)/2,
 8·4096+b/2^(t+1)).
```

The finite table is then checked by the *source's executable Lean Boolean checker*, which also enforces `m≤13`, `0<k≤12`, `2^k∤a` and `2^k|b` for every node. The largest individual graph has 42 vertices, and the 156 two-feeder graphs contain **3692 vertices** in total. All q indices satisfy `q≥109`, hence the original source bridge's `q≥29` and `B+K+3≤15q` hypotheses at uniform `B=13,K=12`.

- [QNodesA.lean](QNodesA.lean) and [QNodesB.lean](QNodesB.lean): 156 explicit affine finite graphs, each paired with its `check 12 13 ... = true` reduction.
- [QFinal.lean](QFinal.lean): generic affine-root membership transport, 78 source gateway exclusions, and the aggregate `newQ_unreachable` theorem.
- [Manual original-source verifier](../../.github/workflows/agent28-p1-affine4096-source.yml): reconstructs unmodified Agent1/9/13 dependencies, compiles the source checker, then compiles the generated nodes and final theorem in Lean 4.36.0-rc2. It rejects Lean errors and `sorryAx`.

The graph generator is a deterministic transcription of Agent 13's existing [generate_narrow.py](../agent13-p1-adaptive-param/generate_narrow.py), specializing `P=4096`. Independent finite evaluation checked every vertex's exact successor formula, precision invariant and cost bound before producing the Lean tables. The generator is discovery code; the Lean checker and unchanged original-source bridge are the mathematical trust boundary.

## What remains open

The new cylinders are a thin additional set of necessary-gateway exclusions. There remain other P1 halting routes, high-cost/exceptional inverse histories, and unresolved six-state machines. Even after the certificates pass, they do not establish P1 nonhalting or any exact BB(6) value. Improvements should favor a root-connected invariant that covers **all** critical indices, rather than repeatedly adding isolated very sparse cylinder certificates.

**Original-source verification:** [manual run 42548567153](https://github.com/FlareZ123/bb6/actions/runs/42548567153), queued after the proof modules were pushed. Until its completion, the exact graph census and proposed endpoint theorem are candidate evidence only.
