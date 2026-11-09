# P1: kernel-certified 78-class affine exclusion and late-start 79th candidate

**Original-source Lean certification completed for 78 new classes (9 November 2026).** [Run 42548567153](https://github.com/FlareZ123/bb6/actions/runs/42548567153) compiled the entire unchanged original P1 source chain and proved the aggregate theorem with standard axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. [Run 42550344965](https://github.com/FlareZ123/bb6/actions/runs/42550344965) independently compiled the finite disjointness/count proof against the unchanged prior 701-class source census, without any axioms. A proposed additional late-start 79th class is separately identified below, pending its own source workflow. All results address only one **necessary critical gateway** of the six-state P1 machine; they do not decide its complete blank-tape behavior or BB(6).

## Mathematical claim and scope

Define the critical P1 counter
`H(n)=14·2^n−2n−10`. For each `q` in the displayed 78-element list and every `r≥0`, the **original-source-verified** Lean theorem is

```lean
¬ BB6.Agent1.Reach 2
    (14*2^(16*(q+4096*r)+2)-2*(16*(q+4096*r)+2)-10)
```

where `Reach` is the repository's authentic accelerated blank-root source relation. The 78 residues are

```text
109, 165, 225, 253, 397, 409, 413, 433, 533, 629, 681, 737, 793, 821, 865, 877, 993, 1013, 1017, 1021, 1065, 1073, 1109, 1137, 1181, 1201, 1233, 1285, 1401, 1505, 1517, 1633, 1661, 1689, 1765, 1777, 1821, 1841, 1857, 1905, 1985, 2057, 2073, 2101, 2193, 2285, 2293, 2297, 2317, 2353, 2373, 2429, 2441, 2453, 2465, 2485, 2545, 2577, 2589, 2613, 2681, 2769, 2917, 3029, 3085, 3137, 3221, 3337, 3381, 3429, 3493, 3497, 3521, 3541, 3633, 3721, 3725, 3881
```

They are pairwise distinct modulo 4096 and also distinct modulo 1024. All 78 lie outside the earlier **701/1024** necessary-gateway census certified by Agent 13. The disjoint, source-verified extension increases the covered gateway residue count from `2804/4096` to **`2882/4096`**, approximately **70.36%** of critical exponents in this arithmetic progression, apart from previously documented finite low-index exceptions. This is a gateway density, not a percentage of six-state machines decided, a P1 halting probability, or any BB(6) upper bound.

## Exact construction

Reuses the original all-parameter graph checker `BB6.Agent13AdaptiveParam.check` and source theorem `critical_unreachable_of_affine_check` from [Agent13's adaptive-parametric dossier](../agent13-p1-adaptive-param/README.md), without new axioms or machine-model substitutions.

For each q and each feeder side `s∈{8,9}`, begin with `(m,a,b)=(0,cq+4,4096c)`, where `c=12` for s=8 and `c=10` for s=9. For every graph vertex `(m,a,b)`, set `k=v₂(a)+1` and enumerate each `0≤t<k` for which `2^t|a` and `16q+s+m+t+a/2^t` is odd. Add the exact successor

```text
(m+t+1,
 (16q+s+m+t+a/2^t−1)/2,
 8·4096+b/2^(t+1)).
```

The finite table is then checked by the *source's executable Lean Boolean checker*, which also enforces `m≤13`, `0<k≤12`, `2^k∤a` and `2^k|b` for every node. The largest individual graph has 42 vertices, and the 156 two-feeder graphs contain **3692 vertices** in total. All 78 verified q indices satisfy `q≥109`, hence the original source bridge's `q≥29` and `B+K+3≤15q` hypotheses at uniform `B=13,K=12`.

- [QNodesA.lean](QNodesA.lean) and [QNodesB.lean](QNodesB.lean): 156 explicit affine finite graphs, each paired with its `check 12 13 ... = true` reduction.
- [QFinal.lean](QFinal.lean): generic affine-root membership transport, 78 kernel-checked gateway exclusions, and the aggregate `newQ_unreachable` theorem.
- [QDensity.lean](QDensity.lean): three axiom-free Lean checks certifying 78 distinct residues modulo 1024, exactly 78 classes, and no overlap with Agent13's certified 701 classes.
- [Manual original-source verifier](../../.github/workflows/agent28-p1-affine4096-source.yml): reconstructs unmodified Agent1/9/13 dependencies, compiles the source checker, then compiles the generated nodes and final theorem in Lean 4.36.0-rc2. It rejects Lean errors and `sorryAx`.

The graph generator is a deterministic transcription of Agent 13's existing [generate_narrow.py](../agent13-p1-adaptive-param/generate_narrow.py), specializing `P=4096`. Independent finite evaluation checked every vertex's exact successor formula, precision invariant and cost bound before producing the Lean tables. The generator is discovery code; the Lean checker and unchanged original-source bridge are the mathematical trust boundary.

## Late-start residue q ≡ 5 (mod 4096): 79th class under audit

The earlier 78-class scan restricted q bases to 29..4095. A new exact finite pair appears at **q=4101=4096+5**, with 26 and 24 affine nodes, respectively, and the same uniform checker precision K=12, cost B=13, period P=4096. The authentic source theorem's q≥29 hypothesis applies to 4101, yielding a proposed exclusion for **every q=4101+4096r** (r≥0), leaving the small q=5 case outside this theorem. This cylinder is new modulo 4096 and outside the earlier 701/1024 census. Its source is [Q4101.lean](Q4101.lean), with aggregate source theorem `expandedQ_unreachable` and disjointness/checker file [QDensity79.lean](QDensity79.lean).

If the pending 79th-class source audit succeeds, the asymptotic gateway density increases further to **2883/4096 ≈ 70.39%** (ignoring the one finite q=5 exception). The complete 79-class candidate is not yet claimed as kernel-certified; unlike the 78-class result, its original-source CI is pending.

## What remains open

The new cylinders are a limited set of necessary-gateway exclusions. The complete P1 halting criterion also involves other critical indices and high-cost/exceptional inverse histories. The certificates cannot establish P1 nonhalting or an exact BB(6) value. Improvements should favor a root-connected invariant that covers **all** critical indices, rather than repeatedly adding isolated very sparse cylinder certificates.

**Original-source verification:** main 78-class [CI success 42548567153](https://github.com/FlareZ123/bb6/actions/runs/42548567153), confirmed by second [CI success 42550344965](https://github.com/FlareZ123/bb6/actions/runs/42550344965) checking the 701-class disjointness. The 79th-class proof and density update are submitted through the same manual workflow and remain pending source audit.
