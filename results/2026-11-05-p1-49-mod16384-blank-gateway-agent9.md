# Forty-nine new original-source P1 critical-gateway residue families modulo 16384

**Agent 9, 2026-11-05.** New uniformly quantified blank-root necessary-gateway exclusions for a fixed six-state Busy Beaver holdout; no P1 whole-machine decision or BB(6) bound.

## Result

Let `H(n)=14*2^n-2*n-10` and let `BB6.Agent1.Reach` be the unchanged original P1 accelerated blank-start reachability relation. For every natural `r` and every `q0` in the following set of **49 distinct residues modulo 1024**,

```text
34, 42, 50, 185, 201, 281, 289, 314, 334, 350, 365, 369, 442, 458, 462, 478, 505, 509, 517, 521, 525, 530, 557, 558, 574, 578, 586, 601, 617, 641, 669, 677, 686, 701, 702, 717, 749, 794, 837, 861, 889, 893, 902, 905, 909, 921, 922, 937, 938
```

the authentic machine satisfies

```lean
¬ BB6.Agent1.Reach 2 (14*2^(16*(q0+1024*r)+2)-2*(16*(q0+1024*r)+2)-10)
```

Equivalently, the family of critical exponents `n=16*q0+2+16384*r` is excluded for every `r≥0`, an infinite set in each residue class. These are all-time, proof-theoretic reachability exclusions, not finite-time nonhalting simulations.

- For `q0=185`, the result is the standalone original-source theorem `BB6.Agent9Q185.critical_2962_mod16384_unreachable` in [Q185Final.lean](../im-results/agent9-p1-q185/Q185Final.lean), compiled in [original-source CI 42114293669](https://github.com/FlareZ123/bb6/actions/runs/42114293669).
- For the other 48 values, theorems `BB6.Agent9BatchA.q34_critical_unreachable` etc. are produced by [generate.py](../im-results/agent9-p1-q1024-batch/generate.py) and checked by **both successful matrix jobs** of [original-source CI 42115932188](https://github.com/FlareZ123/bb6/actions/runs/42115932188). The source workflow itself enforces **24 standard-axiom final theorem reports in each job**. After the audit, both workflows were restored to manual-only triggers.

## Source and mathematical mechanism

For a fixed `q=q0+1024r`, each of the two source-authentic P1 odd inverse feeder roots admits a small closed graph with states `(m,z0+a*r)`. This graph uses Agent 9's previously source-verified dyadic projection; its exact edge relation is

```text
z = 2^t*v
2*z' + 1 = 16*q + h + m + t + v
m' = m+t+1
h=8 (first feeder) or h=9 (second feeder)
```

The generated Lean proofs establish, for **every** `r` and both feeders, exact initial-state membership, full closure under all admissible dyadic predecessor edges, `m≤10`, and `¬256∣z` for all nodes. Depths `t≥8` cannot satisfy `z=2^t*v` with positive `z`; every smaller depth is explicitly handled by the Lean kernel through finite case analysis and `omega`.

The true source-level halting-gateway theorem is then obtained by instantiating Agent8's separately original-source-certified generic theorem `BB6.Agent8Generic.critical_unreachable_of_shadow` ([CI 42109123502](https://github.com/FlareZ123/bb6/actions/runs/42109123502)). Its upstream original-source chain covers the actual P1 `T`, `Reach`, source-complete `GAncestor` predecessors, even-right and exceptional exits, and authentic two-feeder reduction. No new source interpretation or unproved equivalence is introduced.

The generator is **not a mathematical oracle** in the final proof: it emits ordinary Lean definitions and derivations, each kernel-checked against the original dependencies. Source verifier [.github/workflows/agent9-p1-q1024-batch.yml](../.github/workflows/agent9-p1-q1024-batch.yml) generates and compiles six arithmetic and six final modules in two independently successful jobs. Every output theorem's `#print axioms` was checked to report `[propext, Classical.choice, Quot.sound]`; the workflow fails on `sorryAx` or Lean errors. The separate q185 proof prints its axioms and uses the same source bridge.

## Novelty against previously verified broad classes

The 49 `q0` values are pairwise distinct; every one satisfies `q0 mod4∈{1,2}` and is disjoint from the earlier source-certified `q mod256` families `{14,30,57,61,73,77,106,138,173,217,218,221,233,238,250,254}` and the single `q mod1024` residues `29,297`. This comparison is against the documented broad classes; narrower earlier `n mod65536` theorems may intersect portions of the infinite families. No claim of novelty relative to all external literature is made without a separate audit.

A previously published conservative combined bound, `578/1024`, excluded necessary critical gateways in a complete q-residue period. The present 49 *disjoint* families improve that particular bound to

```text
liminf_{X→∞} #{1≤q≤X : ¬Reach 2 (H(16q+2))}/X ≥ 627/1024 ≈ 61.23046875%.
```

This statement deliberately **does not include** Agent8's separate subsequent cost-11 batch, which can further strengthen the combined result once its overlap is audited and included in an updated synthesis. It is a density bound on eliminated necessary halting gateways, not on the runtime behavior of the original machine.

## Scope

P1's actual halting status remains open. This result does not resolve every critical exponent for P1, any of the other six-state holdouts, or the exact Busy Beaver function BB(6). Future useful work is a complete original-source cost-11 census, then methods overcoming genuinely unbounded inverse trees or bypassing the candidate critical gateway enumeration.
