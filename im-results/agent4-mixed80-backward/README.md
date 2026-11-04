# Machine C: an M80 reverse-closed cylinder beyond basic parity

Agent 4, 2026-11-04. This is an **intermediate all-time reachability exclusion**, not a halting decision. The locally checked Lean proof uses Lean 4.36.0-rc2 and standard axioms only. The unchanged-repository-source manual CI audit is [run 41889910700](https://github.com/FlareZ123/bb6/actions/runs/41889910700), **pending when this note was written**. Earlier failed runs were reproducibility issues: run 41888705457 referenced a local Reach declaration absent from original A4Backward, and run 41889154293 encountered a single bad source-archive byte. Both are corrected in the present revision.

## Exact mathematical statement

Let `BB6CLine.Reach` be the inductive finite-reachability predicate for the original checked-in [Machine C accelerator](../agent11-c-line/CLine.lean), starting at the authentic blank entry `(5,0,1)`. The new Lean theorem `A4Five80.source_no80` proves

```lean
∀ a k : Nat, a % 80 = 41 → k % 80 = 15 →
  ¬ BB6CLine.Reach (a,k,0)
```

Equivalently, in the [unified complete nonzero stopping equation](../agent1-c-unified-gateway/README.md),
```
a = 2*u+1
k+u+3*m+4 = 4^(m+1)*(u+2)
```
we have the genuine all-natural parameterized corollary `A4Five80.source_stop_m11_u60_unreachable`:

```
u % 80 = 60, m % 80 = 11  ==>  ¬Reach (2*u+1,k,0).
```

The power congruence `4^(m+1)%80=16` in this sector and the induced `(a%80,k%80)=(41,15)` are kernel-proved in [Five80Stop.lean](Five80Stop.lean). This excludes infinitely many **candidate stopping inputs**, with no assumption that these candidates are encountered by the real trajectory. The entire remaining stopping family, Machine C and BB(6) are still unresolved.

## The compact predecessor-closed invariant

For each nonnegative `a,k,c`, define `bad` as follows. For `c=2`, it is false. For `c<4` and `c≠2`, set `w=(k+c)` and use

```
(a%80,w%80) = (41,15)
or (a%80,w%40) = (26,19)
or (a%80,w%40) = (66,39).
```

For `c≥4`, set `d=(a+80-c%80)%80`, `t=(a+k)%80`, and use

```
(d,t%40) = (0,31), (23,2), (40,11), (63,22), (65,25),
or (d,t) = (38,53).
```

All nine clauses together are predecessor-closed for every actual `A4Backward.nextC` transition. The true root `(5,0,1)` is outside. [Five80Compact.lean.gz.b64](Five80Compact.lean.gz.b64) is the exact 7,201-byte locally Lean-checked source, gzip then base64 encoded for reliable repository transport; decompressed SHA256 is `62b9841a3d1dd1b06c14ed87a8b7f11703a342a0b3d93d7c01e882c7b2e40bf2`. The first source-level theorem uses the existing original [A4Backward.nextC_source_equal](../agent4-mixed96-backward/SourceBridge.lean) to transport closure to the untouched [CLine.lean](../agent11-c-line/CLine.lean).

The independent [C++17 representative checker](check_core.cpp) verifies all **4,172,800 nonhalting representative edges** of the M80 quotient, a total of **537,600** projected triples. Exactly **895** projected vertices satisfy `bad`; its predicate is independent of the first-return proof. The checker verifies every checked representative has the same predicate value as its projection. The Lean proof is all-natural and does not depend on this finite checker.

## Comparison and limits

The candidate sector has `a%4=1,k%4=3`, so it is outside the two `a,k` odd–odd parity exclusions in [Agent38's source-certified invariant](../agent38-c-section-mod4/README.md). Its unified parameters satisfy `(u+m)%4=3`, so they also survive [Agent1's shared barrier](../agent1-c-unified-gateway/README.md). For the concrete first member `(u,m)=(60,11)`, the actual candidate is `(a,k,c)=(121,1040187295,0)`. Independently computed M16, M32, M64, M96 and M192 forward **overapproximations** admit its corresponding projected state, whereas M80 rejects it. This establishes separation between those *particular finite quotient computations*; it does not establish non-subsumption by all other source-certified invariants, stronger mixed quotients or published work. Some higher parameter lifts overlap Agent4's earlier mixed192 side family. A full independent novelty comparison remains open.

The pre-existing pinned original DeepMind Cryptids-to-CLine source transport was separately checked in [CI 41696303681](https://github.com/FlareZ123/bb6/actions/runs/41696303681). This file's new CI checks the unchanged checked-in accelerator and its source-equality bridge; the older upstream transport remains a named separate dependency. No universal Busy Beaver upper bound or exact value follows.

## Reproduction and next useful problem

The manual-only [GitHub Actions workflow](../../.github/workflows/agent4-machine-c-80.yml) checks the finite graph, reconstructs the hash-pinned Lean source, compiles original `CLine`, `BackwardMod`, `SourceBridge`, `Five80Compact`, `Five80Stop` and `Five80Source`, and prints the final axioms. Reproduction does not need a simulation cutoff.

The best follow-up is to compare this exact source-gate cylinder against Agent3/38/43 and newer M512 and inverse-cone results on the **same original candidate family**, then seek a structural extension that covers a complete still-surviving stopping sector. Do not extrapolate a complete Machine C nonhalting proof from one cylinder.
