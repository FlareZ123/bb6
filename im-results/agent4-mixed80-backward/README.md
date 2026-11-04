# Machine C: an M80 reverse-closed cylinder beyond basic parity

Agent 4, 2026-11-04. This is an **intermediate all-time reachability exclusion**, not a halting decision. **Original-source proof verified.** The complete unchanged-source Lean 4.36.0-rc2 manual [CI 41889910700](https://github.com/FlareZ123/bb6/actions/runs/41889910700) **succeeded**, compiling the source bridge, the new all-natural closure, the stopping arithmetic, and the source-level reachability theorems. The three final theorem audits `source_blank_never_bad80`, `source_no80`, `source_stop_m11_u60_unreachable` report only `[propext, Classical.choice, Quot.sound]`, no sorryAx. Earlier failed runs were reproducibility issues: run 41888705457 referenced a local Reach declaration absent from original A4Backward, and run 41889154293 encountered a single bad source-archive byte. Both are corrected in the present revision.

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
we have two genuine all-natural, disjoint parameterized corollaries `source_stop_m11_u60_unreachable` and `source_stop_m51_u20_unreachable`:

```
(u % 80, m % 80) = (60,11) OR (20,51)  ==>  ¬Reach (2*u+1,k,0).
```

For every `m≥2` satisfying the exact stopping equation, **these are precisely the two parameter residue pairs mapping to this excluded cylinder**. [Five80OnlyTwo.lean](Five80OnlyTwo.lean) proves the arithmetic equivalence `stopping_m80_iff_two` for all natural inputs; in both sectors `4^(m+1)%80=16`, implying `(a%80,k%80)=(41,15)`. The individual arithmetic consequences are checked in [Five80Stop.lean](Five80Stop.lean) and the second source corollary in [Five80Second.lean](Five80Second.lean). All passed unchanged-source [manual CI 41891467952](https://github.com/FlareZ123/bb6/actions/runs/41891467952) with only standard axioms. This excludes infinitely many **candidate stopping inputs**, with no assumption that these candidates are encountered by the real trajectory. The entire remaining stopping family, Machine C and BB(6) are still unresolved.

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


## Second independently certified M80 reverse core: first stopping family

**New as of 2026-11-04 19:04 UTC:** A separate compact all-natural reverse-closed M80 core excludes every authentic accelerated state `(1,k,0)` with `k%80=71`. The genuine first-family stopping equation `k+3*m+4=2*4^(m+1)` intersects this cylinder **if and only if** `m%80=39` for all `m≥2`. The formal theorem `A4First80.first_m80_iff` proves this exact arithmetic iff, and `A4First80.source_first_m39_unreachable` proves that **all** resulting first-family halting candidates are unreachable from the genuine blank entry at any finite accelerated time.

The entire source chain **passed unchanged-source Lean 4.36.0-rc2 [CI 41892845571](https://github.com/FlareZ123/bb6/actions/runs/41892845571)**. Full axioms of `backward_step`, `source_blank_never_bad80`, `source_no_first80`, and `source_first_m39_unreachable` were `[propext, Classical.choice, Quot.sound]`. `first_m80_iff` used only `[propext, Quot.sound]`. None contained `sorryAx`.

The reverse core has these explicit predicates, with `w=k+c`:
- For `c=2`, false; for `c<4` otherwise, `(a%80,w%80)=(1,71)` or `(a%80,w%40)=(34,11),(74,31)`.
- For `c≥4`, take `d=(a+80-c%80)%80`, `t=(a+k)%80`; require `(d,t%40)=(9,33),(16,35),(31,2),(56,15),(71,22)` or exact `(d,t)=(78,69)`.

The entire all-natural `A4First80.backward_step` is in [First80.lean.gz.b64](First80.lean.gz.b64), reconstructed via the manual CI workflow with SHA256 `ccbdee97223d0fb09899a3a72ac758aa9b3cce43c7ab20c326e972c4371e4036`; [First80Source.lean](First80Source.lean) imports the **unchanged** original CLine and first-family reach, while [First80Arithmetic.lean](First80Arithmetic.lean) and [First80Stop.lean](First80Stop.lean) prove exact parameter arithmetic and its root exclusion.

An independent C++ implementation [check_first.cpp](check_first.cpp) exhaustively verifies reverse closure for all **4,172,800 representative edges**, **895** forbidden quotient states, with the genuine root outside. Both first/second finite checkers and the complete original-source Lean chain passed [follow-up CI 41893106291](https://github.com/FlareZ123/bb6/actions/runs/41893106291).

**Novelty boundaries:** The new `m%80=39` first-depth class is disjoint from the previously specifically cited Agent46 `m%64=38,58`, `m%128=3,51`, and Agent21 `m%64=11` classes as *congruence conditions* only in part; arithmetic class intersections can occur at larger periods. Its witness candidate `(a,k,c)=(1,k_{m=39},0)` is admitted by the specified earlier low-precision forward quotient checks. Broader overlap against Agent3/11/15, Agent43 kernel quotient and published results is **not yet fully audited**. The two cores give an independently source-certified obstruction in **both** of Machine C's stopping sectors, but leave infinitely many halting candidates in each and do not decide the machine or BB(6).

## Reproduction and next useful problem

The manual-only [GitHub Actions workflow](../../.github/workflows/agent4-machine-c-80.yml) checks the finite graph, reconstructs the hash-pinned Lean source, compiles original `CLine`, `BackwardMod`, `SourceBridge`, the new `Five80Compact`, `Five80Stop`, `Five80Source`, `Five80Second` and `Five80OnlyTwo`, and prints the final axioms. Reproduction does not need a simulation cutoff.

The best follow-up is to compare this exact source-gate cylinder against Agent3/38/43 and newer M512 and inverse-cone results on the **same original candidate family**, then seek a structural extension that covers a complete still-surviving stopping sector. Do not extrapolate a complete Machine C nonhalting proof from one cylinder.
