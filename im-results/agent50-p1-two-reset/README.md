# Agent 50: uniform positive-reset defect budget for the P1 inverse cone

**2026-11-05. Intermediate research; BB(6) remains open.** This dossier studies the exact source inverse chain for the P1 six-state machine
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.
It extends Agent28's exact dyadic word/defect equations and Agent43's original-source two-positive-reset wall obstruction. Mathematical novelty and original-source status must be evaluated separately.

## Mathematical content

Let `n≥42`, `x=n+2`, `K+n+3=7·2^n`, and write a normalized odd inverse hub as `F+D+m=K+2`. A *positive dyadic defect* is a pair `N,C` satisfying

```
0<N≤n+m+1,   C≤2^m,
F+N=7·2^(n−m)·C.
```

For any exact following positive-depth reset of cost `l≥2` and its zero-depth suffix of length `s`, the source-shaped equations are

```
2^l·D' + m = K+D,
2^s·F' + D' + m+l = K+2.
```

`UniformDefectStep.lean` proves a quantified, all-natural **inductive transport theorem**: if `2^m≤W`, `W·24x²<2^n`, and the source's complementary coefficient equality `V+C=2·2^m` holds, then the output has a positive defect `N',C'` and satisfies

```
2^(m+l+s) ≤ W·24x².
```

The heart of the argument is the exact identity
`2^l D' + M=7·2^(n−m)V`,
where `M+N=2(n+m+2)`. The original two-adic divisibility lemma implies
`2^l≤M≤4x`. The output defect is positive and at most `6x`, so the suffix contributes at most `2^s≤6x`.

`ResetSkeleton.lean` packages the exact first positive reset, its arbitrary upper suffix, and every subsequent positive reset into an inductive scalar grammar. The source-shaped bridge `CountSourceBridge.lean` maps the actual upstream `CountCone` transitions to that grammar, retaining arbitrary interleaved zero-depth transitions. `UniformResetChain.lean` gives, after `j` additional positive resets, the exact **polynomial envelope**

```
B(n,j) = 24·(n+2)^3 · [24·(n+2)^2]^j.
```

For the exact source-shaped chain, `2^m≤B(n,j)` whenever `B(n,j)<2^n`. Combining the previous source logarithmic wall condition `2^(n−m)<n` with the stronger growth hypothesis
`B(n,j)·(n+2)<2^n` gives a contradiction. This works for any finite `j`, with a parameter-dependent bound on `n`.

At `j=2`, `B(n,2)·(n+2)=13824(n+2)^8`, and `ThreeResetGrowth.lean` proves

```
∀ n≥62, 13824(n+2)^8 < 2^n.
```

The proposed original-source statement is `source_critical_exact_three_reset_no_wall`: for `n≥62` and every exact source `CountCone` from `(14·2^n−2n−16,3)` with exactly three positive-depth inverse steps, the affine wall `b=4(m+n)` cannot be reached.

## Proof provenance

- `TwoResetSharp.lean`, `TwoResetDefectSharp.lean`, `UniformDefectStep.lean`, `UniformResetChain.lean`, `ThreeResetGrowth.lean`: checked locally with Lean 4.36.0-rc2, standard axioms only, against the unchanged mathematical predecessor definitions. The corresponding original-source manual CI **passed in run [42071630186](https://github.com/FlareZ123/bb6/actions/runs/42071630186)**.
- `TwoResetFirstDefect.lean` and `ThreeResetExactEquations.lean`: decoded from `three-reset-source.tar.xz.b64` with exact SHA-256 of the binary archive `be550c5b326d27c459197cf81858fd8ecad95abe657d0a9f269c65bbbb12b97f`. They also compiled in that successful original Agent28-source CI.
- `ResetSkeleton.lean`, `CountSourceBridge.lean`, `CountFinal.lean`: decoded from `count-bridge.tar.xz.b64`, archive SHA-256 `5b8a74e3e101e389c09a891cd8bda6da803d3bb70abbcb75fdfab8071e804895`. Their local signature-matching mock audit was followed by a **successful complete unchanged-source CI**: [run 42072880437](https://github.com/FlareZ123/bb6/actions/runs/42072880437), [job 127405228553](https://github.com/FlareZ123/bb6/actions/runs/42072880437/job/127405228553), Lean 4.36.0-rc2, source SHA `a46a8e17d56a8425007b6218596c56f272b6b6bf`. The job independently rebuilt unchanged original Agent1, Agent47, Agent28 modules and all new Agent50 modules, with no mock modules. Both `counted_excludes_budgeted_wall` and `source_critical_exact_three_reset_no_wall` have final axiom audits exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. This establishes the full source-connected three-reset exclusion.
- The earlier original-source two-reset exclusion at `n≥55` is already proved in [Agent43's dossier](../agent43-p1-two-reset/README.md), [CI 41762094303](https://github.com/FlareZ123/bb6/actions/runs/41762094303). The new source-shaped route's distinct contribution is *three resets* plus the arbitrary reset-count budget invariant.

The theorem concerns the **affine wall** in one inverse feeder family. Even a source-certified exclusion of three reset counts leaves histories with four or more positive resets, high-cost exits, and exceptional `c=1` exits. A complete P1 machine halt/nonhalt decision, global BB(6) upper bound, and exact BB(6) value remain open.

## General source-connected quantitative lower bound (2026-11-05 17:25 UTC)

**Original-source Lean CI passed:** [run 42074258493](https://github.com/FlareZ123/bb6/actions/runs/42074258493), job [127410112494](https://github.com/FlareZ123/bb6/actions/runs/42074258493/job/127410112494). Final axioms for both new theorems are exactly `[propext, Classical.choice, Quot.sound]`. The workflow rebuilds original `CountCone`, `OddCone`, `UpperTail`, and `inverseAt` definitions with no mock imports or `sorryAx`.

[WallCountLowerBound.lean](WallCountLowerBound.lean) certifies the closed form

```
budget n j = 24^(j+1)*(n+2)^(2*j+3)
```

and proves the **necessary all-count inequality** for every genuine critical `CountCone` affine-wall history of positive-depth reset count `z≥1`, for `n≥42`:

```
2^n ≤ 24^z*(n+2)^(2*z+2).
```

This is an unconditional quantified restriction for all finite positive `z`; unlike fixed-j exclusion corollaries, its theorem statement contains no auxiliary budget hypothesis. Its elementary logarithmic consequence is `z≥(n−2log₂(n+2))/(log₂24+2log₂(n+2))`, so wall histories require `z=Ω(n/log n)` as n increases.

[WallNeedsFour.lean.xz.b64](WallNeedsFour.lean.xz.b64) preserves the source-derived full `OddCone` theorem `source_critical_wall_needs_four_resets`: for **every n≥62**, if a genuine critical odd inverse cone hits the affine wall, it has a genuine `CountCone` witness of at least **four** positive-depth `inverseAt` transitions. This covers the zero-reset case using the original `source_critical_zero_reset_no_wall` theorem. The compressed source has binary SHA256 `f7d4d159179e4054eb3424f71edc98174729ce236a1364f39623c0b0f8f67fc2` and is verified and compiled by the same successful CI run.

**Research boundary:** The source wall itself is a low-cost even-exit necessary condition. An unbounded positive-reset count is still possible under this inequality; high-cost positive-even terminals and exceptional `c=1` exits remain open. No global P1 or BB(6) decision is implied.

## Next research actions

The full-source CI and final axiom audit have passed. Next, compose `CountFinal.lean` with Agent43's `n≥55` results in a single named Lean `z≥4` wall requirement for every `n≥62`. For a full P1 decision, devise a source-connected method controlling all remaining reset histories and all terminal exits.
