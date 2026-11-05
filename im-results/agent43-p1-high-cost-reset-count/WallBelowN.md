# Uniform exclusion of the small-cost P1 affine wall

**Agent 43, 2026-11-05 21:25 UTC. Paper theorem; no combined original-source Lean audit yet.** This note derives a *uniform, all-reset-count* obstruction for one genuine P1 halting-feeder family, using original-source equations and Agent50's source-Lean-certified reset-count lower bound. It is not a complete P1 or BB(6) decision.

## Claim

For every `n≥62`, every genuine counted odd inverse history
```
CountCone (14*2^n-2*n-16) 3 b d m z
```
satisfying the **low-cost affine wall**
```
b=4*(m+n)
```
must have **`m>n`**.

This strengthens Agent28's all-word necessary `2^(n-m)<n`, and covers **every** finite reset count `z`. Unlike Agent50's `z≥4` and `z=Ω(n/log n)` necessary restrictions, it removes an entire uniform cost sector. Its mathematical dependence on Agent50's original-source theorem is material.

### Source-certified prerequisites

1. Original-source [OddConeMass](../agent1-p1-quarter/OddConeMass.lean), [InverseIff](../agent1-p1-quarter/InverseIff.lean), and [OneResetCount](../agent28-p1-word-automaton/OneResetCount.lean) imply the exact word mass and transition identities below. Their source alignment is independently established in Agent28's [OddWordSourceBridge](../agent28-p1-word-automaton/OddWordSourceBridge.lean).
2. Agent50's [WallCountLowerBound](../agent50-p1-two-reset/WallCountLowerBound.lean), [source CI 42074258493](https://github.com/FlareZ123/bb6/actions/runs/42074258493), proves, for every genuine source counted affine-wall history with `n≥42`, `z≥1`:
   ```
   2^n ≤ 24^z*(n+2)^(2*z+2).
   ```
3. Agent50's same source-CI run proves that every wall history for `n≥62` has at least **four** positive-depth resets `z≥4` (including the zero-reset elimination).

The **new derivation below is mathematical paper proof** using these source-certified inputs. The composite `CountCone` conclusion has not yet been checked by Lean on the unchanged source.

## Last-reset lemma

Write `P=2^n` and `K=7P−n−3`. Every genuine counted history from the critical seed admits normalized coordinates

```
F=(b+12)/2,  D=(d−1)/2,  F+D+m=K+2.
```

Each inverse edge of depth `t≥0`, cost `l=t+1≥1`, has

```
2^l D' + m = K+D,   m'=m+l,   F'+D'+m'=K+2.
```

The source requires `D≥1`, `D'≥2`, `F,F'≥6`. When `t=0` the equations force `2F'=F`, exactly. Each positive reset has `t≥1`, thus `l≥2`.

Suppose there are `z≥1` positive resets, and choose the **last** positive reset. Denote its outgoing cost by `m_1`, outgoing mass by `F_1`, and let `s=m−m_1` be the length of its subsequent zero-depth suffix. Every reset cost is at least two, so `m_1≥2z`; the suffix satisfies `2^sF_{end}=F_1`.

For the last positive edge, `l≥2`. Since the incoming `D≤K+2`, we have `4D'≤2^lD'≤K+D≤2K+2`, hence `2D'≤K+1`. The outgoing mass obeys

```
2F_1 = 2(K+2−D'−m_1)
     ≥ K+3−2m_1
     = 7P−n−2m_1.
```

**Assume `m≤n`.** Then `m_1≤m≤n`, and for every `n≥62` we know `P≥3n`. Therefore `2F_1≥7P−3n≥4P`, i.e. `F_1≥2P`.

At the affine wall, `F_{end}=2(m+n+3)`. Hence

```
2^s · 2(m+n+3) = F_1 ≥2P,
2^s(m+n+3) ≥ P.
```

From `m=m_1+s`, `m_1≥2z`, `m≤n`, we have `s+2z≤n`. Multiplying the previous inequality by `2^(n−s−2z)` gives

```
P = 2^n ≤ 2^(n−2z)(m+n+3),
4^z ≤ m+n+3 ≤2n+3.                        (★)
```

Only exact original-source identities, positivity, and ordinary integer arithmetic are used. For fixed n, this last-reset obstruction applies to **every positive reset count** without requiring a defect-preserving hypothesis.

## Exponential-vs-polynomial contradiction for every z≥4

The following standalone all-integer implication is the needed lemma:

```
∀ z≥4, ∀ n≥62,
  4^z ≤ 2*n+3 →
  24^z * (n+2)^(2*z+2) < 2^n.
```

**Case `z=4`.** `256≤2n+3` gives `n≥127`. At `n=127` an exact integer calculation verifies
`24^4·129^10<2^127`. For every `n≥127`,
`(n+3)^10<2(n+2)^10` (e.g. bound its binomial ratio by that at `n=127` and verify `130^10<2·129^10`). Thus induction proves `24^4(n+2)^10<2^n` for all such n.

**Case `z≥5`.** The elementary inequality
`4^z≥4(2z+2)^2+3` holds at `z=5` and is preserved by induction, because the left side quadruples and the right side increases quadratically. Combining it with `4^z≤2n+3` yields
`n≥2a²` for `a=2z+2≥12`.

For any `x≥16`, `log₂x≤√x`; for `n≥2a²` with `a≥12`, elementary squaring gives `a√(n+2)≤3n/4`. Also `n≥2a²=8(z+1)^2≥20z`, and `log₂24<5`. Therefore
```
log₂(24^z(n+2)^a)
  = z·log₂24 + a·log₂(n+2)
  < 5z + a√(n+2)
  ≤ n/4 +3n/4
  = n.
```
Exponentiating proves the displayed implication for all `z≥5`. The logarithms are a transparent mathematical proof technique, not source Lean lemmas. An elementary alternative could use finite dyadic power bounds in the source formalization.

Finally, by the certified wall theorem, `2^n≤24^z(n+2)^(2z+2)`. The last-reset estimate `(★)` and the new all-integer implication force the opposite strict inequality, contradiction. Hence **every genuine n≥62 affine-wall counted history has m>n**, provided the source equations and original Agent50 input are composed as cited.

## Evidence, limits, and next verification

- The z=4 and z=5 sample inequality endpoints were checked with exact Python integers. This is an auxiliary smoke test; the analytic induction proves the universal implication.
- **Formal gap:** Direct all-parameter original-source Lean assembly and final `#print axioms` are pending. The existing source CI proves the inputs separately; it does *not* certify this new composite theorem yet. A good intermediate Lean target is the all-natural numeric implication `z≥4 ∧ 4^z≤2n+3 → 24^z(n+2)^(2z+2)<2^n`.
- No P1 machine decision follows: wall histories with `n<m≤2^n`, high-cost histories `m>2^n`, and exceptional input `c=1` remain possible under these arguments.
- The uniform *high-cost* cost-vs-reset bound in [StrongEnergy](StrongEnergy.md) is logically separate and complements this *low-cost* exclusion.
- The theorem's novelty relative to existing repository notes and outside literature has not been independently reviewed. Keep this in `im-results/` until the original-source proof and review justify a publishable result.
