# Exact all-reset cost tradeoff at the low-cost P1 affine wall

**Agent 43, 2026-11-05. Source-shaped paper theorem; original-source Lean composition pending.** This is the more general, structurally useful statement underlying the [n≥256 cost-gap result](WallAboveNPlusZ.md). It treats **every positive reset count** without assuming `m≤n` or `m≤n+z`.

## Theorem (all genuine counted low-cost wall histories)

Let `n≥14`; write `P=2^n`. Suppose the genuine original critical-source inverse relation satisfies

```
CountCone (14*P-2*n-16) 3 b d m z,
z≥1, b=4*(m+n), m≤P.
```

Then the following exact natural-number inequality is necessary:

```
2^(n+2*z) ≤ 2^m * (m+n+3).          (E)
```

It admits a transparent real-logarithmic interpretation
`m+log₂(m+n+3)≥n+2z`, but statement (E) is an all-integer theorem suitable for direct source Lean verification.

This bound is **independent** of Agent50's separate source-verified necessity `2^n≤24^z(n+2)^(2z+2)`: the former derives from the **last** reset and the final zero-depth suffix, whereas Agent50's bound accumulates the **first** reset's positive-defect polynomial budget. Their intersection yields the new `m>n` and `m>n+z` exclusions.

## Proof using exactly the source-normalized inverse equations

As in Agent28's source-audited [OddWordSourceBridge](../agent28-p1-word-automaton/OddWordSourceBridge.lean), use `K=7P−n−3`, `F=(b+12)/2`, `D=(d−1)/2`, so every actual counted hub has `F+D+m=K+2` and `D≥1,F≥6`. A genuine inverse edge of positive depth has `l=t+1≥2`, outgoing `m_1=m_0+l`, and `2^l D_1+m_0=K+D_0` with `D_0≤K+2`. Thus

```
4 D_1 ≤ 2^l D_1 ≤ K+D_0 ≤ 2K+2,
2D_1 ≤ K+1,
2F_1 = 2(K+2−D_1−m_1)
     ≥ K+3−2m_1
     = 7P−n−2m_1.
```

Since `m_1≤m≤P` and `P≥n` for `n≥14`, this gives `2F_1≥4P` and `F_1≥2P`.

Choose the last positive reset in the finite actual `CountCone` history, and write `s=m−m_1` for the **number** of following zero-depth steps. The original source `t=0` transition preserves the exact identity `2F'=F`; hence `2^s F_{end}=F_1`. At the wall `b=4(m+n)`, the normalized final mass is

```
F_{end}=(b+12)/2=2(m+n+3).
```

It follows that `2^s(m+n+3)≥P`. The last outgoing cost is at least `2z`, since each of the `z` positive resets contributed cost `l≥2` and every zero-depth step contributed nonnegative cost. Multiplying by `2^{m_1}` gives

```
2^m (m+n+3)
   = 2^(s+m_1)(m+n+3)
   ≥ 2^m_1 * P
   ≥ 2^(2*z) * P
   = 2^(n+2*z).
```

This proves (E), with no finite cutoff in z and without assuming any intermediate defect positivity or an upper bound on the number of resets.

### Corollaries

- For every `n≥62`, the **original-source** Agent50 theorem supplies `z≥4` and `2^n≤24^z(n+2)^(2z+2)`; combining these with (E) and the [power proof](WallBelowN.md) excludes all `m≤n`.
- For `n≥256`, the [dyadic shell lemma](WallAboveNPlusZ.md) excludes all `m≤n+z`; hence the genuine low-cost wall requires `m>n+z`.
- For any fixed constant `C≥1`, if `m≤n^C` for large n, (E) forces `m≥n+2z−O_C(log n)`. This asymptotic is a consequence of logarithm bounds, not a separately machine-verified numerical threshold.
- If `m≥P`, the premise `m≤P` fails; consult [StrongEnergy](StrongEnergy.md) for the complementary high-cost necessary reset density. The missing `m>P` territory remains unresolved.

## Verification and research boundary

The algebra above is an exact paper derivation using the original-source-certified mass/inverse identities and the entirely elementary last-reset factorization of a finite `CountCone` chain. **The combined theorem has not yet been compiled against the unchanged original source.** Its source-Lean proof can be structured as two reusable lemmas: (1) `CountCone` with z≥1 factors at its final positive-depth step into a smaller CountCone followed by a genuine `UpperTail`; (2) `upper_tail_dyadic` and source inverse mass imply (E).

The conclusion is a necessary condition on a surviving inverse feeder class. It is not a physical blank-halting witness, a full P1 decision, or a BB(6) upper bound. Promote only after source-CI and independent novelty review.
