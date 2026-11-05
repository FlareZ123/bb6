# Proposed extension: all-count small-left half-plane for P1

**Agent 43, 2026-11-05. Mathematical derivation using source-verified scalar prerequisites; generalization of Agent50's final-wall proof awaits direct source Lean integration.** This note targets a stronger region than the exact equality wall.

## Candidate uniform result

For genuine original critical `CountCone` histories `n≥256` with `z` positive-depth resets and total inverse cost `m`, the following **paper-level** necessary implication is expected:

```
b ≤ 4*(m+n)  ==>  m > n+z.
```

For `62≤n<256`, the same argument suggests `b≤4(m+n) ⇒ m>n`. The exact original-source CI for this *inequality-region extension* has **not** been run; the already source-verified Agent50 theorem explicitly assumes equality `b=4(m+n)` and must not be cited as if it already covered the inequality.

## Mathematical mechanism (where equality is inessential)

### (1) Any small-left word has the same near-exponential cost necessity

Agent28's source-certified exact scalar word invariants read `2^m D+T=1+K A`, `A<2^m`, `T≥0`, `F+D+m=K+2`, `K+n+3=7·2^n`. Consequently,

```
K*(2^m−A)=1+2^m*(F+m−2)−T
```

as an *integer identity*. Since `2^m−A≥1`, `K≥0`, and `T≥0`, this proves `K≤1+2^m*(F+m−2)`. If `b≤4(m+n)` then `F=(b+12)/2≤2(m+n+3)`, and hence

```
K ≤ 1+2^m*(3m+2n+4).                 (W)
```

This is **exactly the weak wall-necessity bound** used in Agent28's all-word `source_critical_wall_cost_logarithmic_gap`, but it follows from a left *inequality* just as from the equality wall. For n≥14 it implies the same necessary `2^(n−m)<n` (if m≥n this is automatic). No original-source change to the inverse word or to its core mass equation is needed.

### (2) The last-reset lower energy bound is also monotone in b

For any counted history with `z≥1`, `m≤2^n`, the outgoing mass of its final positive reset is at least `2^(n+1)`, independent of the endpoint b. The zero-depth suffix gives

```
2^m F ≥2^(n+2*z+1).
```

If the endpoint has `b≤4(m+n)`, then `F≤2(m+n+3)`, so

```
2^(n+2*z) ≤2^m*(m+n+3).            (L)
```

This is the same source-shaped *last-reset tradeoff* as in [LastResetTradeoff.md](LastResetTradeoff.md), and uses only the upper bound on b. No exact-wall equality is needed.

### (3) Reuse the already source-certified all-count polynomial envelope

Agent50's source-verified `UniformResetChain` / `CountSourceBridge` establish a bound on `2^m` for every original counted inverse history with a prescribed finite reset count, **independently of any final wall** under their explicit budget hypotheses. The terminal contradiction in `counted_excludes_budgeted_wall` uses the small-cost wall-necessity `2^(n−m)<n`. By (W), that same necessity holds for a small-left **inequality**. Repeating the proof with this generalization is expected to establish the all-count necessary inequality

```
2^n ≤24^z*(n+2)^(2*z+2)           (R)
```

for every genuine small-left history with z≥1, n≥42. **This is the specific unverified source bridge.** The existing theorem proves (R) only on exact b=4(m+n), so (R) on a half-plane is currently a derived research target.

Once (R) is proved, the entirely source-independent dyadic lemma in [WallAboveNPlusZ.md](WallAboveNPlusZ.md) uses (L) to show `m>n+z` for n≥256; similarly [WallBelowN.md](WallBelowN.md) provides the n≥62 lower cost exclusion once zero-reset cases are treated.


### (4) The zero-reset subwall case is separately excluded at low cost

For `z=0`, every original counted edge has depth zero. The unchanged source theorem `upper_tail_dyadic` gives `2^m F=F_0=7P−n−2`. Under the contradiction hypothesis `m≤n+z=n`, this implies `2^m | F_0` and `2^m | 7P`, hence `2^m | (n+2)` and `2^m≤n+2`. A subwall endpoint gives `F≤2(m+n+3)≤2(2n+3)`, so `7P−n−2≤2(n+2)(2n+3)`, false for every `n≥256` by a one-base exponential-vs-quadratic induction. Thus the proposed n≥256 half-plane result does not require treating z=0 as a positive-reset history.

## Boundary / next action

An effective source-Lean next action is to replace the final `hwall:b=4(m+n)` of Agent50's source lower-count theorem with a weaker `hle:b≤4(m+n)`, proving (W) from the exact `OddWord` mass identity and reusing the original budget proof. Then compose this with the counted last-reset factorization in [CountedLastResetDraft.lean](CountedLastResetDraft.lean), currently uncompiled.

This proposed extension covers synthetic source inverse histories in an entire lower-left region and could be reused for other P1 feeders. It remains a **necessary** inverse-cone obstruction, not a blank-root halting decision or any BB(6) bound. External novelty and source CI are pending.
