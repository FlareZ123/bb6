# Space Needle: fifth-linear terminal inverse and authentic-root exception exclusion

**Research scope (7 November 2026).** This note records an exact fifth-linear restriction on the one-step terminal inverse of the original six-state Space Needle machine, together with a finite inverse certificate excluding its large exceptional feeder from the genuine blank-start orbit. BB(6) and the Space Needle halting problem remain **undecided**. The original-source Lean workflow is [the selective manual check](../../.github/workflows/agent48-space-needle-five.yml); the first CI of the new arithmetic bound was dispatched as [run 42332720650](https://github.com/FlareZ123/bb6/actions/runs/42332720650). The rooted extension has a separate follow-up check to be recorded when complete. Never infer success before a completed green source run.

## Mathematically precise result

The pinned published Cryptids [high-level source](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean) starts from `N 1`; a nonterminal counter `d` factors as `d+2=2^v(2q+3)`, and one successful high-level successor has `d'=d+v+3(q+1)`. An immediate transition into a terminal tower of exponent `K>=1` requires and, with nonnegative parameters, is equivalent to

```text
E(q,v,K): 2^K=(2^(v+1)+3)*q+3*2^v+v+3.
```

The new [FifthHigh.lean](FifthHigh.lean) proves for **all natural** `q,v,K`:

```text
E(q,v,K) AND 4*v<=K+2
  implies
(q=340282366920822406584691642613415018481, v=42, K=171)
OR 5*v<=K+3.
```

Combined with the earlier source-certified [quartic bound](NeedleQuarticEnumerate.lean), every terminal source satisfies the complete disjunction

```text
(q,v,K)=(61,6,13)
OR (q,v,K)=(340282366920822406584691642613415018481,42,171)
OR 5*v<=K+3.
```

Both exceptional triples solve the actual affine equation, so they cannot be dropped from the **unrestricted** source-level statement. The large exception coincides with the `t=1` instance of [Agent 20's unbounded-valuation construction](../agent20-needle-coprime/NeedleVariableValuation.lean). This observation fixes its relationship to prior research and rules out claiming the exception itself as a new construction.

[NeedleQuinticEnumerate.lean](NeedleQuinticEnumerate.lean) proves a complete all-natural exact list `quinticParents K` by checking all valuations `0<=v<=floor((K+3)/5)` and inserting the explicit K=13 and K=171 exceptions. The iff is over the actual affine equation for every K, not a finite experimental cutoff. [NeedleQuinticEnumerateSource.lean](NeedleQuinticEnumerateSource.lean) translates it to the original pinned high-level transition.

## Proof mechanism

Write `D=2^(v+1)+3`. In the high region `K=4v+3+s`, reduce the fourth power `(2^(v+1))^4` modulo `D`. Exact natural-number identities establish

```text
2*v ≡ 81*2^s+3 (mod D).
```

If `v>=s+7`, both sides are strictly below D, making this a literal integer equality; its parity forces `s=0`, and then `2v=84`, hence v=42. Substitution determines the exceptional q exactly.

In the near-fourth region `K+t=4v+4` with `2<=t<=6`, the same polynomial reduction yields

```text
2^t*v ≡ 81+3*2^(t-1) (mod D).
```

For v>=10 both sides are below D, contradicting parity. Exhaustive *kernel-elaborated* reduction of the remaining v<10, 2<=t<=6 yields only the actual equation solutions `(45,2,9)`, `(214,3,12)`, and `(62600,5,22)`, all inside the fifth-linear bound. The proof uses finite arithmetic only after reducing the unbounded case to v<10.

Local Lean 4.36.0-rc2 compiled the complete [FifthHigh.lean](FifthHigh.lean) with axiom audit `[propext, Classical.choice, Quot.sound]` for `fifth_exact` and no sorry. The separate all-natural enumerator was checked locally against the **exact public signatures** of the earlier quartic theorems, then submitted for unchanged original-source CI.

## Blank-root exception: more than a synthetic constraint

The large source counter is the exact 171-bit natural number

```text
source42 = oddTower 340282366920822406584691642613415018481 42
         = 2993155353252668329380384070183193549327509602959358.
```

The complete source inverse of Agent 20's `NeedleGeneralInverse.parents` has an **empty** finite predecessor list at `source42+2`. The [original-root Lean module](SpaceNeedleFifthRoot.lean) provides a kernel-computable `source42_has_no_parents` certificate, then derives `¬ReachN source42`: it is different from initial counter 1 and every noninitial reachable counter has a genuine incoming predecessor. This excludes the large exceptional feeder **from the real blank orbit**, without having to decide whether it is synthetically legal as a predecessor of a terminal.

The earlier genuine-root theorem [NeedleRootSharp.blank_never_7998](../agent20-needle-coprime/NeedleRootSharp.lean) excludes the K=13 exceptional source. Combining both with the source-checked cubic halting equivalence gives the new claimed rooted criterion, pending complete original-source CI:

```text
IsHalt originalSpaceNeedle
  iff ∃ k q v,
    ReachN (oddTower q v)
    AND (v,q) ∈ quinticParents(k+1)
    AND 5*v <= k+4.
```

This removes *both* exceptional feeder cases from the authentic-root existential. It remains unbounded in k and reachability, and is **not** a halt/nonhalt verdict.

## Comparison, use, and decisive residual problem

The prior exact quartic inverse enumeration checks valuations to `floor((K+2)/4)` plus one exception. This theorem improves the uniform finite search width to `floor((K+3)/5)` plus two explicit exceptions, and the rooted criterion can omit both exceptional cases. The [previous all-slope superlinear theorem](SuperlinearOne.lean) already proves `c*v<K` whenever v>=3^c+1, and its [optimized enumerator](SuperlinearOptimized.lean) may give fewer candidates for sufficiently large K. The present result fills a uniform, small/medium-valuation gap and adds a genuine blank-root exclusion; there is no claim of external mathematical novelty or a new lower bound.

The unresolved question is whether the actual deterministic `N 1` orbit reaches **any** still-admissible terminal feeder. Exact per-target root reachability is [already decidable](../agent20-needle-coprime/NeedleRootDecisionSource.lean), but the universal quantifier over all exponents remains. Subsequent work should seek an all-time history-sensitive invariant, a genuine terminal witness, or an exhaustive root closure rather than only increasing the synthetic slope.
