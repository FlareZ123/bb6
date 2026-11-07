# P1: source-count subwall and exceptional right-five inverse restrictions

**Current synthesis, 7 November 2026.** These are mathematical restrictions on genuine original-source finite inverse histories. Their strongest statements have been checked against the unmodified P1 `CountCone`, `OddCone`, `inverseAt`, and `UpperTail` definitions using Lean 4.36.0-rc2 and the repository's SHA-verified dependent sources. The P1 blank-root halting outcome and BB(6) remain **open**. External mathematical novelty has not been established, so every result remains in `im-results/`.

## Right-five five-reset floor (7 November 2026)

The source bridge now raises the right-five positive-reset floor from three to **five** for every `n>=14`. [ThreeResetWallPrefix.lean](../agent43-p1-high-cost-reset-count/ThreeResetWallPrefix.lean) proves the source theorem `source_right_five_five_reset_floor_shifted_wall` for the unmodified original `CountCone`:
`CountCone (14*2^n-2*n-16) 3 b 5 m z => 5<=z`.

Its key intermediate theorem, `source_no_three_reset_shifted_wall`, excludes a genuine three-positive-reset prefix on `b+4*m+4*n+20=12*2^n`. The proof peels the last two positive resets, eliminates depth-one cases by forcing negative predecessor right counters, and obtains the exact depth-two constants `c2+3=2P+18*m2+18*n+102` and `c1+3=2P+146*m2+146*n+816`. The remaining first reset is ruled out by the formal dyadic gap split `r=0,1,>=2` in [ThreeResetCore.lean](ThreeResetCore.lean).

**Verification:** original-source CI [42398746712](https://github.com/FlareZ123/bb6/actions/runs/42398746712) succeeded at head `55902afb482ea84aaddb93a688802facde679c98`. The source wrapper imports the existing original-source reset and depth modules, and the workflow compiles the new core and leaf theorem. The arithmetic core was also compiled locally with Lean 4.36.0-rc2; its explicit axiom report contains no `sorryAx`. Both new Lean files contain `#print axioms` commands for source-level auditing.

This result is a necessary source-history restriction. It does not bound the reset count above, close high-cost histories, prove blank-root reachability, or decide P1/BB(6). It remains in `im-results/` pending adversarial review and possible integration with stronger P1 exclusions.

## Strongest exceptional right-five result

Let `K(n) = 14*2^n-2*n-16`. The theorem [`BB6.Agent50RightFiveThree.source_right_five_needs_three_resets`](RightFiveThreeSource.lean) proves, with no cost or inverse-word-length cutoff,

```
n >= 14,
CountCone (K(n)) 3 b 5 m z
    => z >= 3.
```

Here `CountCone` counts exactly the genuinely positive-depth inverse transitions, with depth-zero stretches retained and arbitrary finite history length permitted. The right-five endpoint is the exceptional `c=1` inverse exit. This result **extends the pre-existing, independently certified Agent50 reset-density conclusion for `n>=70`** down to `n>=14`; it does not rule out arbitrary counts `z>=3`. [Earlier density proof](../agent50-p1-reset-density/README.md).

The proof is in three small source-auditable files:

1. [RightFiveResetFloor.lean](RightFiveResetFloor.lean): every right-five source history has at least two positive resets. A pure `UpperTail` from the right counter 3 cannot end at 5. The one-reset case contradicts the source last-reset depth/energy identities.
2. [RightFiveTwoArithmetic.lean](RightFiveTwoArithmetic.lean): a kernel-checked dyadic interval obstruction. When the first positive inverse follows no depth-zero steps, its required power falls strictly between `2C` and `4C`; if it follows at least one, it falls strictly between `4C` and `8C`. Both exclude the exact powers of two admitted by the original source.
3. [RightFiveThreeSource.lean](RightFiveThreeSource.lean): connects the forbidden dyadic intervals to the exact `z=2` source shape, using the original first-inversion `inverseAt_iff_power_mass` and an independently proved zero-tail mass invariant. The general exceptional depth theorem forces the final positive reset to depth `n+1`; a large preceding left counter forbids any later depth-zero inverse.

**Verification:** [manual original-source Lean CI run 42336144100](https://github.com/FlareZ123/bb6/actions/runs/42336144100) **succeeded**, at head `efdd21c68fd6fd7217b0146adc62db0a2683ea0d`. It compiled the exact original source chain and all three files. `#print axioms` for `source_right_five_needs_three_resets` reports `[propext, Classical.choice, Quot.sound]` only. The pure arithmetic gap has `[propext, Quot.sound]`. No `sorryAx`, mock imports, or `native_decide` occur in this source check. [Manual-only reproducible workflow](../../.github/workflows/agent50-p1-exceptional-last-reset-depth-source.yml).

## All-length mid-cost shallow-edge theorem (7 November)

The exact [RightFiveShallowSource.lean](RightFiveShallowSource.lean) theorem `BB6.Agent50Shallow.source_low_cost_right_five_has_shallow_edge` proves that every original-source `CountCone (14*2^n-2*n-16) 3 b 5 m z` with `n>=14` and `2*m+n+2<=5*2^n` contains a **genuine** previous source edge `inverseAt B D t = some (k,c)` where `t<=1`, embedded in a prefix `CountCone (14*2^n-2*n-16) 3 B D M Z`. The statement imposes **no reset count, word length, or maximum inverse depth bound**. It is a necessary low-cost restriction, not a right-five global exclusion.

The proof uses the source-preserving disjunction `source_shallow_or_all_deep`: each exact counted word either contains a `t<=1` edge or belongs to the genuine source-defined [DeepCone](RightFiveDeepCone.lean) where all inverse steps have depth `t>=2`. A universal strict defect invariant then rules out the right-five mid-cost end of an all-deep history. Define `P=2^n` and `W=b+4*m+4*n+20`. Every valid all-deep source prefix satisfies `W>12P`, while the unique final inverse at low exceptional right-five cost would require its immediate predecessor `W=12P`. The invariant is derived from **the original** inverseAt power and mass equations and is preserved without any limit on the number of steps.

The authentic `CountCone` disjunction and final low-cost shallow theorem were verified in **[manual original-source CI 42337286479](https://github.com/FlareZ123/bb6/actions/runs/42337286479)** at head `b02ee59d1c591629cf1255d1e1385556b2db36fe`; the all-deep source proof previously passed **[42336988993](https://github.com/FlareZ123/bb6/actions/runs/42336988993)**. Every printed axiom list contains at most `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`. This result is complementary to the all-cost `z>=3` theorem above and does not close the `t=0` or `t=1` routes.

## Universal shifted-defect gap and cost sieve (7 November)

The newest original-source theorem is a **general all-endpoint energy invariant** rather than a right-five-only numerical cost claim. Let `P=2^n`, `W=b+4*m+4*n+20`, and, for a chosen inverse-cost budget `M<=n`, define the positive integer buffer

```
threshold(n,M,m) = 16*(M+n+6)*(M-m+1)*2^(M-m).
```

[`BB6.Agent50EnergyParam.source_energy_budget_gap_param`](RightFiveEnergyParam.lean) proves for every `n>=14`, every `M<=n` satisfying `64*(n+2)^2*2^M<=P`, and **every original-source** `CountCone (14*P-2*n-16) 3 b d m z` with `m<=M`:

```
W > 12*P     OR     W + threshold(n,M,m) <= 12*P.
```

The strict gap is uniform in all inverse depths, right endpoints `d`, history lengths, and numbers `z` of true positive-depth resets. It is an exact structural source invariant; all counted cone branches are handled directly with no preselected transition sequence.

The key source-level identities for an actual original `inverseAt b d t = some(k,c)` and output cost `m+t+1` are

```
W + 2^(t+1)*(c+3) = 28*P,
W_after + (c+3) = 14*P + 2*(m+n+t+4).
```

At depths `t<=1`, modest-cost paths fall at least `P` below the `12P` wall. Every `t>=3` transition ends above it. A `t=2` transition satisfies the exact cocycle

```
8*W_after = W_before + 84*P + 16*(m+n+6),
```

so the dyadic buffer is preserved through arbitrary numbers of depth-two steps. The positive `threshold` makes equality at `W=12P` impossible throughout the stated cost range. See [RightFiveEnergyNumeric.lean](RightFiveEnergyNumeric.lean), [RightFiveEnergyStep.lean](RightFiveEnergyStep.lean), and the exact source induction [RightFiveEnergyCone.lean](RightFiveEnergyCone.lean).

**Verification:** manual [original-source CI run 42338373090](https://github.com/FlareZ123/bb6/actions/runs/42338373090) **SUCCESS** at head `3f67e90e348d1deee3a5a78c0b93345689689ad0`. The parametric theorem `source_energy_budget_gap_param`, its corollary `source_right_five_parametric_cost_gap`, and [`source_right_five_near_double_cost`](RightFiveNearDouble.lean) all print only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. [Earlier original-source run 42338039826](https://github.com/FlareZ123/bb6/actions/runs/42338039826) independently verified the simpler all-count cost floor `m>n+2+floor(n/2)` for `n>=128`, in [RightFiveCostGapSource.lean](RightFiveCostGapSource.lean).

**Numerical corollaries and priority:** If `n>=14, M<=n, 64*(n+2)^2*2^M<=P`, a right-five `CountCone` has `m>n+2+M`. More explicitly, if `2*k<=n` and `8*(n+2)<=2^k`, [RightFiveNearDouble.lean](RightFiveNearDouble.lean) yields `2*n+2-2*k<m`, a near-`2n-O(log n)` cost barrier. These numerical bounds are **weaker** than the earlier [Agent8 original-source theorem `2*n<=m+Nat.log2(n+1)`](../agent8-p1-fixed-reset/ExceptionalNearDoubleSource.lean), [CI 41837316502](https://github.com/FlareZ123/bb6/actions/runs/41837316502). Do not claim a record improvement. The independent all-endpoint forbidden-zone invariant and its elementary source proof are the main reusable contribution; their external mathematical novelty has not been reviewed.

## Earlier source-certified subwall results

The same source history, with arbitrary right endpoint `d`, has these necessary conditions:

| Hypotheses and domain | Certified conclusion | Source and original CI |
| --- | --- | --- |
| `n>=14, z>=1, m<=2^n, b<=4*(m+n+r)`, arbitrary `r>=0` | `2^(n+2*z)<=2^m*(m+n+r+3)` | [SubwallSource.lean](SubwallSource.lean); [42146998575](https://github.com/FlareZ123/bb6/actions/runs/42146998575) |
| `n>=42, z>=1, b<=4*(m+n+r)` | `2^n<=24^z*(n+2)^(2*z+1)*(n+r)` | [OffsetBudget.lean](OffsetBudget.lean); [42150387600](https://github.com/FlareZ123/bb6/actions/runs/42150387600) |
| `n>=148, b<=4*(m+n)`, all `z>=0` | `m>n+z` | [SubwallAllCount.lean](SubwallAllCount.lean); [42149985248](https://github.com/FlareZ123/bb6/actions/runs/42149985248) |
| `n>=14, OddCone(K(n),3,b,d,m), b<=4*(m+n)` | `2^(n-m)<n` | [SubwallLog.lean](SubwallLog.lean); [42148404771](https://github.com/FlareZ123/bb6/actions/runs/42148404771) |

The earlier uniform-width results generalize exact-wall costs but do not remove the high-cost case `m>2^n`. They are restrictions on source histories rather than blanket exclusions of even exit or the physical blank-tape orbit. See [Agent43's related cost bounds](../agent43-p1-high-cost-reset-count/README.md) and the [original P1 proof infrastructure](../agent28-p1-word-automaton/README.md).

## Exact last-reset shape across all costs

[ExceptionalLastResetDepthSource.lean](ExceptionalLastResetDepthSource.lean) proves that for every `n>=14, z>=1` with a right-five terminal, there exists a genuine predecessor history ending at `(bp,dp,mp,zp)` and an actual positive inverse `inverseAt bp dp t = some (k,1)` satisfying

```
z=zp+1,  m=mp+t+1,  2<=t<=n+1,
b=2*k-4,
k+m+n+7=7*2^n,
bp+2^(t+3)=4*k+4*t+12,
dp+14*2^n=2^(t+3)+2*mp+2*n+7.
```

Its extra inequalities, full cost bands, the four-integer gaps between adjacent depth bands, and the narrower mid-cost/two-depth classifications are recorded in the [historical derivation](RESEARCH_HISTORY.md). The all-cost theorem's proof was repaired by making the counted reset multiplication explicit; the complete dependency passed [original-source run 42336144100](https://github.com/FlareZ123/bb6/actions/runs/42336144100) with standard axioms only. In particular, any fixed total cost `m` admits at most one final positive-reset depth in these necessary bands.

## Quantified gap toward BB(6)

The new all-`n` three-reset floor gives no uniform upper bound on how many resets may occur, and cannot exclude the surviving `z>=3` source words. A source inverse `CountCone` witness also need not be a **genuine blank-origin forward** witness. A complete P1 decision requires closing every authentic exceptional right-five and even-exit branch, including unbounded source costs and counts, with a proved source-to-root connection or an actual halting trace. None of those quantified obligations is established here.

The most useful next direction is a uniform argument that constrains the `z>=3` exceptional prefixes by a persistent invariant that survives every positive reset, or a root-connected proof of the even-exit alternative. Additional finite prefix enumerations are validation aids, not substitutes for those quantifiers.

## Reproducibility and history

The [original-source CI workflow](../../.github/workflows/agent50-p1-exceptional-last-reset-depth-source.yml) verifies compressed source archives by SHA-256, builds unchanged dependency modules, imports the new leaf proofs, and audits the final theorem's axioms. The companion [subwall workflow](../../.github/workflows/agent50-p1-subwall-source.yml) checks the other source restrictions. All historical derivations, older statuses, supporting numerical bounds, and precise earlier CI revisions have been preserved in [RESEARCH_HISTORY.md](RESEARCH_HISTORY.md).
