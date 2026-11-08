# P1: counted inverse-history energy, walls and one-shallow obstructions

**Research synthesis, 8 November 2026.** These are mathematical restrictions on P1's inverse histories. The genuine original-source results are explicitly separated from the new, fully Lean-checked **source-shaped arithmetic model**. Neither a P1 blank-start halting decision nor an exact value of BB(6) follows. The strongest new all-count reset-density theorem is by Agent50; further bounded-reset floor work has lower priority.

## Strongest genuine original-source deductions

**Unrestricted reset energy.** [CountedEnergySource.lean](CountedEnergySource.lean) and [CountedEnergyCostSource.lean](CountedEnergyCostSource.lean) certify for every original critical counted inverse history with `n>=14` the upper energy bound

```
m <= n+1+(2*n+3)*z
```

where `m` is total inverse cost and `z` counts genuinely positive-depth resets. It covers arbitrary zero-depth interludes. [Original-source CI 42122986713](https://github.com/FlareZ123/bb6/actions/runs/42122986713) and [42123746362](https://github.com/FlareZ123/bb6/actions/runs/42123746362).

**Small-left wall cost exclusion.** [CountedWall148Source.lean](CountedWall148Source.lean) proves that for `n>=148` a genuine source history on `b=4*(m+n)` must have `n+z<m`, for every reset count and every zero-depth tail. [Original-source CI 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876). Agent50 independently proved the stronger half-plane generalization for `b<=4*(m+n)`, in [SubwallAllCount.lean](../agent50-p1-subwall/SubwallAllCount.lean), original-source [CI 42149985248](https://github.com/FlareZ123/bb6/actions/runs/42149985248). The historical derivations in [WallAboveNPlusZ.md](WallAboveNPlusZ.md) are superseded by these source certificates.

**Exceptional right-five dichotomy and reset floors.** [DepthIndexedResetFloor.lean](DepthIndexedResetFloor.lean) certifies a full original-source dichotomy: a genuine history ending at right counter five either has `3*2^n <= (2*n+3)*z`, or its last positive reset has exactly depth `n+1` and its genuine predecessor lies on the shifted wall `W=b+4m+4n+20=12*2^n`. The predecessor's exact inverse, endpoint, mass and cost equations are provided in the theorem. [CI 42353729728](https://github.com/FlareZ123/bb6/actions/runs/42353729728). [ThreeResetWallPrefix.lean](ThreeResetWallPrefix.lean) excludes every genuine original-source three-positive-reset exact-wall precursor for `n>=14`, yielding the right-five floor `z>=5`, source [CI 42398746712](https://github.com/FlareZ123/bb6/actions/runs/42398746712). The speculative source wrapper [FourResetWallPrefix.lean](FourResetWallPrefix.lean) has **not** passed a full original-source CI (run [42439169870](https://github.com/FlareZ123/bb6/actions/runs/42439169870) failed); its separate arithmetic core has passed local Lean. Do not cite a source-certified six-reset floor based on that wrapper.

**Stronger later result by Agent50.** The genuinely source-certified all-count theorem in [WallLogSourceCorollaries.lean](../agent50-p1-subwall/WallLogSourceCorollaries.lean), [CI 42520350507](https://github.com/FlareZ123/bb6/actions/runs/42520350507), proves for every right-five original history and every `n>=14`:

```
n < 3*z+2*Nat.log2(n)+11.
```

This has no cost or history-length cutoff and asymptotically dominates any fixed reset floor. Its underlying source theorem prohibits the exact or near shifted wall unless `2^n<32*(2*n+7+(2*n+3)*z)*8^z`. It is still a necessary reset-density restriction and leaves arbitrarily many resets open.

## New full-range arithmetic obstruction: one shallow edge between arbitrary depth-two runs

The complete new mathematical note is [TwoRunWallExclusion.md](TwoRunWallExclusion.md). It derives an affine invariant for the exact original-source **depth-two scalar equations**:

```
P=2^n, W=b+4m+4n+20, B=m+n+6
8 W' = W+84P+16B,  B'=B+3
I=49W-588P-112B+384,    I_before=8*I_after.
```

For any `n>=14` and any two unbounded lengths `s,r`, the wall equations for the inverse-depth grammar `(2)^s (0|1) (2)^r` from the critical root are **arithmetically impossible**. The precise `q,p,d` divisibility premises, both exact natural equations and complete proof are in [OneShallowFiniteBridge.lean](OneShallowFiniteBridge.lean). The stronger root-only model theorems [no_scalar_zero_word_wall_from_root](OneShallowModelBridge.lean) and [no_scalar_one_word_wall_from_root](OneShallowModelOne.lean) formally derive the dyadic quotient conditions from [RootTwoDivisor.lean](RootTwoDivisor.lean) and need only an exact initial two-run, the corresponding shallow scalar step, an exact final two-run, and the wall endpoint. Every link was locally compiled with Lean4.36.0-rc2; public theorem audits contain only ordinary axioms, no `sorryAx`. The proof uses a symbolic cubic gap for `n>=28` ([OneShallowLarge.lean](OneShallowLarge.lean)) and a fully kernel-decided finite scan for `14<=n<=27` ([OneShallowFinite.lean](OneShallowFinite.lean)). The direct-root single-shallow special case has separate unbounded-run proofs in [TwoRunBridge.lean](TwoRunBridge.lean).

**Essential limitation:** the new restricted-word conclusion is proved against a separately defined exact recurrence and natural arithmetic consequences, **not yet as a `CountCone` theorem from the unchanged original source**. The scalar equations match the existing original-source [two-step and general energy lemmas](../agent50-p1-subwall/RightFiveEnergyStep.lean); formally transferring an original `inverseAt` history to those equations is the remaining source-lift. This is an informative exact infinite-word exclusion, not an authentic blank-root P1 decision, and its external novelty has not been established. Keep this in `im-results/`.

## Finite right-five search and remaining frontier

[Right-five endpoint enumeration](right_five_finite_search.md) and its [exact search script](right_five_finite_search.py) use source `inverseAt_iff_power_mass` equations and a strictly decreasing two-counter mass to exhaust each fixed-`n` inverse tree when no state cap is reached. Completed runs found no right-five hit for `n=14..1612` and `n=1616..2620`; `n=1614` and `n=2622` remained incomplete at their state limits. These are finite computational observations only.

A reproducible [two-shallow scalar-model scan](two_shallow_model_scan.py), independently run for every n=14..4000, tested 6,708 integral scalar transitions through words of form `2^s(0|1)2^u(0|1)2^r` and encountered no exact-wall hit. This is bounded numerical evidence, not an all-n theorem or an original-source audit. The most valuable next step is to source-integrate the new one-shallow word restriction and extend to words containing **multiple shallow transitions** and all high-depth excursions. The true blank-origin path, exceptional exits and any global six-state maximum certificate remain unresolved. Broader proof history and superseded paper variants are preserved in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).
