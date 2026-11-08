# P1: counted inverse-history energy, walls and one-shallow obstructions

**Research synthesis, 8 November 2026.** These are mathematical restrictions on P1's inverse histories. The new one-shallow theorem is now verified for legal **unchanged-source `inverseAt` transitions**, for every critical index n≥14 and arbitrarily long depth-two blocks. This is a source-word exclusion, with no unrestricted blank-root decision or BB(6) solution. Agent50's all-count reset-density theorem remains the strongest general quantitative result; additional bounded-reset floors have lower priority.

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

## Original-source certified infinite word exclusion: one shallow edge between depth-two runs

The complete new mathematical note is [TwoRunWallExclusion.md](TwoRunWallExclusion.md). It derives an affine invariant for the exact original-source **depth-two scalar equations**:

```
P=2^n, W=b+4m+4n+20, B=m+n+6
8 W' = W+84P+16B,  B'=B+3
I=49W-588P-112B+384,    I_before=8*I_after.
```

For every `n>=14` and all nonnegative lengths `s,r`, the exact shifted wall is impossible for the original-source legal inverse-depth words `(2)^s (0|1) (2)^r` from the critical root. The proof is source-certified through [SourceOneShallowLift.lean](SourceOneShallowLift.lean), original-source [successful CI 42530146731](https://github.com/FlareZ123/bb6/actions/runs/42530146731). The precise `q,p,d` divisibility premises, both exact natural equations and complete proof are in [OneShallowFiniteBridge.lean](OneShallowFiniteBridge.lean). The stronger root-only model theorems [no_scalar_zero_word_wall_from_root](OneShallowModelBridge.lean) and [no_scalar_one_word_wall_from_root](OneShallowModelOne.lean) formally derive the dyadic quotient conditions from [RootTwoDivisor.lean](RootTwoDivisor.lean) and need only an exact initial two-run, the corresponding shallow scalar step, an exact final two-run, and the wall endpoint. Every link was locally compiled with Lean4.36.0-rc2; public theorem audits contain only ordinary axioms, no `sorryAx`. The proof uses a symbolic cubic gap for `n>=28` ([OneShallowLarge.lean](OneShallowLarge.lean)) and a fully kernel-decided finite scan for `14<=n<=27` ([OneShallowFinite.lean](OneShallowFinite.lean)). The direct-root single-shallow special case has separate unbounded-run proofs in [TwoRunBridge.lean](TwoRunBridge.lean).

**Source integration and scope:** [SourceOneShallowLift.lean](SourceOneShallowLift.lean) constructs `SourceTwoChain` from actual unchanged-source `inverseAt` steps with exact legal side conditions (`b>=8`, `b%4=0`, odd right counter and output, `k>=2`). It proves conservation of the original root mass, transfers every depth-two step using the [original two-step cocycle](../agent50-p1-subwall/RightFiveEnergyStep.lean), derives the exact depth-zero/one equations from [original inverse characterization](../agent1-p1-quarter/InverseIff.lean), then invokes the model wall contradictions. Theorems `BB6.Agent43SourceWord.source_no_zero_word_wall` and `source_no_one_word_wall` compiled with original sources in [CI 42530146731](https://github.com/FlareZ123/bb6/actions/runs/42530146731), each with axiom list `[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**. A separate `CountCone` membership/word-shape characterization remains optional formal integration; the theorem itself already uses true `inverseAt` at every edge. This is an infinite legal-word restriction, not a blank-root P1 decision or an established externally novel publishable result. Keep it under `im-results/`.

## New source-certified two-shallow words for all n>=48

[SourceOneShallowLift.lean](SourceOneShallowLift.lean) now also proves the theorem
`BB6.Agent43SourceWord.source_no_two_shallow_word_wall_large`: for **every n>=48** and every **legal unchanged-original-source `inverseAt`** depth word
`(2)^s (0|1) (2)^u (0|1) (2)^r`, with s,u,r arbitrary nonnegative lengths, no endpoint on the exact shifted wall `b+4*m+4*n+20=12*2^n` exists. The theorem simultaneously covers four combinations of the two shallow types and uses the exact mass, parity and bound premises on each genuine source step. The successful original-source [CI run 42532957359](https://github.com/FlareZ123/bb6/actions/runs/42532957359) verifies the complete import chain; `#print axioms` is `[propext, Classical.choice, Quot.sound]`, **without `sorryAx`**.

The arithmetic proof splits into [TwoLayerRemainder.lean](TwoLayerRemainder.lean), [TwoShallowNumeric.lean](TwoShallowNumeric.lean), and [TwoShallowModelLarge.lean](TwoShallowModelLarge.lean). A first positive residue below a dyadic power forces a bounded middle run; a second residual after division forces a bounded last run. Both powers then contradict the all-n `8400000*(n+2)^3<2^n` bound, itself proved for n>=48. This is source-certified progress on an infinite word family, **not** a complete blank-origin P1 decision and not yet a publishable BB(6) theorem. The finite range n14..47 for this two-shallow grammar and words with more than two shallows or high depths remain open.

## Finite right-five search and remaining frontier

[Right-five endpoint enumeration](right_five_finite_search.md) and its [exact search script](right_five_finite_search.py) use source `inverseAt_iff_power_mass` equations and a strictly decreasing two-counter mass to exhaust each fixed-`n` inverse tree when no state cap is reached. Completed runs found no right-five hit for `n=14..1612` and `n=1616..2620`; `n=1614` and `n=2622` remained incomplete at their state limits. These are finite computational observations only.

A reproducible [two-shallow scalar-model scan](two_shallow_model_scan.py), independently run for every n=14..4000, tested 6,708 integral scalar transitions through words of form `2^s(0|1)2^u(0|1)2^r` and encountered no exact-wall hit. This is bounded numerical evidence, not an all-n theorem or an original-source audit. The new two-shallow theorem closes the n>=48 sector for exactly two shallow transitions. The remaining next steps are the finite n14..47 sector, three or more shallow transitions, and unrestricted high-depth excursions. The true blank-origin path, exceptional exits and any global six-state maximum certificate remain unresolved. Broader proof history and superseded paper variants are preserved in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).
