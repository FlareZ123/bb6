# P1 inverse shadow: periodicity obstruction and root-code rigidity

**Research synthesis, 9 November 2026.** The original P1 scalar inverse shadow has exact edges

```text
z = 2^t v
2 z' + 1 = L + m + t + v
m' = m + t + 1.
```

For a root with `L ≥ 8`, `root > 0`, and `root + 4 ≤ L`, every genuine `ShadowReach` node preserves the four-unit margin. [SourcePeriodAllPeriods.lean](SourcePeriodAllPeriods.lean) proves that **no infinite source shadow path has an eventually periodic depth sequence**. This source theorem was kernel checked in [CI 42393598708](https://github.com/FlareZ123/bb6/actions/runs/42393598708). Genuinely aperiodic paths remain the outstanding single-root obstruction.

## New: inverse-depth coding is injective on effective initial states

Let two genuine infinite source histories `p₀`, `p₁` have arbitrary nonnegative source parameters `L₀,L₁`, initial costs `m₀,m₁`, and shadows `z₀,z₁`. Suppose their complete dyadic-depth sequences agree, and the first root satisfies the preceding four-unit margin. Then

```text
L₀ + m₀ = L₁ + m₁
z₀ = z₁.
```

**The input coded by the depth sequence is the effective parameter `X=L+m` together with `z`.** In particular, at equal initial cost, two distinct source `L` values cannot support the same infinite depth history, and two distinct initial shadow coordinates cannot either. The theorem is conditional on two infinite histories already existing. It neither constructs a history nor excludes one from a single fixed source root.

The unrestricted statement and proof are in [EffectiveCode.lean](EffectiveCode.lean), `infinite_shadow_effective_code_injective`; the equal-cost version is [RootCodeUnique.lean](RootCodeUnique.lean), `infinite_shadow_root_code_injective`. These extended Lean files have been locally checked against the exact previously established `InfiniteShadowPath` source theorem interface. Original-dependency CI for the latest extension has been blocked by repeated upstream HTTP 504 responses while installing Lean, before compilation. Earlier source checks of its crucial scaled-offset argument passed in [CI 42565628108](https://github.com/FlareZ123/bb6/actions/runs/42565628108). Do not cite the full unrestricted import as source-CI checked until a complete run passes.

### Exact proof mechanism

For synchronized depths `tₙ`, define integer differences

```text
C = (L₁ + m₁) - (L₀ + m₀),     Dₙ = z₁,ₙ - z₀,ₙ.
```

The difference in initial cost remains constant, so the exact source equations yield, for every n,

```text
Dₙ = 2^(tₙ) (2 Dₙ₊₁ - C).
```

If `C ≠ 0`, write `C=2^e B` with B odd, including negative B. Iterating the difference equation gives

```text
for every k, Dₙ = 2^k u + C v       for some integers u,v.
```

Thus `2^e` divides **every** `Dₙ`. Dividing by `2^e`, write `Eₙ=Dₙ/2^e`. Then

```text
Eₙ = 2^(tₙ) (2 Eₙ₊₁ - B).
```

For odd B the dyadic valuation of the right-hand odd factor determines the depth `tₙ` uniquely from `Eₙ`. The successor `Eₙ₊₁` is likewise unique. Moreover,

```text
|Eₙ₊₁| ≤ max(|Eₙ|, |B|)
```

for every edge. Consequently the `Eₙ` sequence lives in a finite interval and eventually repeats a state. Its deterministic depth sequence becomes eventually periodic, contradicting the original source margin theorem. Therefore `C=0`. The remaining recurrence `Dₙ=2^(tₙ+1)Dₙ₊₁` implies `2^k ∣ D₀` for every k, hence `D₀=0`.

This is a **cross-history comparison theorem**, applying to arbitrary aperiodic depth sequences. It gives no uniform single-history bound on total inverse cost.

### The original P1 feeder roots

The original P1 feeders are

```text
side 0: (L,z)=(16q+8,12q+4)
side 1: (L,z)=(16q+9,10q+4).
```

For arbitrary q₀ and q₁, an infinite common depth sequence from opposite sides is impossible by the odd-offset case alone, as proved in [CrossFeederAll.lean](CrossFeederAll.lean) and source-checked in [CI 42564547994](https://github.com/FlareZ123/bb6/actions/runs/42564547994). Combining this with Agent 13's same-side 2-adic parameter separation [PrefixCylinder.lean](../agent13-p1-adaptive-param/PrefixCylinder.lean) gives the full original-feeder encoding theorem `infinite_feeder_code_unique` in [FeederCoding.lean](FeederCoding.lean), source-checked in [CI 42564771450](https://github.com/FlareZ123/bb6/actions/runs/42564771450).

For two feeder roots sharing the **same q** and a finite exact depth word `w`, its total dyadic cost `M=cost w` and binary marker `H=weight w` satisfy

```text
H ≡ 2q (mod 2^M).
```

If the word is nonempty, its highest marker bit forces `2^(M-1) ≤ 2q`. This finite restriction is [FeederDisjoint.lean](FeederDisjoint.lean) and was source-checked in the same 42564547994 audit.

## Proof modules and auditable milestones

- [PeriodCore.lean](PeriodCore.lean), [PeriodWord.lean](PeriodWord.lean), [PeriodFactorization.lean](PeriodFactorization.lean), [PeriodAllPeriods.lean](PeriodAllPeriods.lean): exact affine finite-word recurrence, binary-marker period factorization and no fixed positive-depth periodic infinite ray. Source certification: [42392999355](https://github.com/FlareZ123/bb6/actions/runs/42392999355).
- [SourcePeriodAllPeriods.lean](SourcePeriodAllPeriods.lean): original-source margin, full eventually periodic depth exclusion, exact varying-depth recentered prefix identity, and zero-run gap bounds. Source certification: [42393598708](https://github.com/FlareZ123/bb6/actions/runs/42393598708) and [42404496047](https://github.com/FlareZ123/bb6/actions/runs/42404496047).
- [OddDifference.lean](OddDifference.lean), [CrossFeederAll.lean](CrossFeederAll.lean), [FeederDisjoint.lean](FeederDisjoint.lean): odd-difference bounded deterministic dynamics, opposite-feeder disjointness, and finite same-q marker restriction. Source certification: [42564547994](https://github.com/FlareZ123/bb6/actions/runs/42564547994).
- [OddParameterSource.lean](OddParameterSource.lean): arbitrary source L pairs of odd difference. Source certification: [42565066761](https://github.com/FlareZ123/bb6/actions/runs/42565066761).
- [OddRescale.lean](OddRescale.lean), [ScaledParameterSource.lean](ScaledParameterSource.lean): arbitrary dyadic-scaled odd difference with source theorem. Source certification: [42565628108](https://github.com/FlareZ123/bb6/actions/runs/42565628108).
- [Factor2.lean](Factor2.lean), [DistinctParameterSource.lean](DistinctParameterSource.lean), [ZeroOffset.lean](ZeroOffset.lean), [RootCodeUnique.lean](RootCodeUnique.lean), [EffectiveCode.lean](EffectiveCode.lean): all integer offsets including zero, and effective initial-state injectivity. Local Lean 4.36.0-rc2 interface proofs; complete source import pending infrastructure recovery.
- [.github/workflows/agent9-cross-feeder-source.yml](../../.github/workflows/agent9-cross-feeder-source.yml): manually dispatched, original-source compiler and axiom audit (fail closed).

## Relation to other work and remaining BB(6) gap

Agent 13's [PrefixCylinder.lean](../agent13-p1-adaptive-param/PrefixCylinder.lean) previously proved uniqueness of the parameter within each separate P1 feeder family. The cross-family theorem adds disjointness of those languages; the generic theorem identifies the effective scalar source state coded by a depth stream. The periodicity obstruction still holds for each source root individually.

For varying depths, [SourcePeriodAllPeriods.lean](SourcePeriodAllPeriods.lean) also kernel-checks the exact recentered identity

```text
2^Mₙ Rₙ = R₀ + Σ_{i<n} 2^Mᵢ (m₀ + Mᵢ + L - 2),
Rₙ = 2zₙ - mₙ - L + 2,    Mₙ = Σ_{i<n}(tᵢ+1).
```

The urgent open task remains **exclude every infinite aperiodic inverse path from at least one authentic P1 feeder root, or exhibit an actual blank-machine halting witness**. Pairwise coding uniqueness alone cannot decide a single root, P1, or BB(6). This dossier contains intermediate research rather than an independently established publishable frontier decision. External priority review of the new comparison theorem remains to be done.
