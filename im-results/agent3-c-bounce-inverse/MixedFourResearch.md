# Machine C: exact four-sector inverse normalization and sharp incoming ancestry

**Agent 3, 2026-11-05. Intermediate original-source mathematical research, not a six-state Busy Beaver decision.**

## Authentic source and definitions

The section map is the original `BB6.Agent46.secNext : (Nat × Nat) → Option (Nat × Nat)`, as defined using the original recursive `bounce` interpreter in `im-results/agent46-c-jump/FastSectionDef.lean`. The physical blank tape is connected to initial section `(5,1)` by the existing original-source `CReachBridge`; we use `BB6.Agent3.CReach x y := ∃t, run secNext t (some (5,1))=some(x,y)`.

The function `mixedFourNormalize x y` in [MixedFourNormalize.lean](MixedFourNormalize.lean) takes every available *exactly unique* predecessor, and halts in the first configuration with none of the following four forced-parent gates:

| Output sector, with all listed height restrictions | Unique predecessor |
|---|---|
| `x%2=y%2=1`, `y≥5`, `(x+y)%4=0`, `(x+y)%16≠0`, `x+y≥24` | `((x+y-4)/2,(x+3y-10)/4)` |
| `x%2=0,y%2=1,y≥5`, `(x+y+1)%16=8`, `x+y≥23` | `((x+y-5)/2,(x+3y-9)/4)` |
| `y≥4` even, `(x+y)%4=1` | `(x+y-2,(y-2)/2)` |
| `y≥6` even, `(x+y)%8∉{0,7}` (Agent24) | `(x+y-2,(y-2)/2)` |

The first two branches strictly decrease weighted mass `x+2y` by 7; the latter two decrease it by 4, establishing termination without an external cutoff. All identities are original-source *iff* theorems, including complete exclusion of any other predecessor in the stated gates.

## Original-source exact consequences

1. **Blank-root reachability invariance**: `mixedFourNormalize_reach_iff`, for every natural x,y, establishes `CReach x y ↔ CReach p.1 p.2`, where `p=mixedFourNormalize x y`. [Source CI 42087619849](https://github.com/FlareZ123/bb6/actions/runs/42087619849).
2. **Exact arbitrary-start canonical chain**: [MixedUniversalAncestry.lean](MixedUniversalAncestry.lean) proves that for every target x,y there exists a finite `d` such that the source transition run from `p` to target in exactly `d` steps is real, and *every* path of length `t+d` from *any* starting pair that reaches target must have visited `p` at time `t`. This is substantially stronger than blank-specific reachability equivalence. [Source CI 42089069740](https://github.com/FlareZ123/bb6/actions/runs/42089069740).
3. **Sharp terminal-root ancestry**: [MixedUniversalSharp.lean](MixedUniversalSharp.lean) proves that if `p.2≥5` is odd and `(p.1+p.2)%4∈{1,2}`, then target's maximal possible incoming path from *any starting pair* has length exactly `d`; no arbitrary-start path of length `d+1` exists, but the real `d`-edge witness above does. [Source CI 42089069740](https://github.com/FlareZ123/bb6/actions/runs/42089069740).
4. **Sharp A/B cone ancestry**: [MixedUniversalAB.lean](MixedUniversalAB.lean) composes an arbitrary forced four-sector prefix of length `d` with the source-certified two-edge A/B rectangles at terminal normalizer `p=(16u+3,32v+16)` or `p=(16u+11,32v+32)`. Then there is a real path of length `d+2` to target, but no path of length `d+3` from any start, and the genuine blank origin never reaches target. [Source CI 42090697247](https://github.com/FlareZ123/bb6/actions/runs/42090697247).
5. **Executable root exclusion**: [MixedFourFilter.lean](MixedFourFilter.lean) provides sound Boolean `mixedFourExcluded` and proof `mixedFourExcluded_sound`. The old three-gate and new four-gate versions are tested empirically in [mixed_high_census.py](mixed_high_census.py): among the 15,872 **finite sampled** high stopping parameter pairs `m=1..31`, `j=0..511`, the prior three-gate filter excludes 6,015 while the four-gate filter excludes 8,488, i.e. 2,473 additional. These counts depend on the stated finite sample and are **not** infinite mathematical claims.

Every theorem in items 1–4 has a **successful unchanged-source Lean 4.36.0-rc2** verification. The displayed `#print axioms` for each named theorem contains only `[propext, Classical.choice, Quot.sound]`. There are no `sorry`, `sorryAx`, `native_decide`, source-definition substitutions, finite recursion cutoffs or custom proof postulates in the certified lemmas. Warning-only Lean deprecations are immaterial.

## New unbounded stopping-parameter obstructions

The unchanged source supplies the exact high stopping equation
`k+j+3m+5=2^(2m+2)*(j+3)`, with stopping pair `(2j+3,k)`.

[MixedHighBoth.lean](MixedHighBoth.lean) proves that for **every** `j,m,k` with `m≥4` and this equation, if either

* `m%4=0` and `(j+m)%32=26`; or
* `m%4=1` and `(j+m)%32=2`,

then this pair is a *genuine immediate stopping input* yet cannot ever appear on the blank section orbit. It has a sharp maximal incoming ancestry of exactly two steps even from arbitrary other starting pairs, as [MixedHighSharp.lean](MixedHighSharp.lean) proves. [MixedHighOne.lean](MixedHighOne.lean) covers the `m=1,j=32q+1` family of stopping pairs `(64q+5,480q+55)`, also absent from the authentic blank run.

For the broad `m≥4` pair the first exact parent is
`((2j+3+k-4)/2,(2j+3+3k-10)/4)`. The second exact parent is
`(a1+k1-2,(k1-2)/2)`. Parameter congruences force the latter to have odd right counter ≥5 and sum residue 1 mod4, incompatible with the source-verified section-image invariant. This gives a uniform symbolic certificate without a computed stopping-time bound. [Source CI 42088330957](https://github.com/FlareZ123/bb6/actions/runs/42088330957).

The two `m≥4` classes have `j%4=2` and `j%4=1` respectively, disjoint from Agent24's first original-source high `j%4=3` barrier. The latter class is also disjoint from Agent24's newer high condition `j%4=1,(j+3m+11)%32=0`, since our condition implies `j+3m+11≡2m+13≡7 (mod8)` for `m%4=1`. Novelty versus *all* previous quotient and symbolic exclusions requires a broader literature/repository overlap review.

The [MixedHighResidual.lean](MixedHighResidual.lean) exact original-blank halting iff removes these infinite high classes from the source's complete two-family halting criterion. This is fully original-source verified by [Lean CI 42092097733](https://github.com/FlareZ123/bb6/actions/runs/42092097733), with standard axioms only.

## Reachability algorithm integration and remaining obligation

[MixedFastRoot.lean](MixedFastRoot.lean) source-certifiably composes `mixedFourNormalize` with Agent11's exact bounded `backwardFastFuel` section-root oracle, using normalized weighted mass as the fuel instead of the unnormalized target. Its original-source verification [CI 42092097733](https://github.com/FlareZ123/bb6/actions/runs/42092097733) succeeded with only standard Lean axioms. It is a fixed-target decision; its correctness for each fixed pair does not imply a uniform decision for the infinite stopping families.

The primary open obligation is to prove that **no** state from *either entire source-authentic infinite stopping family* can be reached from blank, or exhibit an actual reached stopping state. Further finite residue classes are insufficient by themselves, and other unresolved BB(6) machines and the universal step bound remain separate. This work is preserved in `im-results/` accordingly.

## Additional low- and high-sector obstructions under source verification (2026-11-05 19:27 UTC)

The general [MixedEvenEightSharp.lean](MixedEvenEightSharp.lean) is a candidate source theorem: if `x%4=1`, `y%8=0`, and `y≥16`, then `secNext(x+y-2,(y-2)/2)=some(x,y)` is a real and **unique** incoming edge, but **no** other arbitrary-start path of two or more steps enters that target. The parent has odd right counter ≥7 and coordinate sum 2 modulo 4, contradicting the authenticated section-image restriction. The result also implies true blank-root nonreachability.

In [MixedLowFour.lean](MixedLowFour.lean) and [MixedLowFourSharp.lean](MixedLowFourSharp.lean), this yields a whole low-family stopping-index class `m%8=4`: `(1,k)` with `k+3m+4=2^(2m+3)` stops immediately, never occurs from blank, has a real one-step incoming edge from some other start, and has no arbitrary-start incoming path of two or more steps.

In [MixedHighEightSharp.lean](MixedHighEightSharp.lean), the same two-dimensional obstruction gives a disjoint high-family cylinder: `m≥2`, `j%2=1`, `(j+3m+5)%8=0`, and `k+j+3m+5=2^(2m+2)*(j+3)`. Then `(2j+3,k)` stops and has maximal arbitrary-start incoming path length precisely 1; it is absent from the true blank section. The modular assumptions force `k%8=0` and `(2j+3)%4=1`. Example `m=2,j=5,k=496` gives target `(13,496)`, whose authentic unique parent is `(507,247)`, forbidden by the original odd-image invariant.

The [MixedFullResidual.lean](MixedFullResidual.lean) and [MixedThreeHighResidual.lean](MixedThreeHighResidual.lean) candidate source theorems consume these broad low and high cylinders into exact original-blank stopping equivalences. As of this writing, **these newer declarations remain pending Lean verification**. Earlier failed runs were caused by a transparent natural-number expression mismatch `1+k-2` versus `k-1`, now explicitly addressed in source with `simpa only [CReach,hx]`. Do not cite this section as kernel established until a successful original-source CI result appears. The current manual workflow is `.github/workflows/agent3-c-bounce-inverse.yml`, invoked with `mixed_only:true`.
