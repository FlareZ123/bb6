# Four-sector source-exact full backward normalizer and a new Machine C stopping obstruction


## Current four-sector status (2026-11-07)

**Agent 3, 2026-11-07.** The 2026-11-03 three-sector normalizer has been extended with Agent 24's complete six-residue even-right inverse from [EvenRightSixOrbit.lean](../agent24-c48/EvenRightSixOrbit.lean).

The added gate is
```
6 ≤ y
y % 2 = 0
(x+y) % 8 ≠ 0
(x+y) % 8 ≠ 7
```
and its exact source predecessor is `(x+y-2, (y-2)/2)`, with weighted mass `x+2*y` dropping by four. The previous `evenAffineGate` remains earlier in the branch order: for even `y≥6` it is contained in the new gate, while it also handles `y=4`, which the six-residue theorem does not cover. The current `fullForcedNormalize` therefore applies four exact source sectors, and `blank_reach_iff_fullForcedNormalize` proves the all-natural exact reachability equivalence.

The updated [original-source workflow](../../.github/workflows/agent3-c-bounce-inverse.yml) passed targeted run [42366675885](https://github.com/FlareZ123/bb6/actions/runs/42366675885) at commit `ed3619f5a08ada2b9387ca34ed905be1dd9690cb`. It compiled the current four-sector `FullForcedNormalize.lean` and `FullForcedFilter.lean` against the original source modules. The workflow now has a `forced_normalize_only` input so this dependency closure can be checked without running unrelated downstream experiments.

A local Lean 4.36.0-rc2 exact-integer comparison over `3≤m≤35`, `0≤j<256` (8,448 high stopping inputs) gives:
- previous three-sector filter: **3,208** excluded;
- current four-sector filter: **4,517** excluded;
- additional exclusions from the six-residue branch: **1,309**.

[FullForcedCompare.lean](./FullForcedCompare.lean) records this finite comparison, imports the current `FullForcedFilter`, and retains the old three-sector implementation as the baseline. Its regression guards were checked locally against a matching Lean interface stub; the source-importing CI check for this comparison file is pending. These counts are finite experimental evidence only. The universal result is the source-proved soundness theorem `fullForcedExcluded_sound`, which applies to every target where the Boolean returns true.

`HighEvenRightC23FullForcedResidual.lean` now composes the full-forced filter with the exact C70+C23+all-phase+even-right high residual. It proves a refined exact blank-halting equivalence and scans the bounded existing high candidate set for genuinely additional exclusions. Original-source CI run [42369065708](https://github.com/FlareZ123/bb6/actions/runs/42369065708) is verifying the repaired integration. A preceding diagnostic run [42368349091](https://github.com/FlareZ123/bb6/actions/runs/42368349091) computed 22,081 Boolean-accepted candidates in the domain j=0..2000, m=0..20, with 3,100 additional full-forced exclusions and 18,981 remaining. However, its Boolean/Prop equivalence proof had an unsolved propositional goal and consequently printed `sorryAx`; treat these counts as provisional until the repaired equivalence and rerun are source-certified. The theorem `sum7_family_subset_c23_gate` also proves that the sum-seven family is already contained in the C23 gate, so it is an independent cross-check rather than another exclusion to count. Separately, the Agent 4 modular proof-pattern correction compiles locally, and the exact `blank_halts_iff_c23_and_even_right` theorem printed standard axioms in the prior source run. However, the high-even-right `prior_allowed` and `genuinely_new` side lemmas still print `sorryAx`, inherited through the earlier high-sieve proof chain. Do not treat the claim that this family survives every prior sieve as established until those upstream axiom dependencies are removed or audited.

## Historical three-sector result (2026-11-03)

**Agent 3, 2026-11-03 18:50 UTC.** Mathematical and computational intermediate progress. Machine C and BB(6) remain **open**. The complete original-source Lean 4.36.0-rc2 module [FullForcedNormalize.lean](./FullForcedNormalize.lean) and sound [FullForcedFilter.lean](./FullForcedFilter.lean) have **both passed full original-source Lean CI**. The normalizer passed [run 41697210586](https://github.com/FlareZ123/bb6/actions/runs/41697210586); the full filter and exact obstruction passed [run 41697759547](https://github.com/FlareZ123/bb6/actions/runs/41697759547). Both checks compiled unchanged source and audited standard axioms only. An extended infinite-family theorem also passed [run 41698364955](https://github.com/FlareZ123/bb6/actions/runs/41698364955), with full details in [HighAffineInfinite.md](./HighAffineInfinite.md).

## Historical three-sector inverse reduction

Building on the [two-sector source-certified backward normalizer](./OddForcedNormalize.md), `fullForcedNormalize x y` recursively applies a third **exact** source predecessor, in addition to two existing forced regions:

| Target predicate | Genuine forced parent | Exact weighted-mass drop |
| --- | --- | --- |
| odd/odd, y≥5, sum≥24, sum%4=0, sum%16≠0 | ((x+y−4)/2, (x+3y−10)/4) | 7 |
| even/odd, y≥5, sum≥23, (sum+1)%16=8 | ((x+y−5)/2, (x+3y−9)/4) | 7 |
| y even≥4, (x+y)%4=1 | (x+y−2, (y−2)/2) | 4 |

The third predecessor is the unmodified Agent 15 [`blank_reach_iff_affine`](../agent15-c-halting/ReachAffine.lean), itself based on original Machine C source [`SectionAffineInverse`](../agent15-c-halting/SectionAffineInverse.lean).

All inverse steps **strictly decrease the natural rank** `x+2*y`. Lean proves the recursive function terminates by this rank, with no arbitrary simulation fuel, then proves for **all** natural x,y the exact original blank orbit equivalence

```
(∃n, run secNext n (some (5,1)) = some (x,y))
  ↔
(∃n, run secNext n (some (5,1)) =
     some (fullForcedNormalize x y)).
```

The converse direction is important: each forced parent is a **genuine exact original-section edge**. Thus this is a semantics-preserving normalization rather than a speculative inverse search. It is a partial reduction: any residual outside the forced branches may still be reachable.

## Sound computable all-time exclusion

[FullForcedFilter.lean](./FullForcedFilter.lean) implements a total, fully executable Boolean `fullForcedExcluded x y`. It returns true if the normalized residual has odd second counter≥5 and total sum congruent to 1 or 2 modulo 4. From the original-source `blank_section_odd_image` invariant, the theorem `fullForcedExcluded_sound` establishes for **every** natural x,y:

```
fullForcedExcluded x y = true
  ⇒ ∀time, run secNext time (some (5,1)) ≠ some (x,y).
```

The source contains a kernel-checked `decide +kernel` proof `high_m6_j93_exact_excluded` of all-time genuine blank nonreachability for `(189,1572748)`, which is an actual high-stopping input with `j=93,m=6`:

```
1572748 + 93 + 3*6 + 5 = 2^(2*6+2)*(93+3).
```

For this exact input, the three forced inverse branches are **affine → odd/odd → even/odd**, giving the residual **(1081329,1032169)**. Its right counter is odd and at least five; the sum is **2 mod4**. This is a source-structural, unbounded proof obligation, independent of the behavior or soundness of a finite abstract quotient.

## Comparative sample and new target-admitted cases

The original CLine B8/M32 experimental graph was independently reconstructed with **31,570** reached abstract states and **189,834** edges. Exhaustive parameter enumeration **3≤m≤35, 0≤j<256** produced 8,448 high-stopping inputs; a separately coded exact-integer implementation of the full normalizer was compared with that finite graph. Of the targets abstract-reachable in B8/M32, the previous two-sector filter excludes **40**, while the three-sector filter excludes **56**. The 16 additional cases have a chain of three forced inverses **affine → odd/odd → even/odd** and occupy **four distinct target abstract cells**, all present in B8/M32. Example `m=6,j=93` occupies abstract target **(29,12,0)** and normalizes to forbidden state, yet target membership alone in that finite abstraction is inconclusive.

All 16 sample cases satisfy `m%4=2` and `(j+127*m)%128=87` (equivalently `j−m≡87 mod128`). This is a **promising hypothesis for a new infinite parametric obstruction**, requiring a separately constructed Lean theorem to establish the guard chain and stopping-equation arithmetic uniformly. The sample is limited; the existing full normalizer theorem by itself does not prove this residue condition for all parameters. The previous two-sector high families have distinct residues.

The finite graph itself is not part of either soundness proof and the comparison is computational evidence of improved discrimination, not external novelty proof. Do not promote it to `results/` without review.

## Verification and next actions

The manual-only `.github/workflows/agent3-c-bounce-inverse.yml` now builds the actual unchanged [Agent46](../agent46-c-jump/FastSectionDef.lean), [Agent3CImage](../agent3-c-odd-image/Agent3CImage.lean), [Agent15 SectionAffineInverse](../agent15-c-halting/SectionAffineInverse.lean) and [ReachAffine](../agent15-c-halting/ReachAffine.lean) source modules. It compiles every inversion theorem and prints axiom dependencies. **The final full filter, exact high-stopping obstruction, and uniform infinite-family theorem have now passed original-source CI**, all with standard Lean axioms. They remain intermediate scientific progress; Machine C and BB(6) are undecided. The earlier two-sector source CI [41696352388](https://github.com/FlareZ123/bb6/actions/runs/41696352388) **succeeded** with only standard axioms.

The mathematically productive next priority is a uniform exact Lean proof of the candidate infinite `m≡2 (mod4), j−m≡87 (mod128)` stopping family using the three forced inverses, then an adversarial novelty audit against Agent43's M32 and Agent41's mixed96 holdout sets. Wider extension to additional source-exact affine and dyadic predecessor regions may further shrink the stopping locus.

## New audit of the infinite-family hypothesis

The previously conjectured family has been proved in [HighAffineInfinite.lean](./HighAffineInfinite.lean), with [full original-source CI success 41698364955](https://github.com/FlareZ123/bb6/actions/runs/41698364955). The follow-up [mixed96 quotient comparison](./HighAffineInfinite.md#independent-mixed96-reachability-audit-2026-11-03-agent-3-successor) found **all twelve projected target abstract cells reachable in the finite quotient**, validating that this source-exact inverse proof can exclude targets which the mixed96 direct-nonmembership test cannot. This comparison is finite computational evidence and says nothing about actual blank reachability of those twelve abstract cells.
