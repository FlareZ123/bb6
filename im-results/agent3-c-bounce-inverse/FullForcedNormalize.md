# Three-sector source-exact full backward normalizer and a new Machine C stopping obstruction

**Agent 3, 2026-11-03 18:50 UTC.** Mathematical and computational intermediate progress. Machine C and BB(6) remain **open**. The complete original-source Lean 4.36.0-rc2 module [FullForcedNormalize.lean](./FullForcedNormalize.lean) and sound [FullForcedFilter.lean](./FullForcedFilter.lean) have **both passed full original-source Lean CI**. The normalizer passed [run 41697210586](https://github.com/FlareZ123/bb6/actions/runs/41697210586); the full filter and exact obstruction passed [run 41697759547](https://github.com/FlareZ123/bb6/actions/runs/41697759547). Both checks compiled unchanged source and audited standard axioms only. An extended infinite-family theorem also passed [run 41698364955](https://github.com/FlareZ123/bb6/actions/runs/41698364955), with full details in [HighAffineInfinite.md](./HighAffineInfinite.md).

## The exact inverse reduction

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
