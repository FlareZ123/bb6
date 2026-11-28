# Dyadic inverse-word extinction and sparse reachable-section covers

Main mathematical result: [Density-zero inverse reachability for Machine C](../../results/2026-11-24-machine-c-shadow-density-zero-agent21.md).

## Source-certified original Machine C dependency closure

Original-source Lean 4.36.0-rc2 CI [46102569750](https://github.com/FlareZ123/bb6/actions/runs/46102569750) compiled **80 project modules**, including the unchanged CReach source parent law and complete inverse-word extinction proof. The declarations `source_all_rows_sparse`, `source_low_sparse`, and `source_high_sparse` each report exactly `[propext, Classical.choice, Quot.sound]` without `sorryAx`.

`DyadicRays.lean` extends the source-independent result from rows to rays `(x+2*a*t,y+(2*b+1)*t)` via affine slopes `sigma=-2*(a+2*b+1)` and `lambda=-a`. The new `source_ray_sparse` adapter is **not yet source-certified**; do not conflate it with the accepted 80-module build.

## Locally kernel-accepted dependency order

Compile with Lean 4.36.0-rc2 from this directory, setting LEAN_PATH to the directory:

```sh
export LEAN_PATH="$PWD"
for f in DyadicAffine DyadicCollision DyadicAmplification DyadicPopulation DyadicExtinction DyadicReach DyadicCover DyadicStops DyadicRows; do
  lean -o "$f.olean" "$f.lean" || exit 1
done
```

- DyadicAffine: affine unrolled numerator, odd-slope congruence, concatenation and normalization.
- DyadicCollision: equal-mass four-bit collision, arbitrary-depth synchronization and uniform steering.
- DyadicAmplification: uniform existence of arbitrarily many distinct compatible words at one binary cylinder.
- DyadicPopulation: complete and pending inverse words, exact step validity, supermean inequality and uniform population amplification. Includes the weaker Admissible initial condition, sigma even and lambda+sigma/2 odd.
- DyadicExtinction: elementary finite-tree stopped counting and arbitrary small live-cylinder fraction, at a uniform depth.
- DyadicReach: direct reachability-to-open-cylinder theorem assuming the complete parent law, with height propagation and exact valuations.
- DyadicCover: sparse residue list, uniform across every admissible affine root.
- DyadicStops: source-conditional sparse covers of the entire low and high stop families.
- DyadicRows: source-conditional sparse cover for every fixed left counter of the complete reachable section lattice; modulus and height cutoff uniform in the counter.

All listed modules compiled locally; final declarations report standard axioms only. Commits f9fe811b6a676137c0f10dfef7ab25c2bca1a6ae, b421c58af25803ba84380092d956979df732fcd2 and 79bc4d367ee04abf3c24d3978fa2ca7cac8edc3c. Source-level conditionality is exactly one premise: ParentLaw, definitionally the same proposition as Agent42's ModularCone.ParentLaw.

DyadicSource.lean connects the abstract parent law to `ModularConeSource.source_parent`. The row, low-stop, and high-stop corollaries are original-source certified by CI 46102569750. The newer even/odd ray corollary remains under separate compile review. The existing manual workflow `.github/workflows/agent21-low1875-source.yml` accepts input `target: dyadic-density` for this source closure.

## Remaining mathematical issue

**Interpretive correction:** The low/high *stopping-family* sparsity corollaries are correct but do not meaningfully restrict whether the deterministic blank-origin orbit halts: such an orbit can encounter at most one terminal section configuration, so its truly reached stopping family is already finite. The nontrivial structural content is uniform sparsity of the full reachable section relation across every fixed-left row (and, if accepted, across all even-left/odd-right rays). None excludes a particular stopping witness.

The density-zero theorems do not decide any of the exceptional fixed integers. In particular, neither an authentic Machine C halt witness nor a complete proof of nonhalting is established. The explicit uniform depth bound is enormous; its value is the structural theorem, not practical enumeration. Avoid treating its result as an exhaustive machine count or replacing source reachability with the unrestricted modular word process.

## New modular-cone / inverse-word duality research (NOT YET ACCEPTED)

The source-independent finite inverse-word predicate `OpenAt` and Agent42's executable `ModularCone.excluded` appear to be exact Boolean complements on the same signed coordinate pair, at **every** dyadic bit precision. Independent exhaustive checks agree for all signed residue pairs at b=2,...,6 and four high-stop families at b=8. See the mathematically complete but not yet Lean-certified induction in [FiniteDualityProofCandidate.md](FiniteDualityProofCandidate.md), and precise finite checks plus limitations in [FiniteDuality.md](FiniteDuality.md).

A full Lean proof **candidate** of `check_open_duality` and `excluded_open_duality` is written in [DyadicCheckerDuality.lean](DyadicCheckerDuality.lean). Its dependencies include `DyadicOpenRecurrence.lean` (two-sided completed/pending inverse-word decomposition), `DyadicExactGaps.lean`, `DyadicSignedPeriod.lean`, `DyadicResidueOpen.lean`, `DyadicSignedGap.lean`, `DyadicValuation.lean`, `DyadicAllowedHigh.lean`, `DyadicHighEdge.lean`, `DyadicBad.lean` and `DyadicFuel.lean`. **None of these new duality modules has a successful full closure build yet, so none may be claimed as kernel-certified.**

[DyadicCheckerDensity.lean](DyadicCheckerDensity.lean) contains the intended major payoff: combining the exact duality with the accepted uniform extinction theorem would establish that the **existing executable modular-cone algorithm** excludes at least a fraction `1−1/d` of candidate section states along **every** even-left/odd-right affine ray, using one universal bit precision for any `d>0`. This is a structural density theorem about *all candidate residues*, not the trivial density of a deterministic run's terminal states, and **does not solve any remaining particular halting question**.

Manual CI workflow `.github/workflows/agent21-low1875-source.yml` has targets `dyadic-density`, `dyadic-gap`, and `dyadic-duality` for source modules. As of 03:56 UTC 28 November 2026, repair runs 46104561076, 46104564006 and exploratory duality run 46104772927 are queued. Exact proof acceptance is contingent on their logs and later closure builds of `DyadicCheckerDuality` and `DyadicCheckerDensity`; do not infer correctness from a queued dispatch.

