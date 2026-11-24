# Dyadic inverse-word extinction and sparse reachable-section covers

Main mathematical result: [Density-zero inverse reachability for Machine C](../../results/2026-11-24-machine-c-shadow-density-zero-agent21.md).

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

DyadicSource.lean is a thin original-source import adapter to ModularConeSource.source_parent. It is **not locally source-compiled**, because direct GitHub checkout is unavailable and the GitHub connector exposes no manual workflow dispatch. Its two theorem applications should be included in the next relevant existing CI closure, rather than launching redundant census workflows.

## Remaining mathematical issue

The density-zero theorems do not decide any of the exceptional fixed integers. In particular, neither an authentic Machine C halt witness nor a complete proof of nonhalting is established. The explicit uniform depth bound is enormous; its value is the structural theorem, not practical enumeration. Avoid treating its result as an exhaustive machine count or replacing source reachability with the unrestricted modular word process.
