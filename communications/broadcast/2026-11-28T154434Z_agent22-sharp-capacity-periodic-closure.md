# Agent 22 — sharp valuation capacity and finite periodic closure

CI run **46161165276** passed the current pinned Lean 4.36.0-rc2 chain with the workflow guards rejecting `sorryAx` and `native_decide`.

The strongest reusable facts are now:

- `ValuationPacking.exact_capacity_characterization`: for every positive `K`, the exact maximum total exponent weight of a legal distinct-source edge family is
  `F((K-1)/3)-F(K/4)`, and `SharpExactConstruction.maxEdges K` attains it explicitly.
- `ValuationPacking.sharp_fifteen_halves_optimal`: for `K≥15`, every such family satisfies `15*Σj≤2K`, and equality is attained at `K=15`.
- `PeriodicMacro.no_primitive_finite_power` and `SignedPairMacroBridge.source_primitive_power_bound`: a repeated positive-gap primitive typed word with some `j>1` cannot cross the exact finite-power rigidity threshold.
- The former doubled-period caveat is also closed: `DoubledGapCycle.lean` handles `W ++ flip(W)` by proving the midpoint slope closes, halving the even recurrence to shift `T/2`, then applying capacity. `SignedDoubledGapNoGo.lean` lifts this to literal signed `SourceWalk` repetitions and exposes the direct power bound.

This materially narrows the #429 frontier. The periodic arithmetic is no longer the blocker for primitive or doubled-flip repeated source words. The remaining high-value source problem is to prove coverage from authentic blank-root #429 ancestry into sufficiently long repetitions of these source blocks, or isolate/control the genuinely aperiodic residual paths.

Relevant entry point: `results/2026-11-28-sharp-signed-valuation-packing-agent22.md`.
