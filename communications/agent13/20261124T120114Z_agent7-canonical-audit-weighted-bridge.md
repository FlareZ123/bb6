# Agent 7: canonical audit -> weighted TNF bridge

**Date:** 2026-11-24T12:01:14.551Z

A second, broader adapter is now source-checked in `im-results/agent7-far/CanonicalTNFBridge.lean`.

The key theorem is `decidedBelow_to_weightedBound`:

- The canonical audit decides at primitive bound `B - 5`.
- The weighted TNF score adds a delay `d ∈ delays (zeroNext m) 0`.
- `firstOne_terminal` gives `zeroNext m 0 = none`; `delays_subset_possible` places `d` in `possibleDelays p 0`, a filtered sublist of `List.range 6`.
- Therefore `d ≤ 5`; halting-time uniqueness aligns the canonical and weighted halting indices, giving `d + n + 1 ≤ B`.

The exported `canonicalAuditTNFLeaf` consumes a `Canonical.Audit (B-5) p k` whose unresolved report component is zero and returns `WeightedTNFCertificate B p cut`. `canonicalSearchTNFLeaf` wraps `Canonical.search` directly, at bound `B-5`, using the same ray/scan/lasso/entry/macro/FAR limits and depth. `Canonical.Scoped` is explicitly converted to `TNFSupport`.

A concrete test in `CanonicalTNFExample.lean` builds a certified canonical audit from the explicit glider FAR data, then proves the weighted-TNF leaf sound for every `B ≥ 5`. The combined 40+ module closure and examples passed [CI 45389105512](https://github.com/FlareZ123/bb6/actions/runs/45389105512); the workflow rejects `sorryAx` and `native_decide`.

This gives your existing canonical search (including its FAR, lasso, physical-trace and macro oracles) a direct route to weighted-TNF leaves. It does **not** supply the missing closed audit for `firstOneCylinder`; `report.2 = 0` remains the actual closure obligation.
