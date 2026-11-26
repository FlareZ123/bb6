# Raw59: complete source-certified weighted parent Cover

The six-hole Raw59 cylinder (E1=1LA), exact table `1RB---_1RC---_0RD---_1LD1RE_---1LA_------`, has a certified weighted upper bound of **4,200,000**, including all compatible halting completions.

Lean 4.36.0-rc2 source acceptance: [CI 45784817773](https://github.com/FlareZ123/bb6/actions/runs/45784817773), source revision `4cd61999e0e5677c8283239545169e6d2634d372`, artifact `raw59-parent-certified` ID 15100037790, SHA256 `505c7a43fd21abe58f539b7d6119ac956d2a3466ae5ccd7607dca67c4173c595`. The strict merger validates 13 producer shard manifests and 1891 unique dependency-closed modules, then compiles the parent partition, closed branches and complete parent proof with the ordinary axiom gate.

```lean
BB6.Agent32Raw59UpgradeAll.cover :
  Cover (WeightedBound 4200000) BB6.Agent32Raw59.p59
BB6.Agent32Raw59UpgradeAll.bound :
  ∀ m, compatible BB6.Agent32Raw59.p59 m → WeightedBound 4200000 m
```

The final child 0LA passed in [45781689877](https://github.com/FlareZ123/bb6/actions/runs/45781689877); the parent join in that run failed only on an empty-list membership simplification. The assembly-only retry consumes all accepted artifacts, no recomputed machine classification. Long finite traces in that child are checked with the packed sweep/bridge proof machinery and exact primitive cost transport; see [the detailed dossier](../im-results/agent32-raw59/Upgrade.md) and [Raw59ParentCover.lean](../im-results/agent32-raw59/Raw59ParentCover.lean).

The bound is below the accepted champion score floor 6,766,859, so this certificate can discharge the Raw59 obligation in the coordinated direct-from-Canonical64 parent batch, subject to exact roster membership and integrated composition. No new global roster count or global BB(6) upper bound is claimed here.
