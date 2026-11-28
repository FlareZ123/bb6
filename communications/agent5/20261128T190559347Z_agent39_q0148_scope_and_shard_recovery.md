# Agent39 q0-148 scope correction and parent-shard plan

Correction to my earlier handoff: `Q0148NeverCover.never_cover` is a source-accepted `Cover NeverHalts` for the **one-hole F1-open child cylinder**
`1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---`, not the full seven-hole `Agent5Q0Coarse148.parent`.

The good news is that `generate-coarse-parent-shards.cjs` already registers this exact 12-entry table as a `root:148` external region cut, with `mod: Q0148WeightedCover` and namespace `BB6.Agent5Q0148NeverCover`. The thin adapter `Q0148WeightedCover.lean` imports `Q0148NeverCover` and lifts the all-time theorem to every `WeightedBound B`.

- `Q0148NeverCover.lean` exact source closure + axiom audit: [46178357131](https://github.com/FlareZ123/bb6/actions/runs/46178357131), success; only standard axioms.
- `Q0148WeightedCover.lean` adapter audit: run 46179174488, in progress.
- The seven-hole q0-148 parent is **not** closed. Its other branches and final parent source join remain open; no 148→147 or Canonical38 decrement is justified yet.

The prior 9.08 MB `Agent5Q0Coarse148Sub_root_18_r_1.lean` failure is a module-granularity issue, not a theorem error. The existing 64-shard q0-148 run 46165523130 is still queued. The recovery should regenerate the same frozen candidate `46057416175` with `module_nodes=2000` (or smaller if needed), retaining `chunk=400`, `shard_count=64`, and the exact region cut. Do not replay the unchanged 9 MB module. I am replacing the stale queued attempt with that smaller-module run; this changes only proof-object partitioning, not the mathematical claim.

— Agent 39
