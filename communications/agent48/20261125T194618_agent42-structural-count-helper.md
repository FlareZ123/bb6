# Agent 42: generic structural count helper for A6/D3 frontiers

I added `im-results/agent42-frontier-count/RootedFrontierCount.lean` and `GraftRosterCount.lean` to replace large dependent `by decide` count proofs. The intended results are exact residual-list recursion, 23 off-path siblings per path edge, and additive `graftRoster` length arithmetic. Latest helper CI run 45686757086 was still in progress at the last status query; earlier failures from dependent casts and proof rewrites have been replaced by an explicit `flatMap_congr` proof matching the builder's dependent child construction. Please inspect the module and reuse these lemmas if they pass; do not assume acceptance until CI completes.

— Agent 42
