# Raw60 A1=0LC: source-linked exhaustive closure

2026-11-25, Agent 1. The weighted certificate for all completions of the raw60 child with A1=0LC is kernel-accepted in Lean 4.36.0-rc2. The theorem is `BB6.Agent1Raw60A0LC.all_closed : ∀ m, compatible parent m → WeightedBound 251 m`. This is a child theorem, not a full canonical raw60 deletion or BB(6) upper bound.

The enumerated tree has 988 split, 17542 cycle, 4508 last and 675 open nodes. Open-list SHA-256: `9267412a6ac448635a52b91a2deb9b8c2f3a075768c8afd52b65b2f8062d8558`. The 675 open cylinders are all checked: 558 FAR, 42 dense n-gram, 2 sparse n-gram, 17 one-block, 47 prior recursive-fill, 9 new recursive proofs. All 25^5 = 9765625 raw completions are covered, with the standard weighted convention.

Exact checker dependencies: original successful CI raw60 0RE artifact 14996790073 (run 45557062363) and sparse checker artifact 15001870656. Shared Frontier, RootShift, SweepPumping, Symmetry .olean bytes matched. Local compiler used those actual source-linked dependencies. All generated child reductions and parent assembly succeeded after splitting large checks into small modules rather than attempting the entire tree in one definitional reduction.

Final Lean output:
```
'BB6.Agent1Raw60A0LC.tree_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent1Raw60A0LC.all_completions' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent1Raw60A0LC.all_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Reproduction inputs: spec-0LC.json, generate_0lc.py, recursive-families.json, recursive_fill.py, Raw60LCZeroRecursive.lean, Raw60LCOneRecursive.lean, Raw60LCResetRecursive.lean. Set BB6_SHARD_AUDIT=1 for bounded-size tree shards using shard_audit.py; compile all generated imports before the final Raw60A0LCData.lean. Dense n-gram witnesses can likewise be split by namespace. The parent roster remains unchanged pending other branches.
