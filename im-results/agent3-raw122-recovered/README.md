# Raw122: two new full-child Covers

The F1=1LA (index 12) and F1=1RF (index 23) ordinary-transition cylinders now have unconditional, original-source Lean 4.36.0-rc2 weighted bounds of **7014**, and empty residual lists. The preceding Agent43/29 work supplied all 24 checked child objects for each cylinder in successful individual jobs of runs [45702209290](https://github.com/FlareZ123/bb6/actions/runs/45702209290) and [45734681632](https://github.com/FlareZ123/bb6/actions/runs/45734681632). The latter run failed overall due to other branches; only its successful artifacts are used.

- `BB6.Agent3Raw122Recovered12.cover12` and `branch12_empty`, source [Raw122Recovered12.lean](Raw122Recovered12.lean), SHA-256 `4b616221bf5bb57c54093234c3d8ebd7c5b1e294f267ab5f07fb9089a1ae2212`.
- `BB6.Agent3Raw122Recovered23.cover23` and `branch23_empty`, source [Raw122Recovered23.lean](Raw122Recovered23.lean), SHA-256 `b2b2a10457fe96e507439a5f03c9d47b608bef8e54d7618f8cc5a6c28e309715`.

Each branch's root theorem and the two wrapper exports were freshly compiled locally on 2026-11-26 at 03:43Z, with original pinned objects. All four wrapper exports print exactly [propext, Classical.choice, Quot.sound]. Both groups have no unresolved leaves, including the formerly open tables grafted by the prior agents. The two proofs account for 2 × 25^5 = 19,531,250 additional disjoint literal completions of Raw122. Together with the prior 16/24 separately accepted ordinary F1 children, 18/24 are independently bounded. The remaining six are indices 0,4,5,13,16,17 (0LA,0LE,0LF,1LB,1LE,1LF). This is not yet the fully composed parent Cover.

## Reproduction

Download the original source and core archives plus successful shard ZIPs pinned by [pins.json](pins.json), naming each `github-actions-artifact-ID.zip`. Run `python recover.py ARTIFACT_DIRECTORY WORK_DIRECTORY 12 23` with Lean 4.36.0-rc2. This only elaborates the two branch wrappers, reuses all checked subtrees, and rejects conflicting objects or artifact hashes. No repeated witness search.

The final parent must include the larger late-query bound in F1=0LF and F1=1LE. Use Agent43's `Raw122RootCompose.root_bound` once all 24 covers are available.
