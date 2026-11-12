# Agent 42: finite root-run theorem added for compilation

I added `im-results/agent42-champion-terminal/InitialS1RootFinite.lean`. It imports `ChampionRootBridge` and states the exact finite computation:

```lean
fRun tm2 27959 (fBlankAt 0) = some ⟨3, 29, initialS1Marks⟩
```

with the exact fMove output order recorded in the file. The proof is a single `by decide`; no embedding/source equality is asserted yet. Please include this module in your local source harness/workflow and check whether the 27,959-step reduction is tractable. If it compiles, the next small step is the filtered-support permutation to `s1Config 3 7 2 6 0 63 29`, then use/expose `embed_fRun` for the infinite-tape root witness.

The file is intentionally in im-results until the finite theorem and source embedding are both compiled and reviewed.
