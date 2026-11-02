# Actual 25-way sparse-coverage proof tree: A/0 right drift, A/1 arbitrary

**Status:** source-certified *coverage machinery smoke test*, not an original BB(6) machine decision, not a new lower/upper bound, and not a globally complete enumerator. Prepared by Agent 4, 2026-11-02.

The existing Agent 8 `Frontier.lean` declares raw six-state, two-symbol tables with 12 state/read-symbol slots and exactly 25 possible actions per slot (24 ordinary actions plus a halt). A sparse node distinguishes an unassigned slot from a deliberately assigned halt. The inductive `Cover good p` is finite and permits branches only at genuinely unassigned slots, with proof terms for *every* child.

This folder's [`BranchSmoke.lean`](./BranchSmoke.lean) proves:

```lean
BB6Coverage.drift_twentyfive_way_tree (B : Nat) :
  Cover (DecidedBelow B) (driftLeaf true)
```

It constructs an **actual `Cover.branch`** at the otherwise-unassigned A/1 slot, supplies a `Cover.leaf` for each of all 25 `choices`, and discharges each leaf via the authentic `BB6Coverage.blankDrift_never` theorem from Agent8's unchanged `Prune.lean`. The parent table fixes A/0 to write 0, move R, return to A. Its blank run never reads A/1, so every possible setting of A/1 (and every assignment of the other ten entries) is nonhalting. The resulting source-level certificate uses a concrete branch and no metatheoretic assumption that all 25 cases were considered.

**Full original-source verification:** [manual CI run 41485353510](https://github.com/FlareZ123/bb6/actions/runs/41485353510), source commit `9b27760bf2da390a7987427ef4f66ec79e9dc665`, Lean 4.36.0-rc2. CI compiled original `Frontier.lean`, original `Prune.lean`, then `BranchSmoke.lean` through the *existing manually triggered* `.github/workflows/agent4-p1-cone2398.yml`. Final named theorem's axiom audit was **`[propext, Quot.sound]`**, no `sorryAx`, no mocked source, no `native_decide`. Locally a signature-compatible mock was used only to typecheck draft code; the verified CI proof uses entirely unmodified Agent8 modules.

The external 2026-11-02 Critic [coverage-integration direction](../../communications/broadcast/2026-11-02T1643Z_critic-unify-coverage-certificate-pipeline.md) asked for precisely such a concrete finite branch as a smoke test. This closes that **mechanical test** only. It is intentionally redundant with the simpler existing `driftLeaf_certificate`, so its significance lies in source-verified certificate *composition*. A final global `Cover (DecidedBelow B) emptyTable`, actual authenticated rooted holdout leaves, proof of all external normal-form enumerator reductions, a champion runtime and matched universal bound are still missing. In particular this result covers only the A/0=0RA cylinder and supplies zero additional real machine decisions.

Next valuable integration: consume one existing source-authentic rooted original-TM nonhalt/halt theorem as a `Cover` leaf, preserving its table, start state, full tape, and exact attempted-halt step convention; agree on a verified conversion between the independent Agent8 and Agent13 coverage representations.
