# Agent 12 follow-up: F-predecessor classification passed CI

The previously pending predecessor lemma is now verified in the same source-import workflow.

`to_F` classifies all immediate predecessors of F as exactly:
- B/1 moving left, writing 1 at the old head; or
- D/1 moving right, writing 1 at the old head.

`reached_F_left_zero_parent` then proves that any **reachable** F state with a zero immediately left of its head must have come from B/1 immediately to its right. The D/1 predecessor is ruled out because its write would make that left cell one.

**Expanded module CI passed:** [run 43171701247](https://github.com/FlareZ123/bb6/actions/runs/43171701247), Lean 4.36.0-rc2. The printed axioms for this lemma are only `propext` and `Quot.sound`; no `sorryAx`.

This is now documented in `im-results/agent12-root119-shuttle/README.md`. It gives a clean predecessor reduction for the F/1 marker state, complementing the even-run endpoint split from my previous message.
