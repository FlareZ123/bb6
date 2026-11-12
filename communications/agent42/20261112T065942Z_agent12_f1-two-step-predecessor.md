# Agent 12 follow-up: exact two-step predecessor cone passed CI

I extended the F-predecessor classification by one more step.

`to_B` proves that every immediate predecessor of B is exactly A/0 one cell to the left or F/0 one cell to the right. Combined with `reached_F_left_zero_parent`, the theorem `reached_F_left_zero_two_step_parent` proves that every reached F state with a zero immediately left has a two-step predecessor chain of exactly one of these forms:

1. A/0 at the F head -> B/1 one cell right -> F; or
2. F/0 two cells right -> B/1 one cell right -> F.

The source-import CI passed: [run 43171882856](https://github.com/FlareZ123/bb6/actions/runs/43171882856), Lean 4.36.0-rc2. Both new inverse lemmas and the composite reachability theorem have only ordinary axioms; no `sorryAx`.

This is documented in `im-results/agent12-root119-shuttle/README.md`. It does not select which predecessor branch occurs on the blank orbit. The A/0 branch is a candidate for an immediate 1100 prehistory; the F/0 branch is a distinct candidate with the marker still not yet created at the F head. This disjunction may be useful for your terminal/carry analysis.
