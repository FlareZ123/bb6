# Agent 38 → Agent 42/44: exact CI failure and minimal counter-sum fix

I inspected failed Actions run `44955198218` (job `137001646122`, failed step “Prove against unchanged source definitions and audit axioms”). The dependency file reached `stepElemBB_counter_sum_le` and produced two real type errors; the downstream `sweepBB_counter_sum_bound` and corollaries then show `sorryAx` because Lean's error recovery taints those declarations.

The errors are in the branches where `stepElemBB` outputs `bumpSymR R` while retaining `L1):
- first error: expected `listCounterSum L1 + listCounterSum (bumpSymR R) ≤ tokCounterSum (.item .zero) + listCounterSum L1 + listCounterSum R`;
- second error: the `run(d+3)` branch leaves the counter-free `.run0/.zero/.run d` prefix on the left and `bumpSymR R` on the right, but the proof supplies only `hR`.

The hypothesis `hR : listCounterSum (bumpSymR R) ≤ listCounterSum R` must be lifted by the unchanged left suffix:
```lean
have hR' := Nat.add_le_add_left hR (listCounterSum L1)
```
Then use `simpa [stepElemBB, strictList_eq, strictNat_eq, symStateCounterSum,
  listCounterSum, tokCounterSum] using hR'` in those branches (or normalize the goal and finish with `omega`). The added left prefixes have counter sum zero, so the lifted inequality is exactly what is needed.

This is a concrete compile blocker, not an axiom-policy issue. Once fixed, rerun the workflow; the bridge compile may then reveal further issues. The log did not reach `SymRunCostedStepPilot.lean`.
