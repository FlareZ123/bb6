# Agent 12: exact SymRun source-gate diagnosis

I attempted the required local RC2 preflight once. Both `container.exec` and `python.exec` returned tool-level `ClientError` before executing any command; no local compiler was run. Per the Critic direction, I am not substituting CI or retrying unchanged setup commands.

I retrieved the failed-job log for run 44955198218 (job 137001646122). The two actual Lean errors are both in `stepElemBB_counter_sum_le`:

1. In the `.item (.run 1)` branch, the proof ends with `exact hR`, but `hR : listCounterSum (bumpSymR R) ≤ listCounterSum R` omits the unchanged left suffix. The goal also contains `listCounterSum L1` on both sides.
2. The same mismatch occurs in the `.item (.run 2)` branch.

The current-main source still has these two bare `exact hR` lines at 1426 and 1431. The `.zero` and `run >= 4` branches already use the correct left-lifted form.

Suggested minimal repair in each failing branch:

```lean
have hR' := Nat.add_le_add_left hR (listCounterSum L1)
simp [stepElemBB, strictList_eq, symStateCounterSum, listCounterSum, tokCounterSum]
omega
```

The `omega` step has the missing run-counter slack (1 for run1, 2 for run2); `hR'` transports the bump inequality with the untouched suffix. This is a proof-script correction, not a counterexample to the symbolic transition.

The reported `sorryAx` in `sweepBB_counter_sum_bound` is downstream: the failed `stepElemBB_counter_sum_le` declaration is elaborated with a placeholder after the errors, and `sweepBB_counter_sum_bound` depends on it. There is no literal `sorry`/`admit` in the current `SymRunTraceStats.lean`. Repairing the two source branches should remove this particular placeholder dependency, but only a fresh exact-source RC2 compile and transitive axiom audit can establish that.

I have not edited or promoted the file because the mandated local preflight surface is unavailable. Please apply the two-line repair and run the exact pinned-source preflight when a working RC2 runtime is available; do not dispatch the manual source audit until that succeeds.

— Agent 12