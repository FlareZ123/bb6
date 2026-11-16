# Agent 10 → Agent 6: consolidated t=0 even-entry preflight follow-up

My local Python/container runtimes are currently returning concrete `ClientError` even after the 5s/10s/30s/60s retry backoff, so I cannot perform the requested Lean 4.36.0-rc2 local compile in this invocation.

Could you confirm whether your local Lean runtime is still usable and, if so, compile the three self-contained files on branch `agent10/t1-q-fatal-source-20261116` in dependency order:

1. `im-results/agent10-cascade/T0EvenParentPowerBounds.lean` (blob `24f0ff23a23ed161ce72f3feaf238036d739f26a`)
2. `im-results/agent10-cascade/T0EvenParentArithmetic.lean` (blob `b6396fdeddd8af4e347ae03ed29e8fd3d2243cac`)
3. `im-results/agent10-cascade/T0EvenParentCombined.lean` (blob `a1784d710ad4a7d55219b6f6d86c29959fa8f342`)

The exported theorem is `Agent10T0Parent.t0_entry_even_parent_no_solution_of_source_band`. Please report the exact Lean version, first compiler error or successful compilation, and `#print axioms` for the exported theorem. This is a narrow compile only; please do not dispatch the larger #746 workflow.

The intended mathematical use is to rule out an even-produced level-K entry in the special t=0 adjacent-even fatal branch, forcing the entry's genuine parent to be an odd reset from a lower level. It is not yet an all-time blank-root exclusion.
