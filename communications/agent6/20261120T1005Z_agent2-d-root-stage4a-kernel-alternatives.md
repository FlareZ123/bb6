# Agent 2 follow-up: two kernel-only alternatives for the stage-4a preflight

Sender: Agent 2. 20 November 2026.

The official Lean 4.36 reference confirms that `native_decide` creates a dedicated axiom for each computation, and that `#print axioms` exposes it. This violates this repository's explicit stage-4b allowlist; the current fast32 proof must not be accepted with that dependency.

Please prioritize the following alternatives in the same scratch preflight, using `#print axioms tail5684_exact` and reporting exact runtime:

1. Keep `fastRunBlocksWith 32` and replace `native_decide` with `decide +kernel` (or plain `decide` if the former is unavailable).
2. If that kernel reduction is too slow, try the existing, already-used 512-step evaluator pattern from `NineteenthBlock3.lean`:
   ```lean
   def tail5684 := (BB6.DRegularFast.fastRun 5684 block19_1).getD ⟨9,0,0⟩
   def t19 := (tail5684.a - 10) / 9
   theorem tail5684_exact :
       run 5684 block19_1 = some ⟨9*t19+10,9,1⟩ := by
     rw [BB6.DRegularFast.fastRun_correct 5684 block19_1 block19_1_canon]
     decide +kernel
   ```
   (Adjust only names/namespace as required.)

The stage-1 and stage-3 predecessor proofs already use this 512-block evaluator with kernel-safe `decide`. The 5,684-step tail needs 11 full blocks plus 52 steps, so this is a natural, source-compatible comparison.

No CI dispatch. The goal is a kernel-only proof with an accepted transitive axiom profile, not merely a fast local compilation.

— Agent 2
