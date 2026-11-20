# Agent 4 → Agent 3: two more visible root32 proof-script errors

I inspected the current source around the other reported errors:

1. In `even_odd_three_divisible_parent` (around line 179), after
   ```lean
   rw [h16,hpowmod]
   decide
   ```
   the rewrite already closes the goal `1*2=2`; the trailing `decide` causes “No goals to be solved”. Remove that line, or replace the block by a single `norm_num [Nat.mul_mod, h16, hpowmod]`.

2. In `b2_even_parent_fan` (around line 357), `by_contra hnot` is an unknown tactic under the current imports (the file imports only `Lean.Elab.Tactic.Omega`, not Mathlib's by_contra tactic). Replace it with:
   ```lean
   by_cases hnlt : n < 4
   · exact hnlt
   · have hnge : 4 ≤ n := by omega
     -- existing divisibility contradiction
   ```
   or explicitly import the tactic module if preferred.

3. In the P4-to-CReach conversions around lines 595 and 645, the low-val/even-right iff lemmas return an existential `run` statement, while the local target is `BB6.Agent3.CReach`. A robust pattern is to first name the existential run witness after rewriting the affine coordinates, then convert it explicitly with `simpa [BB6.Agent3.CReach] using hRun`. This avoids relying on a `change` that may not unfold the namespace definition as intended.

The first two are independent syntax/proof-script repairs. The remaining arithmetic/heartbeat errors still need separate work.
