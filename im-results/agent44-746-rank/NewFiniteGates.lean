import FastDecision
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
namespace CascadeFastReturn
open CascadeSweep CascadeManyShield

theorem no_257_bool : fatalHitBool 257 = false := by decide
theorem no_262_bool : fatalHitBool 262 = false := by decide
theorem no_263_bool : fatalHitBool 263 = false := by decide
theorem no_268_bool : fatalHitBool 268 = false := by decide
theorem no_269_bool : fatalHitBool 269 = false := by decide

theorem no_fatal_257 (hr : ReachC (2,0) (fatal 257,0)) : False := by
  have ht := (root_fatal_iff_fatalHitBool 257 (by decide)).mp hr
  rw [no_257_bool] at ht
  contradiction

theorem no_fatal_262 (hr : ReachC (2,0) (fatal 262,0)) : False := by
  have ht := (root_fatal_iff_fatalHitBool 262 (by decide)).mp hr
  rw [no_262_bool] at ht
  contradiction

theorem no_fatal_263 (hr : ReachC (2,0) (fatal 263,0)) : False := by
  have ht := (root_fatal_iff_fatalHitBool 263 (by decide)).mp hr
  rw [no_263_bool] at ht
  contradiction

theorem no_fatal_268 (hr : ReachC (2,0) (fatal 268,0)) : False := by
  have ht := (root_fatal_iff_fatalHitBool 268 (by decide)).mp hr
  rw [no_268_bool] at ht
  contradiction

theorem no_fatal_269 (hr : ReachC (2,0) (fatal 269,0)) : False := by
  have ht := (root_fatal_iff_fatalHitBool 269 (by decide)).mp hr
  rw [no_269_bool] at ht
  contradiction

/-- Five newly source-root-excluded fatal candidates just above the old
    n<=256 certified frontier. -/
theorem fatal_unreachable_257_to_269 (n : Nat)
  (hn : 257≤n) (hhi : n≤269) (hres : n%6=4 ∨ n%6=5) :
  ¬ ReachC (2,0) (fatal n,0) := by
  have hcases : n=257 ∨ n=262 ∨ n=263 ∨ n=268 ∨ n=269 := by omega
  rcases hcases with h | h | h | h | h
  · subst n; exact no_fatal_257
  · subst n; exact no_fatal_262
  · subst n; exact no_fatal_263
  · subst n; exact no_fatal_268
  · subst n; exact no_fatal_269

#print axioms fatal_unreachable_257_to_269
end CascadeFastReturn
