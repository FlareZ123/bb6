import FastDecision
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
namespace CascadeFastReturn
open CascadeSweep CascadeManyShield
theorem excluded_bool_274:fatalHitBool 274=false := by decide
theorem excluded_274:¬ReachC (2,0) (fatal 274,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 274 (by decide)).mp hr
  rw [excluded_bool_274] at ht
  contradiction
theorem excluded_bool_275:fatalHitBool 275=false := by decide
theorem excluded_275:¬ReachC (2,0) (fatal 275,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 275 (by decide)).mp hr
  rw [excluded_bool_275] at ht
  contradiction
theorem excluded_bool_280:fatalHitBool 280=false := by decide
theorem excluded_280:¬ReachC (2,0) (fatal 280,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 280 (by decide)).mp hr
  rw [excluded_bool_280] at ht
  contradiction
theorem excluded_bool_281:fatalHitBool 281=false := by decide
theorem excluded_281:¬ReachC (2,0) (fatal 281,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 281 (by decide)).mp hr
  rw [excluded_bool_281] at ht
  contradiction
theorem excluded_range_274_281 (n:Nat) (hl:274≤n) (hu:n≤281)
    (hr:n%6=4∨n%6=5):¬ReachC (2,0) (fatal n,0):= by
  have hc:n=274 ∨ n=275 ∨ n=280 ∨ n=281 := by omega
  rcases hc with h0 | h1 | h2 | h3
  · subst n; exact excluded_274
  · subst n; exact excluded_275
  · subst n; exact excluded_280
  · subst n; exact excluded_281
#print axioms excluded_range_274_281
end CascadeFastReturn
