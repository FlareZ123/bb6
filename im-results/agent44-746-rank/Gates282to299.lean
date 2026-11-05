import FastDecision
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
namespace CascadeFastReturn
open CascadeSweep CascadeManyShield
theorem excluded_bool_286:fatalHitBool 286=false := by decide
theorem excluded_286:¬ReachC (2,0) (fatal 286,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 286 (by decide)).mp hr
  rw [excluded_bool_286] at ht
  contradiction
theorem excluded_bool_287:fatalHitBool 287=false := by decide
theorem excluded_287:¬ReachC (2,0) (fatal 287,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 287 (by decide)).mp hr
  rw [excluded_bool_287] at ht
  contradiction
theorem excluded_bool_292:fatalHitBool 292=false := by decide
theorem excluded_292:¬ReachC (2,0) (fatal 292,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 292 (by decide)).mp hr
  rw [excluded_bool_292] at ht
  contradiction
theorem excluded_bool_293:fatalHitBool 293=false := by decide
theorem excluded_293:¬ReachC (2,0) (fatal 293,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 293 (by decide)).mp hr
  rw [excluded_bool_293] at ht
  contradiction
theorem excluded_bool_298:fatalHitBool 298=false := by decide
theorem excluded_298:¬ReachC (2,0) (fatal 298,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 298 (by decide)).mp hr
  rw [excluded_bool_298] at ht
  contradiction
theorem excluded_bool_299:fatalHitBool 299=false := by decide
theorem excluded_299:¬ReachC (2,0) (fatal 299,0) := by
  intro hr
  have ht := (root_fatal_iff_fatalHitBool 299 (by decide)).mp hr
  rw [excluded_bool_299] at ht
  contradiction
theorem excluded_range_286_299 (n:Nat) (hl:286≤n) (hu:n≤299)
    (hr:n%6=4∨n%6=5):¬ReachC (2,0) (fatal n,0):= by
  have hc:n=286 ∨ n=287 ∨ n=292 ∨ n=293 ∨ n=298 ∨ n=299 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · subst n; exact excluded_286
  · subst n; exact excluded_287
  · subst n; exact excluded_292
  · subst n; exact excluded_293
  · subst n; exact excluded_298
  · subst n; exact excluded_299
#print axioms excluded_range_286_299
end CascadeFastReturn
