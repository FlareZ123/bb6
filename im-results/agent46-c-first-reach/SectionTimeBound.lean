import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46TimeBound
open BB6.Agent46

/-- The recursive bounce consumes at most twice the initial third counter. -/
theorem bounce_time_le_double (c : Nat) : ∀ k : Nat, (bounce k c).1 ≤ 2*c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro k
      rw [bounce.eq_1]
      by_cases h4 : c<4
      · simp [h4]
      · simp only [h4, ite_false]
        by_cases ho : k%2=1
        · simp only [ho, ite_true]
          by_cases hs : c≤2*k+6
          · simp only [hs, ite_true]
            omega
          · simp only [hs, ite_false]
            have hh : c-(2*k+3)<c := by omega
            have hr := ih (c-(2*k+3)) hh (2*k+3)
            omega
        · simp only [ho, ite_false]
          by_cases hc4 : c=4
          · simp [hc4]
          · simp only [hc4, ite_false]
            by_cases hc5 : c=5
            · simp [hc5]
            · simp only [hc5, ite_false]
              by_cases hs : c≤2*k+8
              · simp only [hs, ite_true]
                omega
              · simp only [hs, ite_false]
                have hh : c-(2*k+5)<c := by omega
                have hr := ih (c-(2*k+5)) hh (2*k+4)
                omega

/-- All arithmetic Machine C section calls take at most 4k+5 steps,
    independently of the left counter a. -/
theorem secTime_le (a k : Nat) : secTime (a,k) ≤ 4*k+5 := by
  simp only [secTime,exactSection]
  by_cases ha0 : a=0
  · simp only [ha0, ite_true]
    by_cases hk0 : k=0
    · simp [hk0]
    · simp only [hk0, ite_false]
      by_cases hk1 : k=1
      · simp [hk1]
      · simp only [hk1, ite_false]
        have hb := bounce_time_le_double (2*k+1) 1
        omega
  · simp only [ha0, ite_false]
    by_cases ha1 : a=1
    · simp only [ha1, ite_true]
      by_cases hk0 : k=0
      · simp [hk0]
      · simp only [hk0, ite_false]
        by_cases hk1 : k=1
        · simp [hk1]
        · simp only [hk1, ite_false]
          by_cases hk2 : k=2
          · simp [hk2]
          · simp only [hk2, ite_false]
            by_cases hk3 : k=3
            · simp [hk3]
            · simp only [hk3, ite_false]
              have hb := bounce_time_le_double (2*k-3) 4
              omega
    · simp only [ha1, ite_false]
      by_cases hk0 : k=0
      · simp [hk0]
      · simp only [hk0, ite_false]
        by_cases hd : 2*k≤a
        · simp only [hd, ite_true]
          omega
        · simp only [hd, ite_false]
          have hb := bounce_time_le_double (2*k-a+3) (a-1)
          omega

#print axioms bounce_time_le_double
#print axioms secTime_le
end BB6.Agent46TimeBound
