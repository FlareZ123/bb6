import Agent8SixBudgetSource

/-!
Improved five-per-block (+2) universal completed B-drain gain for source #623.
The proof uses an exact ternary evaluator potential, its stronger k>=2
version, and the previous source-checked 3*bb<=k residual bound.
No finite-state sampling or copied machine semantics occurs.
-/

namespace BB6.Agent8FiveBudgetSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8SixBudgetSource

theorem evalA_five_budget (a : Nat) :
    ∀k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      dd+5*bb ≤ m+3*k+2 := by
  induction a with
  | zero =>
      intro k m aa bb dd h
      rw [evalA] at h
      by_cases h2 : k%3=2
      · simp [h2] at h
        cases h
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at h
        · simp [h2,h0] at h
          cases h
          omega
  | succ a ih =>
      intro k m aa bb dd h
      rw [evalA] at h
      by_cases h2 : k%3=2
      · simp [h2] at h
        cases h
        omega
      · by_cases h0 : k%3=0
        · simp [h2,h0] at h
          cases h
          omega
        · simp [h2,h0] at h
          have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h
          omega

theorem evalA_five_ge2 (a k m aa bb dd : Nat)
    (hk : 2≤k)
    (h : evalA a k m = some (aa,bb,dd)) :
    dd+5*bb ≤ m+3*k := by
  rw [evalA] at h
  by_cases h2 : k%3=2
  · simp [h2] at h
    cases h
    omega
  · by_cases ha : a=0
    · simp [h2,ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
      · simp [h0] at h
        cases h
        omega
    · simp only [if_neg h2, if_neg ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
        cases h
        omega
      · simp only [if_neg h0] at h
        have hr := evalA_five_budget (a-1) (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Every successful source B-drain gains at most five units per block plus
two, independently of its first counter and all other branches. -/
theorem drainB_five (b : Nat) :
    ∀a d aa dd, drainB a b d = some (.D aa dd) →
      dd≤d+5*b+2 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd h
      rw [drainB] at h
      by_cases hb : b=0
      · simp [hb] at h
        cases h
        omega
      · simp only [if_neg hb] at h
        cases hev : evalA a (b-1) (d+2*b+3) with
        | none => simp [hev] at h
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev,Option.bind_some] at h
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at h
              have hr := ih b1 hlt a1 d1 aa dd h
              have hbb := evalA_bb_three_le a (b-1) (d+2*b+3) a1 b1 d1 hev
              by_cases hb1 : b1=0
              · have hzero : dd=d1 := by
                  rw [drainB] at h
                  simp only [hb1,ite_true] at h
                  cases h
                  rfl
                have hu := evalA_five_budget a (b-1) (d+2*b+3) a1 b1 d1 hev
                omega
              · have hu := evalA_five_ge2 a (b-1) (d+2*b+3) a1 b1 d1 (by omega) hev
                omega
            · simp [hlt] at h

#print axioms evalA_five_budget
#print axioms evalA_five_ge2
#print axioms drainB_five

end BB6.Agent8FiveBudgetSource
