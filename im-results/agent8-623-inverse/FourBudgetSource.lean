import Agent8FiveBudgetSource

/-!
Source-linked four-per-block plus four upper gain for the full #623 B-drain.
Uses a universal evaluator potential and the exact stronger +2 potential
on nonzero returned B-block index. One-block exceptional gain (7) is handled
by the original-source-correct drainB_six index theorem. This is an all-natural
result, with no copied transition rules, fuel, or sampled trace.
-/
namespace BB6.Agent8FourBudgetSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8SixBudgetSource

/-- Global 4-to-2 evaluator potential. The +3 offset handles input k=1. -/
theorem evalA_four_budget (a : Nat) :
    ∀k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      dd+4*bb ≤ m+2*k+3 := by
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
      have horig := h
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
          by_cases hk1 : k=1
          · have hr := evalA_six_budget_pos (a+1) k m aa bb dd (by omega) horig
            omega
          · have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h
            omega

/-- Sharper +2 potential for evaluator returns with a positive B-index;
the strong residual inequality excludes the problematic k=1 branch. -/
theorem evalA_four_pos_b (a : Nat) :
    ∀k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      0<bb → dd+6*bb ≤ m+2*k+2 := by
  induction a with
  | zero =>
      intro k m aa bb dd h hb
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
      intro k m aa bb dd h hb
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
          have hbb := evalA_bb_three_le a (k/3) (m+2*(k/3)+3) aa bb dd h
          have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h hb
          omega

/-- Universal exact full-drain gain upper bound 4b+4 in the final third
counter, stronger than all previously established linear upper potentials. -/
theorem drainB_four (b : Nat) :
    ∀a d aa dd, drainB a b d = some (.D aa dd) → dd≤d+4*b+4 := by
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
              by_cases hb1 : b1=0
              · have hzero : dd=d1 := by
                  rw [drainB] at h
                  simp only [hb1,ite_true] at h
                  cases h
                  rfl
                have hu := evalA_four_budget a (b-1) (d+2*b+3) a1 b1 d1 hev
                omega
              · have hu := evalA_four_pos_b a (b-1) (d+2*b+3) a1 b1 d1
                  hev (by omega)
                by_cases hone : b1=1
                · have hspecial := (drainB_six b1 a1 d1 aa dd h).2.1 hone
                  omega
                · omega
            · simp [hlt] at h

/-- For b=2 the additive constant 4 is attained, and for b=1 the
linear coefficient 4 would need an additive constant at least 3. -/
theorem drainB_four_constant_sharp (a d : Nat) :
    drainB (a+2) 2 d = some (.D a (d+12)) := by
  rw [drainB]
  simp [evalA,drainB]

#print axioms evalA_four_budget
#print axioms evalA_four_pos_b
#print axioms drainB_four
#print axioms drainB_four_constant_sharp

end BB6.Agent8FourBudgetSource
