import Agent49ParitySource

/-!
# Exact weighted cocycle for the authentic #623 B-drain

This file imports the unchanged Cryptids #623 definitions through
Agent49ParitySource. Under the strict ternary-ones budget, evalA preserves
an exact weighted quantity. Iterating that identity through drainB gives
an exact correction relation, not merely an upper bound.
-/

namespace BB6.Agent22ExactDrainCocycleSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/-- Under the strict all-ones budget, a successful evaluator preserves
    the exact weighted potential 2*a + k + m = 2*aa + 3*bb + dd. -/
theorem evalA_weighted_exact (a : Nat) :
    ∀ k m aa bb dd : Nat, k < ternaryOnes a →
      evalA a k m = some (aa, bb, dd) →
      2*aa + 3*bb + dd = 2*a + k + m := by
  induction a with
  | zero =>
      intro k m aa bb dd hbudget heval
      simp [ternaryOnes] at hbudget
  | succ a ih =>
      intro k m aa bb dd hbudget heval
      rw [evalA] at heval
      by_cases hk2 : k % 3 = 2
      · simp [hk2] at heval
        cases heval
        omega
      · by_cases hk0 : k % 3 = 0
        · simp [hk2, hk0] at heval
          cases heval
          omega
        · have hk1 : k % 3 = 1 := by omega
          have hnew : k / 3 < ternaryOnes a := by
            simp only [ternaryOnes] at hbudget
            omega
          simp [hk2, hk0] at heval
          have hi := ih (k / 3) (m + 2*(k / 3) + 3) aa bb dd hnew heval
          omega

/-- A successful B-drain under its source ternary budget has an exact
    weighted output. The integer r counts outer drain iterations. -/
theorem drainB_weighted_exact (b : Nat) :
    ∀ a d aa dd : Nat, b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      ∃ r : Nat, 2*aa + dd = 2*a + d + 3*b + 2*r := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd hbudget hdrain
      rw [drainB] at hdrain
      by_cases hb : b = 0
      · simp [hb] at hdrain
        cases hdrain
        refine ⟨0, ?_⟩
        omega
      · have hstrict : b - 1 < ternaryOnes a := by omega
        simp only [if_neg hb] at hdrain
        cases he : evalA a (b - 1) (d + 2*b + 3) with
        | none =>
            simp [he] at hdrain
        | some p =>
            rcases p with ⟨a1, b1, d1⟩
            simp only [he, Option.bind_some] at hdrain
            by_cases hlt : b1 < b
            · simp only [if_pos hlt] at hdrain
              have hbudget1 : b1 ≤ ternaryOnes a1 := by
                obtain ⟨a2, b2, d2, he2, hb2⟩ :=
                  evalA_ones_budget a (b - 1) (d + 2*b + 3) hstrict
                rw [he] at he2
                cases he2
                exact hb2
              obtain ⟨r, hr⟩ := ih b1 hlt a1 d1 aa dd hbudget1 hdrain
              have hpot := evalA_weighted_exact a (b - 1) (d + 2*b + 3)
                a1 b1 d1 hstrict he
              refine ⟨r + 1, ?_⟩
              omega
            · simp [hlt] at hdrain

#print axioms evalA_weighted_exact
#print axioms drainB_weighted_exact

end BB6.Agent22ExactDrainCocycleSource
