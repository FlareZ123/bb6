import Agent49ParitySource

/-!
Sharp complementary coordinate bounds for the original DeepMind Cryptids #623
evaluator and B-drain, pinned to source c86f15861709b76042998c5211c7b2f83991621b.
The original definitions are imported unchanged. These inequalities concern
only synthetic section transitions and do not decide the blank-root orbit.
-/

namespace BB6.Agent8UpperCounterSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Joint first loss and third-plus-block potential for every successful E. -/
theorem evalA_joint_bounds (a : Nat) :
    ∀ k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      a + bb ≤ aa + k + 1 ∧ dd + 7*bb ≤ m + 5*k + 2 := by
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
          have hr := ih (k/3) (m + 2*(k/3) + 3) aa bb dd h
          omega

/-- Both output coordinates of every successful B-drain obey sharp, uniform
linear bounds. For b=1 with initial first a+1, both are equalities. -/
theorem drainB_sharp_bounds (b : Nat) :
    ∀ a d aa dd, drainB a b d = some (.D aa dd) →
      a ≤ aa+b ∧ dd ≤ d+7*b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd h
      rw [drainB] at h
      by_cases hb : b=0
      · simp [hb] at h
        cases h
        constructor <;> omega
      · simp only [if_neg hb] at h
        cases he : evalA a (b-1) (d+2*b+3) with
        | none => simp [he] at h
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [he,Option.bind_some] at h
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at h
              have hp := evalA_joint_bounds a (b-1) (d+2*b+3) a1 b1 d1 he
              have hr := ih b1 hlt a1 d1 aa dd h
              constructor <;> omega
            · simp [hlt] at h

/-- A universal exact witness showing that the loss coefficient 1 and
third-coordinate gain coefficient 7 cannot be decreased uniformly. -/
theorem drainB_unit_sharp (a d : Nat) :
    drainB (a+1) 1 d = some (.D a (d+7)) := by
  rw [drainB]
  simp only [Nat.one_ne_zero, ite_false]
  rw [evalA]
  simp
  rw [drainB]
  simp

#print axioms evalA_joint_bounds
#print axioms drainB_sharp_bounds
#print axioms drainB_unit_sharp
end BB6.Agent8UpperCounterSource
