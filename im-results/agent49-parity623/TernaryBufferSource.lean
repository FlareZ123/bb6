import Agent49TernaryShiftSource
import Agent8BudgetSource

/-! Original-source authenticated research on the #623 affine buffer.
DeepMind Cryptids source SHA c86f15861709b76042998c5211c7b2f83991621b.
Every theorem is about the source highLevelNext, not a blank-root decision.
-/
namespace BB6.Agent49TernaryBufferSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Sharp universal source evaluator potential. -/
theorem evalA_first3 (a : Nat) : ∀ k m aa bb dd : Nat,
    evalA a k m = some (aa,bb,dd) → 3*aa+bb ≤ 3*a+k+1 := by
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
        have hh:=ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Universal B-drain bound: 3*output_first≤3*input_first+input_index. -/
theorem drainB_first3 (b : Nat) : ∀ a d aa dd : Nat,
    drainB a b d = some (.D aa dd) → 3*aa ≤ 3*a+b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at h
          have hp := evalA_first3 a (b-1) (d+2*b+3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

#print axioms evalA_first3
#print axioms drainB_first3
end BB6.Agent49TernaryBufferSource
