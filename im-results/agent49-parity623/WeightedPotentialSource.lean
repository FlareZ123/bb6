import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
A weighted potential for the unchanged original Cryptids #623 ternary accelerator.
Lean source imports the original evalA and drainB directly. No source rules
are copied, no sorry, and no auxiliary axioms. A successful drain satisfies
2*a+b+d <= 2*a'+d', strengthened for b>0 to
2*a+d+2*b+3 <= 2*a'+d'. This is conditional on success and proves
neither raw-machine nonhalting nor a Busy Beaver bound.
-/

namespace BB6.Agent49WeightedSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem evalA_weight2 (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) →
      2*a + m ≤ 2*aa + bb + dd := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k%3=2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k%3=0
      · simp [hk2, hk0] at h
      · simp [hk2, hk0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k%3=2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k%3=0
      · simp [hk2, hk0] at h
        cases h
        omega
      · simp [hk2, hk0] at h
        have hr := ih (k/3) (m + 2*(k/3) + 3) aa bb dd h
        omega

theorem drainB_weight2 (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) →
      (2*a + b + d ≤ 2*aa + dd) ∧
      (0 < b → 2*a + d + 2*b + 3 ≤ 2*aa + dd) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      constructor <;> omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d + 2*b + 3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he, Option.bind_some] at h
        by_cases hlt : b1 < b
        · simp only [if_pos hlt] at h
          have hm := evalA_weight2 a (b-1) (d+2*b+3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          constructor <;> omega
        · simp [hlt] at h

#print axioms evalA_weight2
#print axioms drainB_weight2
end BB6.Agent49WeightedSource
