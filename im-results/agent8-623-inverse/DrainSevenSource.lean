import Agent8DrainSectorSource

/-!
Optimal universal linear third-output bound on the actual #623 B-drain:
successful B(a,b,d)=D(aa,dd) implies dd <= d+7*b.
The coefficient seven is attained at b=1, a>0.
This is an all-input theorem, with no blank-root decision.
-/

namespace BB6.Agent8DrainSevenSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Source evaluator upper potential, including the exceptional final
ternary-one digit. -/
theorem evalA_third_potential (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) →
      dd + 2*bb ≤ m+2*k+3 := by
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
        by_cases hq : k/3=0
        · have hk : k=1 := by omega
          subst k
          cases a with
          | zero => simp [evalA] at h
          | succ a' =>
            simp [evalA] at h
            cases h
            omega
        · have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
          omega

/-- The sharp source bound for every successfully completed B-drain. -/
theorem drainB_third_upper_seven (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) → dd ≤ d+7*b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    by_cases hb0 : b=0
    · subst b
      simp [drainB] at h
      cases h
      omega
    · by_cases hb1 : b=1
      · subst b
        cases a with
        | zero =>
          have hnone : drainB 0 1 d = none := by
            rw [drainB]
            simp [evalA]
          rw [hnone] at h
          contradiction
        | succ a =>
          have heval : evalA (a+1) 0 (d+5) = some (a,0,d+7) := by
            simp [evalA]
          have hd0 : drainB a 0 (d+7) = some (.D a (d+7)) := by
            rw [drainB]
            simp
          have hon : drainB (a+1) 1 d = some (.D a (d+7)) := by
            rw [drainB]
            simp [heval, hd0]
          rw [hon] at h
          cases h
          omega
      · rw [drainB] at h
        simp only [if_neg hb0] at h
        cases he : evalA a (b-1) (d+2*b+3) with
        | none => simp [he] at h
        | some p =>
          rcases p with ⟨a1,b1,d1⟩
          simp only [he,Option.bind_some] at h
          by_cases hlt : b1<b
          · simp only [if_pos hlt] at h
            have hp := evalA_third_potential a (b-1) (d+2*b+3) a1 b1 d1 he
            have hquot := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
              a (b-1) (d+2*b+3) a1 b1 d1 he
            have hrec := ih b1 hlt a1 d1 aa dd h
            omega
          · simp [hlt] at h

/-- Source B-drain sector landing in the provably safe far-left cone. -/
theorem drainB_left_sector_seven (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd))
    (hfar : 2*d+16*b+8 ≤ a) :
    2*dd+8 ≤ aa := by
  have ha := BB6.Agent8DrainSectorSource.drainB_first_lower b a d aa dd h
  have hd := drainB_third_upper_seven b a d aa dd h
  omega

#print axioms evalA_third_potential
#print axioms drainB_third_upper_seven
#print axioms drainB_left_sector_seven
end BB6.Agent8DrainSevenSource
