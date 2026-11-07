import Agent8DrainSevenSource

/-!
Optimal first-coordinate loss and joint all-input source envelopes for #623.
For any successfully completed source B(a,b,d) = D(aa,dd),
    a <= aa+b,  d+3b <= dd <= d+7b.
The coefficient one in the first inequality and seven in the last
are attained simultaneously at b=1,a>0; no blank-origin verdict follows.
-/

namespace BB6.Agent8DrainFirstSharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- An evaluator loses at most k+1 in first counter, compensated by bb. -/
theorem evalA_first_potential (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) →
      a+bb ≤ aa+k+1 := by
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
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- The coefficient one for first-coordinate loss of a source B-drain
is optimal, already attained at a>0,b=1. -/
theorem drainB_first_lower_sharp (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) → a ≤ aa+b := by
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
          have hpot := evalA_first_potential a (b-1) (d+2*b+3) a1 b1 d1 he
          have hrec := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- Two optimal one-call B-drain gain bounds. -/
theorem drainB_sharp_first_and_third (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    a ≤ aa+b ∧ dd ≤ d+7*b := by
  exact ⟨drainB_first_lower_sharp b a d aa dd h,
         BB6.Agent8DrainSevenSource.drainB_third_upper_seven b a d aa dd h⟩

/-- Optimal-coefficient safe outer cone for the original B-drain. -/
theorem drainB_left_sector_best (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd))
    (hfar : 2*d+15*b+8 ≤ a) :
    2*dd+8 ≤ aa := by
  have ha := drainB_first_lower_sharp b a d aa dd h
  have hd := BB6.Agent8DrainSevenSource.drainB_third_upper_seven b a d aa dd h
  omega

#print axioms evalA_first_potential
#print axioms drainB_first_lower_sharp
#print axioms drainB_sharp_first_and_third
#print axioms drainB_left_sector_best
end BB6.Agent8DrainFirstSharpSource
