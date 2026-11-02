import CLine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48

/-- Every state reached from the original C blank-entry acceleration with zero
middle counter has a left counter congruent to one modulo four. -/
theorem reached_middle_zero_mod4 (a c : Nat)
    (h : BB6CLine.Reach (a,0,c)) : a % 4 = 1 := by
  cases h with
  | init => decide
  | next s t hs hn =>
      rcases s with ⟨x,k,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
          omega
        · rcases k with _|k
          · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
            omega
          · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
            omega
        · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
          omega
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hk:k%2=0
          · simp [BB6CLine.nextC,hk] at hn
          · simp only [BB6CLine.nextC,hk,↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hn
            omega
        · simp [BB6CLine.nextC] at hn

#print axioms reached_middle_zero_mod4
/-- Exhaustive structural classification of all reachable zero-middle states:
no path information is needed beyond the final incoming transition. -/
theorem reached_middle_zero_shape (a c : Nat)
    (h : BB6CLine.Reach (a,0,c)) :
    (a=5 ∧ c=1) ∨
      (∃ k, a=1 ∧ c=2*k+2) ∨
      (∃ k d, a=4*k+5 ∧ c=d+4) := by
  cases h with
  | init => exact Or.inl ⟨rfl,rfl⟩
  | next s t hs hn =>
      rcases s with ⟨x,k,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
          right;left
          exact ⟨k,hn.1.symm,hn.2.2.symm⟩
        · rcases k with _|k
          · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hn
            exact Or.inl ⟨hn.1.symm,hn.2.2.symm⟩
          · simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hk:k%2=0
          · simp [BB6CLine.nextC,hk] at hn
          · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            right;right
            exact ⟨k/2,e,hn.1.symm,hn.2.2.symm⟩
        · simp [BB6CLine.nextC] at hn
#print axioms reached_middle_zero_shape

/-- This entire infinite family lies outside the actual blank-entry orbit. -/
theorem no_middle_zero_3mod4 (t c : Nat) :
    ¬ BB6CLine.Reach (4*t+3,0,c) := by
  intro h
  have hm := reached_middle_zero_mod4 (4*t+3) c h
  omega

/-- No reached zero-middle state can have zero right counter. -/
theorem no_both_middle_and_right_zero (a : Nat) :
    ¬ BB6CLine.Reach (a,0,0) := by
  intro h
  rcases reached_middle_zero_shape a 0 h with ⟨_,h⟩ | ⟨k,_,h⟩ | ⟨k,d,_,h⟩ <;> omega

#print axioms no_middle_zero_3mod4
#print axioms no_both_middle_and_right_zero
end BB6.Agent48
