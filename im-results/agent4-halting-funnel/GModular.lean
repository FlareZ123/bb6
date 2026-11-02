import HaltingFunnel

namespace BB6.HaltingFunnel

/-- A rigid mod-8/mod-4 dichotomy for the recursive G drain,
    provided the input counter is congruent to 1 mod 4. -/
theorem G_odd_modular (k c : Nat) (hc : c % 4 = 1) :
    ((G k c).1 % 8 = 0 ∧ (G k c).2 % 4 = 1) ∨
    ((G k c).1 % 8 = 4 ∧ (G k c).2 % 4 = 3) := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1, dite_true]
      apply ih _ (by omega) _
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp only [h1, dite_false, h2, ite_eq_left]
        left
        constructor
        · trivial
        · clear ih h1 h2
          omega
      · rw [G]
        simp only [h1, dite_false, h2, ite_false]
        have hd : 2*k+2 ≤ c := by omega
        rcases Nat.mod_two_eq_zero_or_one k with he | ho
        · right
          constructor <;> omega
        · left
          constructor <;> omega

#print axioms BB6.HaltingFunnel.G_odd_modular
end BB6.HaltingFunnel
