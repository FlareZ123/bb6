import Std

/-! Intermediate arithmetic lemmas for DeepMind-certified acceleration of
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.
No conclusion about halting is claimed. -/
namespace BB6.P1Reduction

def G (k c : Nat) : Nat × Nat :=
  if h : c < 2*k then
    G (k - (c/2 + 1)) (2*c + 3)
  else if c ≤ 2*k+1 then
    (0, 2*c+3)
  else
    (4*k+4, c-(2*k+2))
termination_by k
decreasing_by omega

theorem G_first_even (k c : Nat) : (G k c).1 % 2 = 0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1, dite_true]
      exact ih _ (by omega) _
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h1, h2]
      · rw [G]
        simp [h1, h2]
        omega

theorem G_preserves_odd_second (k c : Nat) (hc : c % 2 = 1) :
    (G k c).2 % 2 = 1 := by
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
        omega
      · rw [G]
        simp [h1, h2]
        omega

def T (a c : Nat) : Option (Nat × Nat) :=
  if c = 0 then some (2, a+1)
  else if c = 1 then some (a+2, 0)
  else if a % 2 = 0 then some (a+3, c-2)
  else if c = 2 then none
  else if c = 3 then some (G (a/2) 1)
  else some (G (a/2 + 1) (c-2))

theorem T_none_iff (a c : Nat) :
    T a c = none ↔ c = 2 ∧ a % 2 = 1 := by
  unfold T
  by_cases hc0 : c = 0
  · simp [hc0]
  · by_cases hc1 : c = 1
    · simp [hc0, hc1]
    · by_cases ha : a % 2 = 0
      · simp [hc0, hc1, ha]
      · by_cases hc2 : c = 2
        · simp [hc0, hc1, ha, hc2]
          omega
        · by_cases hc3 : c = 3
          · simp [hc0, hc1, ha, hc2, hc3]
          · simp [hc0, hc1, ha, hc2, hc3]

theorem T_danger_predecessor (a c a' : Nat)
    (h : T a c = some (a', 2)) (ha' : a' % 2 = 1) :
    a % 2 = 0 ∧ c = 4 := by
  unfold T at h
  by_cases hc0 : c = 0
  · simp [hc0] at h
    omega
  · by_cases hc1 : c = 1
    · simp [hc0, hc1] at h
    · by_cases ha : a % 2 = 0
      · simp [hc0, hc1, ha] at h
        omega
      · by_cases hc2 : c = 2
        · simp [hc0, hc1, ha, hc2] at h
        · by_cases hc3 : c = 3
          · simp [hc0, hc1, ha, hc2, hc3] at h
            have he := G_first_even (a/2) 1
            have hfirst : (G (a/2) 1).1 = a' := congrArg Prod.fst h
            rw [hfirst] at he
            omega
          · simp [hc0, hc1, ha, hc2, hc3] at h
            have he := G_first_even (a/2 + 1) (c-2)
            have hfirst : (G (a/2 + 1) (c-2)).1 = a' := congrArg Prod.fst h
            rw [hfirst] at he
            omega

#print axioms BB6.P1Reduction.G_first_even
#print axioms BB6.P1Reduction.G_preserves_odd_second
#print axioms BB6.P1Reduction.T_none_iff
#print axioms BB6.P1Reduction.T_danger_predecessor
end BB6.P1Reduction
