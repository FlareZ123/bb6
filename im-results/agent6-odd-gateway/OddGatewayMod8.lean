import Std

namespace BB6Agent6

/-- Exact nested drain in the published BB(6) P1 acceleration. -/
def G (k c : Nat) : Nat × Nat :=
  if h : c < 2*k then G (k - (c/2 + 1)) (2*c+3)
  else if c ≤ 2*k+1 then (0,2*c+3)
  else (4*k+4,c-(2*k+2))
termination_by k
decreasing_by omega

/-- If the input is 1 mod 4 and the output's right counter equals 3,
    then the output's left counter equals 4 mod 8. -/
theorem G_one_mod4_right_three (k c : Nat) (hc : c % 4 = 1) :
    (G k c).2 = 3 → (G k c).1 % 8 = 4 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    rw [G]
    by_cases hsmall : c < 2*k
    · simp only [hsmall, dite_true]
      have hnext : (2*c+3) % 4 = 1 := by omega
      have hlt : k-(c/2+1) < k := by omega
      exact ih (k-(c/2+1)) hlt (2*c+3) hnext
    · simp only [hsmall, dite_false]
      by_cases hmid : c ≤ 2*k+1
      · simp only [hmid, ite_true]
        intro hout
        omega
      · simp only [hmid, ite_false]
        intro hout
        have heven : k%2=0 := by omega
        omega

/-- For an even drain index and odd input, reaching right counter 3
    forces left-counter residue 4 modulo 8. -/
theorem G_even_k_right_three (k c : Nat)
    (hk : k % 2 = 0) (hc : c % 2 = 1) :
    (G k c).2 = 3 → (G k c).1 % 8 = 4 := by
  rw [G]
  by_cases hsmall : c < 2*k
  · simp only [hsmall, dite_true]
    have hmod : (2*c+3)%4=1 := by omega
    exact G_one_mod4_right_three (k-(c/2+1)) (2*c+3) hmod
  · simp only [hsmall, dite_false]
    by_cases hmid : c ≤ 2*k+1
    · simp only [hmid, ite_true]
      intro hout
      omega
    · simp only [hmid, ite_false]
      intro hout
      omega

/-- Exact odd-sector return from Agent 4's independently restated P1 map. -/
def U (a c : Nat) : Nat × Nat :=
  if c=1 then (2,a+3)
  else if c=3 then (2,a+6)
  else if c=5 then G (a/2+1) 1
  else G (a/2+2) (c-4)

/-- A right-counter-3 return from a left counter divisible by 4 must
    arrive with left counter 4 modulo 8. -/
theorem U_four_multiple_right_three (a c : Nat)
    (ha : a % 4 = 0) (hc : c % 2 = 1) (h5 : 5 ≤ c) :
    (U a c).2 = 3 → (U a c).1 % 8 = 4 := by
  by_cases hfive : c=5
  · subst c
    simpa [U] using (G_one_mod4_right_three (a/2+1) 1 (by decide))
  · have h1 : c≠1 := by omega
    have h3 : c≠3 := by omega
    have hk : (a/2+2)%2=0 := by omega
    have hodd : (c-4)%2=1 := by omega
    simpa [U, h1, h3, hfive] using
      (G_even_k_right_three (a/2+2) (c-4) hk hodd)

#print axioms BB6Agent6.U_four_multiple_right_three
#print axioms BB6Agent6.G_even_k_right_three
end BB6Agent6
