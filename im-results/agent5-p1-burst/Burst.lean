import Std

namespace BB6.P1Burst

def G (k c : Nat) : Nat × Nat :=
  if h : c < 2*k then
    G (k - (c/2 + 1)) (2*c + 3)
  else if c ≤ 2*k+1 then
    (0, 2*c+3)
  else
    (4*k+4, c-(2*k+2))
termination_by k
decreasing_by omega

def T (a c : Nat) : Option (Nat × Nat) :=
  if c = 0 then some (2, a+1)
  else if c = 1 then some (a+2, 0)
  else if a % 2 = 0 then some (a+3, c-2)
  else if c = 2 then none
  else if c = 3 then some (G (a/2) 1)
  else some (G (a/2 + 1) (c-2))

theorem G_direct (k c : Nat) (h : 2*k + 1 < c) :
    G k c = (4*k+4, c-(2*k+2)) := by
  rw [G]
  simp only [show ¬ c < 2*k by omega, dite_false]
  simp only [show ¬ c ≤ 2*k+1 by omega, ite_false]

theorem T_pair_direct (m y : Nat) (hy : 2*m + 10 ≤ y) :
    T (2*m) y = some (2*m+3, y-2) ∧
    T (2*m+3) (y-2) = some (4*m+12, y-(2*m+10)) := by
  constructor
  · unfold T
    simp only [show y ≠ 0 by omega, ite_false]
    simp only [show y ≠ 1 by omega, ite_false]
    simp
  · unfold T
    simp only [show y - 2 ≠ 0 by omega, ite_false]
    simp only [show y - 2 ≠ 1 by omega, ite_false]
    simp only [show (2*m+3) % 2 ≠ 0 by omega, ite_false]
    simp only [show y - 2 ≠ 2 by omega, ite_false]
    simp only [show y - 2 ≠ 3 by omega, ite_false]
    have hd : 2 * (m + 2) + 1 < y - 4 := by omega
    rw [show (2*m+3)/2 + 1 = m+2 by omega]
    rw [show y - 2 - 2 = y - 4 by omega]
    rw [G_direct (m+2) (y-4) hd]
    have hy4 : 4 ≤ y := by omega
    have hfst : 4 * (m + 2) + 4 = 4*m + 12 := by omega
    have hsnd : y - 4 - (2 * (m + 2) + 2) = y - (2*m+10) := by omega
    rw [hfst, hsnd]

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

theorem T_odd_second_stays_odd_or_zero (a c a' c' : Nat)
    (hc : c % 2 = 1) (h : T a c = some (a', c')) :
    c' = 0 ∨ c' % 2 = 1 := by
  unfold T at h
  by_cases hc0 : c = 0
  · omega
  · by_cases hc1 : c = 1
    · simp [hc0, hc1] at h
      omega
    · by_cases ha : a % 2 = 0
      · simp [hc0, hc1, ha] at h
        right
        rcases h with ⟨_, hsnd⟩
        omega
      · by_cases hc2 : c = 2
        · omega
        · by_cases hc3 : c = 3
          · simp only [hc0, hc1, ha, hc2, hc3, ite_false, ite_true] at h
            right
            have hg := G_preserves_odd_second (a/2) 1 (by omega)
            have hsnd : (G (a/2) 1).2 = c' := by
              injection h with hpair
              exact congrArg Prod.snd hpair
            rwa [hsnd] at hg
          · simp only [hc0, hc1, ha, hc2, hc3, ite_false] at h
            right
            have hcodd : (c - 2) % 2 = 1 := by omega
            have hg := G_preserves_odd_second (a/2 + 1) (c-2) hcodd
            have hsnd : (G (a/2 + 1) (c-2)).2 = c' := by
              injection h with hpair
              exact congrArg Prod.snd hpair
            rwa [hsnd] at hg

theorem T_positive_even_output_requires_even_input (a c a' c' : Nat)
    (h : T a c = some (a', c')) (hpos : 0 < c') (heven : c' % 2 = 0) :
    c % 2 = 0 := by
  have hcmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hcmod with hz | ho
  · exact hz
  · have hs := T_odd_second_stays_odd_or_zero a c a' c' ho h
    rcases hs with hzero | hodd
    · omega
    · omega

def X (n : Nat) : Int := 14 * (2:Int)^n - 12

def Y (N : Int) (n : Nat) : Int := N + 14 - 14 * (2:Int)^n + 2*n

theorem X_succ (n : Nat) : X (n+1) = 2 * X n + 12 := by
  rw [show n+1 = n.succ by omega]
  simp [X, Int.pow_succ]
  omega

theorem Y_succ (N : Int) (n : Nat) :
    Y N (n+1) = Y N n - X n - 10 := by
  rw [show n+1 = n.succ by omega]
  simp [Y, X, Int.pow_succ]
  omega

def dangerStart (n : Nat) : Int := 14 * (2:Int)^n - 2*n - 10

theorem danger_hits_four (n : Nat) : Y (dangerStart n) n = 4 := by
  simp [Y, dangerStart]
  omega

#print axioms BB6.P1Burst.G_direct
#print axioms BB6.P1Burst.T_pair_direct
#print axioms BB6.P1Burst.G_preserves_odd_second
#print axioms BB6.P1Burst.T_odd_second_stays_odd_or_zero
#print axioms BB6.P1Burst.T_positive_even_output_requires_even_input
#print axioms BB6.P1Burst.X_succ
#print axioms BB6.P1Burst.Y_succ
#print axioms BB6.P1Burst.danger_hits_four
end BB6.P1Burst
