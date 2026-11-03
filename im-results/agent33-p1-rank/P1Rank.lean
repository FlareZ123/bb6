import PosEvenForm
set_option linter.unusedSimpArgs false
namespace BB6.Rank
open BB6.Agent1

theorem G_mass_lower (k c : Nat) :
    2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h : c < 2*k
    · rw [G]
      simp only [h, dite_true]
      have hdec : k - (c/2+1) < k := by omega
      have hb := ih _ hdec (2*c+3)
      omega
    · by_cases hm : c ≤ 2*k+1
      · rw [G]
        simp [h,hm]
        omega
      · rw [G]
        simp [h,hm]
        omega

theorem G_one_mass_strict (k : Nat) (hk : 1 ≤ k) :
    2*k+5 ≤ (G k 1).1+(G k 1).2 := by
  have hlow : 1 < 2*k := by omega
  rw [G]
  simp only [hlow,dite_true]
  change 2*k+5 ≤ (G (k-1) 5).1 + (G (k-1) 5).2
  have hb := G_mass_lower (k-1) 5
  omega

theorem T_mass_strict_except (a c b d : Nat) (h : T a c = some (b,d))
    (ha : a ≠ 1) : a+c < b+d := by
  unfold T at h
  by_cases hzero : c=0
  · simp [hzero] at h
    omega
  · by_cases hone : c=1
    · simp [hzero,hone] at h
      omega
    · by_cases heven : a%2=0
      · simp [hzero,hone,heven] at h
        omega
      · by_cases htwo : c=2
        · simp [hzero,hone,heven,htwo] at h
        · by_cases hthree : c=3
          · simp [hzero,hone,heven,htwo,hthree] at h
            have hb := G_one_mass_strict (a/2) (by omega)
            have heq : (G (a/2) 1).1+(G (a/2) 1).2=b+d := by rw [h]
            omega
          · simp [hzero,hone,heven,htwo,hthree] at h
            have hb := G_mass_lower (a/2+1) (c-2)
            have heq : (G (a/2+1) (c-2)).1+(G (a/2+1) (c-2)).2=b+d := by rw [h]
            omega

theorem T_output_left_ne_one (a c b d : Nat)
    (h : T a c = some (b,d)) : b ≠ 1 := by
  unfold T at h
  by_cases hzero : c=0
  · simp [hzero] at h
    omega
  · by_cases hone : c=1
    · simp [hzero,hone] at h
      omega
    · by_cases heven : a%2=0
      · simp [hzero,hone,heven] at h
        omega
      · by_cases htwo : c=2
        · simp [hzero,hone,heven,htwo] at h
        · by_cases hthree : c=3
          · simp [hzero,hone,heven,htwo,hthree] at h
            have hp := G_first_even (a/2) 1
            rw [h] at hp
            omega
          · simp [hzero,hone,heven,htwo,hthree] at h
            have hp := G_first_even (a/2+1) (c-2)
            rw [h] at hp
            omega

theorem reachable_left_ne_one (a c : Nat) (h : Reach a c) : a ≠ 1 := by
  induction h with
  | init => omega
  | next a c b d hreach hstep ih =>
      exact T_output_left_ne_one a c b d hstep

theorem reachable_step_rank_strict (a c b d : Nat)
    (hr : Reach a c) (hstep : T a c = some (b,d)) :
    a+c < b+d :=
  T_mass_strict_except a c b d hstep (reachable_left_ne_one a c hr)

#print axioms reachable_step_rank_strict
end BB6.Rank
