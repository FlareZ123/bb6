import Std
import Core192Source

namespace BB6.Agent15

open Agent41M192

/-- The M192 backward invariant excludes every original CLine section state
whose right coordinate is at least eight. This generalizes the single
(9,67,0) corollary currently exposed by the source dossier. -/
theorem source_no_c0_right_ge8 (a k : Nat) (hk : 8≤k) :
    ¬ BB6CLine.Reach (a,k,0) := by
  intro hreach
  have hnot := source_blank_never_bad a k 0 hreach
  have hbad : bad a k 0 := by
    simp [bad, low, hk]
  exact hnot hbad

/-- Elementary lower bound used to place the second stopping family in the
right-coordinate region excluded by source_no_c0_right_ge8. -/
theorem two_pow_lower_linear (m : Nat) :
    2*m+3 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hexp : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [hexp, Nat.pow_add]
      simp
      omega

/-- Every parameter in the second stopping family with m≥2 has k≥10. -/
theorem second_stop_k_ge10 (j m k : Nat) (hm : 2≤m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) : 10≤k := by
  have hp := two_pow_lower_linear m
  have hmul : (2*m+3)*(j+3) ≤ 2^(2*m+2)*(j+3) :=
    Nat.mul_le_mul_right (j+3) hp
  have hmain : (2*m+3)*(j+3) ≤ k+j+3*m+5 := by
    calc
      (2*m+3)*(j+3) ≤ 2^(2*m+2)*(j+3) := hmul
      _ = k+j+3*m+5 := heq.symm
  have hexpand : (2*m+3)*(j+3) = (2*m+3)*j + 6*m+9 := by
    rw [Nat.mul_add]
    omega
  have hprod : (2*m+3)*j = (2*m+2)*j + j := by
    rw [show 2*m+3 = (2*m+2)+1 by omega, Nat.add_mul]
    simp
  rw [hexpand, hprod] at hmain
  clear hp hmul heq
  omega

/-- Consequently the entire second stopping family, for every j and m≥2,
is excluded from the original blank-root CLine orbit. No residue restriction
on j or m is needed. -/
theorem source_no_second_stop_all (j m k : Nat) (hm : 2≤m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  apply source_no_c0_right_ge8
  have hk := second_stop_k_ge10 j m k hm heq
  omega

/-- The first stopping family has k≥8 for every positive m. -/
theorem first_stop_k_ge8 (m k : Nat) (hm : 1≤m)
    (heq : k+3*m+4 = 2^(2*m+3)) : 8≤k := by
  by_cases hm6 : 6≤m
  · have hp := two_pow_lower_linear m
    have hpow : 4*m+6 ≤ 2^(2*m+3) := by
      have hexp : 2*m+3 = (2*m+2)+1 := by omega
      rw [hexp, Nat.pow_succ]
      simp
      omega
    have hmain : 4*m+6 ≤ k+3*m+4 := by
      calc
        4*m+6 ≤ 2^(2*m+3) := hpow
        _ = k+3*m+4 := heq.symm
    omega
  · have hcases : m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals simp at heq
    all_goals omega

/-- The second stopping family has k≥8 except for its single small
parameter point (j,m)=(0,0). -/
theorem second_stop_k_ge8_except_00 (j m k : Nat)
    (hjm : j ≠ 0 ∨ m ≠ 0)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) : 8≤k := by
  by_cases hm0 : m=0
  · subst m
    have hj : 1≤j := by
      rcases hjm with hj | hm
      · omega
      · contradiction
    have heq' : k+j+5 = 4*(j+3) := by simpa using heq
    omega
  · by_cases hm1 : m=1
    · subst m
      have heq' : k+j+8 = 16*(j+3) := by simpa using heq
      omega
    · have hm2 : 2≤m := by omega
      have hk10 := second_stop_k_ge10 j m k hm2 heq
      omega

/-- Every positive-m first stopping-family target is absent from the
original blank-root CLine orbit. -/
theorem source_no_first_stop_m_pos (m k : Nat) (hm : 1≤m)
    (heq : k+3*m+4 = 2^(2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  apply source_no_c0_right_ge8
  exact first_stop_k_ge8 m k hm heq

/-- Every second stopping-family target except (j,m)=(0,0) is absent from
the original blank-root CLine orbit. -/
theorem source_no_second_stop_except_00 (j m k : Nat)
    (hjm : j ≠ 0 ∨ m ≠ 0)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  apply source_no_c0_right_ge8
  exact second_stop_k_ge8_except_00 j m k hjm heq

#print axioms source_no_second_stop_all

end BB6.Agent15
