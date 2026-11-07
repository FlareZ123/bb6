import Core192Source

namespace BB6.Agent15

open BB6.Agent41M192

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
  | zero =>
      norm_num
  | succ m ih =>
      have hexp : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [hexp, Nat.pow_add]
      norm_num
      nlinarith

/-- Every parameter in the second stopping family has k≥10. -/
theorem second_stop_k_ge10 (j m k : Nat) (hm : 2≤m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) : 10≤k := by
  have hp := two_pow_lower_linear m
  have hmul : (2*m+3)*(j+3) ≤ 2^(2*m+2)*(j+3) :=
    Nat.mul_le_mul_right (j+3) hp
  have hmain : (2*m+3)*(j+3) ≤ k+j+3*m+5 := by
    rw [heq]
    exact hmul
  nlinarith

/-- Consequently the entire second stopping family, for every j and m≥2,
is excluded from the original blank-root CLine orbit. No residue restriction
on j or m is needed. -/
theorem source_no_second_stop_all (j m k : Nat) (hm : 2≤m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  apply source_no_c0_right_ge8
  exact le_trans (by norm_num) (second_stop_k_ge10 j m k hm heq)

#print axioms source_no_second_stop_all

end BB6.Agent15
