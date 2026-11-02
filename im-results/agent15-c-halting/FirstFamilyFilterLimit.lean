import AffineQuotientExclusion
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15
private theorem simple_pass (k : Nat)
    (hk : k%16=3 ∨ k%16=6 ∨ k%16=10 ∨ k%16=11 ∨ k%16=14 ∨ k%16=15) :
    affineQuotientExcluded 1 k = false := by
  have hguard : ¬(4≤k ∧ k%2=0 ∧ (1+k)%4=1) := by omega
  have hnorm : affineNormalize 1 k=(1,k) := by
    rw [affineNormalize, dif_neg hguard]
  have hbasic : ¬(k=0 ∨ k=2 ∨ (k%2=1 ∧ (1+k)%4=2 ∧ (1,k)≠(5,1))) := by omega
  have hquot : ¬((1%8=7 ∧ k%8=4) ∨ (1%8=1 ∧ k%16=2) ∨
    (1%16=9 ∧ k%16=15) ∨ (1%16=1 ∧ k%16=7 ∧ (1≠1 ∨ k≠7))) := by omega
  unfold affineQuotientExcluded affineExcluded
  simp [affineQuotientCondition,hnorm,hbasic,hquot] <;> omega

private theorem step_pass (k : Nat)
    (hk : k%16=4 ∨ k%16=12) (hbig : 4≤k) :
    affineQuotientExcluded 1 k = false := by
  have hstep : 4≤k ∧ k%2=0 ∧ (1+k)%4=1 := by omega
  have hstop : ¬(4≤(k-2)/2 ∧ ((k-2)/2)%2=0 ∧ ((k-1)+(k-2)/2)%4=1) := by omega
  have hnorm : affineNormalize 1 k=(k-1,(k-2)/2) := by
    rw [affineNormalize, dif_pos hstep]
    have ha : 1+k-2=k-1 := by omega
    rw [ha,affineNormalize,dif_neg hstop]
  have hyge : 1≤(k-2)/2 := by omega
  have hxy : ((k-1)+(k-2)/2)%4=0 := by omega
  have hxb : (k-1)%8=3 := by omega
  have hx16a : (k-1)%16≠9 := by omega
  have hx16b : (k-1)%16≠1 := by omega
  have hbasic : ¬((k-2)/2=0 ∨ (k-2)/2=2 ∨
    (((k-2)/2)%2=1 ∧ ((k-1)+(k-2)/2)%4=2 ∧
     (k-1,(k-2)/2)≠(5,1))) := by omega
  have hquot : ¬(((k-1)%8=7 ∧ ((k-2)/2)%8=4) ∨
    ((k-1)%8=1 ∧ ((k-2)/2)%16=2) ∨
    ((k-1)%16=9 ∧ ((k-2)/2)%16=15) ∨
    ((k-1)%16=1 ∧ ((k-2)/2)%16=7 ∧
     ((k-1)≠1 ∨ ((k-2)/2)≠7))) := by omega
  unfold affineQuotientExcluded affineExcluded
  simp [affineQuotientCondition,hnorm,hbasic,hquot] <;> omega

private theorem first_pow_lower (m : Nat) : 3*m+8≤2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)+3 = (2*n+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem first_pow_mod16 (m k : Nat) (hm : 0<m)
    (hk : k+3*m+4=2^(2*m+3)) :
    (k+3*m+4)%16=0 := by
  have hpow : 16 ∣ 2^(2*m+3) := by
    obtain ⟨r,hr⟩ : ∃ r, 2*m+3=4+r := ⟨2*m-1,by omega⟩
    rw [hr,Nat.pow_add]
    rw [show (2:Nat)^4=16 by decide]
    exact ⟨2^r,rfl⟩
  rw [hk]
  exact Nat.mod_eq_zero_of_dvd hpow

/-- All remaining first halting family residues pass this precise filter. -/
theorem first_family_remaining_pass (m k : Nat)
    (hm : m%16=0 ∨ m%16=2 ∨ m%16=3 ∨ m%16=6 ∨
          m%16=8 ∨ m%16=10 ∨ m%16=11 ∨ m%16=15)
    (hk : k+3*m+4=2^(2*m+3)) :
    affineQuotientExcluded 1 k = false := by
  by_cases hzero : m=0
  · subst m
    have hkeq : k=4 := by simp at hk; omega
    subst k
    exact step_pass 4 (Or.inl (by decide)) (by decide)
  · have hmp : 0<m := by omega
    have hmod := first_pow_mod16 m k hmp hk
    have hbig : 4≤k := by
      have hb := first_pow_lower m
      omega
    rcases hm with h0|h2|h3|h6|h8|h10|h11|h15
    · apply step_pass k (Or.inr (by omega)) hbig
    · apply simple_pass k (Or.inr (Or.inl (by omega)))
    · apply simple_pass k (Or.inl (by omega))
    · apply simple_pass k (Or.inr (Or.inr (Or.inl (by omega))))
    · apply step_pass k (Or.inl (by omega)) hbig
    · apply simple_pass k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    · apply simple_pass k (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · apply simple_pass k (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))

#print axioms first_family_remaining_pass
end BB6.Agent15
